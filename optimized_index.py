import sqlite3
import mmap
import threading
import logging
from typing import Generator, List, Dict, Set, Optional
from dataclasses import dataclass
from datetime import datetime
import tempfile
import os
import gc
import hashlib
import json
import re
from pathlib import Path
import PyPDF2
from docx import Document
import chardet
from collections import OrderedDict
import platform

# פונקציית עזר – נתיב אחסון לאפליקציה
def get_app_data_path():
    if platform.system() == 'Windows':
        app_data = os.path.join(os.getenv('APPDATA'), 'DocumentSearchApp')
    elif platform.system() == 'Darwin':
        app_data = os.path.join(os.path.expanduser('~'), 'Library', 'Application Support', 'DocumentSearchApp')
    else:
        app_data = os.path.join(os.path.expanduser('~'), '.config', 'DocumentSearchApp')
    os.makedirs(app_data, exist_ok=True)
    return app_data


def tokenize(text: str) -> list:
    """פירוק טקסט למילים עם הסרת ניקוד"""
    if not text:
        return []
    
    # הסרת ניקוד
    text = re.sub(r'[\u0591-\u05C7]', '', text)
    
    # הסרת תווים מיוחדים והמרה לאותיות קטנות
    text = re.sub(r'[^\w\s\u0590-\u05FF]', ' ', text.lower())
    
    # פיצול למילים והסרת רווחים מיותרים
    words = [word.strip() for word in text.split() if word.strip()]
    
    # סינון מילים קצרות מדי
    words = [word for word in words if len(word) > 1]
    
    return words

# הוספת הגדרת SearchOptions
class SearchOptions:
    def __init__(self):
        self.exact_match = False
        self.word_distance = None
        self.match_all_words = True
        self.exclude_words = []
        self.file_types = []
        self.date_range = {'start': None, 'end': None}
        self.min_word_count = None
        self.search_in_path = False
        self.cache_results = True
        self.chunk_size = 10 * 1024 * 1024  # 5MB במקום 1MB
        self.default_context_words = 200
        
#------------------------
#  שיפור האינדקס
#-------------------------

@dataclass
class IndexStats:
    """נתונים סטטיסטיים על האינדקס"""
    total_files: int = 0
    processed_files: int = 0
    failed_files: int = 0
    total_words: int = 0
    last_update: datetime = None
    processing_time: float = 0

class OptimizedFileIndex:
    def __init__(self, folder_path: str):
        self.folder_path = folder_path
        self.app_data_path = get_app_data_path()
        self._init_paths()
        self._init_db()
        self.chunk_size = 1024 * 1024  # 1MB
        self.max_file_size = 100 * 1024 * 1024  # 100MB
        self.index_lock = threading.Lock()
        self.stats = IndexStats()

    def _init_paths(self):
        """אתחול נתיבי קבצים"""
        folder_hash = hashlib.md5(self.folder_path.encode()).hexdigest()
        self.db_path = os.path.join(self.app_data_path, f'index_{folder_hash}.db')
        self.backup_dir = os.path.join(self.app_data_path, 'backups')
        os.makedirs(self.backup_dir, exist_ok=True)
        


    def _init_db(self):
        """אתחול בסיס הנתונים SQLite"""
        with sqlite3.connect(self.db_path) as conn:
            # יצירת טבלת קבצים
            conn.execute('''
                CREATE TABLE IF NOT EXISTS files (
                    path TEXT PRIMARY KEY,
                    hash TEXT,
                    filename TEXT,
                    file_size INTEGER,
                    last_modified TIMESTAMP
                )
            ''')

            # יצירת טבלת תוכן
            conn.execute('''
                CREATE TABLE IF NOT EXISTS content (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    file_path TEXT,
                    location TEXT,
                    content TEXT,
                    FOREIGN KEY(file_path) REFERENCES files(path)
                )
            ''')

            # יצירת טבלת מילים
            conn.execute('''
                CREATE TABLE IF NOT EXISTS words (
                    word TEXT PRIMARY KEY,
                    frequency INTEGER DEFAULT 1,
                    last_used TIMESTAMP
                )
            ''')

            # יצירת טבלת מיקומי מילים
            conn.execute('''
                CREATE TABLE IF NOT EXISTS word_locations (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    word TEXT,
                    content_id INTEGER,
                    position INTEGER,
                    FOREIGN KEY(word) REFERENCES words(word),
                    FOREIGN KEY(content_id) REFERENCES content(id)
                )
            ''')

            # יצירת אינדקסים
            conn.execute('CREATE INDEX IF NOT EXISTS idx_word ON word_locations(word)')
            conn.execute('CREATE INDEX IF NOT EXISTS idx_content ON word_locations(content_id)')


    def _get_file_hash(self, file_path: str) -> str:
        """חישוב hash של קובץ"""
        hash_md5 = hashlib.md5()
        try:
            with open(file_path, "rb") as f:
                for chunk in iter(lambda: f.read(4096), b""):
                    hash_md5.update(chunk)
            return hash_md5.hexdigest()
        except Exception as e:
            logging.error(f"Error calculating file hash for {file_path}: {e}")
            return None            

    def _remove_file_content(self, conn: sqlite3.Connection, file_path: str) -> None:
        """מחיקת תוכן קודם של קובץ"""
        try:
            # מחיקת מיקומי מילים
            conn.execute("""
                DELETE FROM word_locations 
                WHERE content_id IN (
                    SELECT id FROM content WHERE file_path = ?
                )
            """, (file_path,))
            
            # מחיקת תוכן
            conn.execute("DELETE FROM content WHERE file_path = ?", (file_path,))
            
            # מחיקת הקובץ
            conn.execute("DELETE FROM files WHERE path = ?", (file_path,))
            
        except Exception as e:
            logging.error(f"Error removing file content for {file_path}: {e}")
            
        
    def process_file(self, file_path: str) -> bool:
        """עיבוד קובץ בודד"""
        try:
            # בדיקות מקדימות
            if not os.path.exists(file_path) or not os.access(file_path, os.R_OK):
                logging.warning(f"File not accessible: {file_path}")
                return False

            file_size = os.path.getsize(file_path)
            if file_size > self.max_file_size:
                logging.warning(f"File too large: {file_path}")
                return False

            file_hash = self._get_file_hash(file_path)

            with sqlite3.connect(self.db_path) as conn:
                conn.execute("PRAGMA journal_mode=WAL")
                conn.execute("PRAGMA synchronous=NORMAL")
                
                # מחיקת תוכן ישן אם הקובץ השתנה
                conn.execute("""
                    DELETE FROM files WHERE path=? AND hash<>?
                """, (file_path, file_hash))
                
                # בדיקה אם הקובץ עדיין קיים לאחר המחיקה
                existing = conn.execute(
                    "SELECT hash FROM files WHERE path=?", (file_path,)
                ).fetchone()
                if existing:
                    logging.info(f"File unchanged: {file_path}")
                    return False

                # עיבוד התוכן
                contents = self._extract_file_content(file_path)
                if not contents:
                    logging.warning(f"Empty or invalid content extracted from {file_path}")
                    return False

                # הוספת הקובץ לטבלת files
                conn.execute("""
                    INSERT OR REPLACE INTO files 
                    (path, hash, filename, file_size, last_modified)
                    VALUES (?, ?, ?, ?, ?)
                """, (
                    file_path,
                    file_hash,
                    os.path.basename(file_path),
                    file_size,
                    datetime.fromtimestamp(os.path.getmtime(file_path))
                ))

                # הוספת התוכן והמילים
                self._add_content_and_words(conn, file_path, contents)

                return True

        except Exception as e:
            logging.error(f"Error processing file {file_path}: {e}")
            return False
        finally:
            gc.collect()
        
    def _extract_file_content(self, file_path: str):
        """חילוץ תוכן מקובץ לפי סוגו"""
        if file_path.lower().endswith('.pdf'):
            return self._extract_pdf_content(file_path)
        elif file_path.lower().endswith(('.doc', '.docx')):
            return self._extract_docx_content(file_path)
        elif file_path.lower().endswith('.txt'):
            return self._extract_txt_content(file_path)
        else:
            logging.warning(f"Unsupported file type: {file_path}")
            return []

    def _extract_pdf_content(self, file_path: str) -> List[Dict]:
        """חילוץ תוכן PDF"""
        contents = []
        try:
            with open(file_path, 'rb') as pdf_file:
                reader = PyPDF2.PdfReader(pdf_file)
                for page_num, page in enumerate(reader.pages):
                    text = page.extract_text()
                    if text.strip():
                        contents.append({
                            'content': text.strip(),
                            'page': page_num + 1
                        })
                        logging.debug(f"Extracted page {page_num + 1}: {text[:100]}")  # דיבוג: הצגת 100 התווים הראשונים
        except Exception as e:
            logging.error(f"Error extracting PDF content from {file_path}: {e}")
        return contents
    
    def _extract_docx_content(self, file_path: str) -> List[Dict]:
        """חילוץ תוכן DOCX"""
        contents = []
        try:
            doc = Document(file_path)
            for para_num, para in enumerate(doc.paragraphs):
                text = para.text
                if text.strip():
                    contents.append({
                        'content': text.strip(),
                        'paragraph': para_num + 1
                    })
        except Exception as e:
            logging.error(f"Error extracting DOCX content from {file_path}: {e}")
        return contents

    def _extract_txt_content(self, file_path):
        """חילוץ תוכן מקובץ טקסט"""
        contents = []
        try:
            # זיהוי קידוד אוטומטי
            with open(file_path, 'rb') as f:
                raw_data = f.read()
                detected = chardet.detect(raw_data)
                encoding = detected.get('encoding', 'utf-8')

            # קריאת הקובץ בקידוד שזוהה
            with open(file_path, 'r', encoding=encoding, errors='replace') as f:
                chunk = ''
                chunk_num = 1
                for line in f:
                    chunk += line
                    # בדוק אם הגענו לגודל ה-chunk
                    if len(chunk) >= self.chunk_size:
                        contents.append({
                            'content': chunk.strip(),
                            'chunk': chunk_num
                        })
                        chunk = ''
                        chunk_num += 1
                # הוספת שארית התוכן
                if chunk.strip():
                    contents.append({
                        'content': chunk.strip(),
                        'chunk': chunk_num
                    })
        except Exception as e:
            logging.error(f"Error extracting TXT content from {file_path}: {e}")
        return contents

    def _add_content_and_words(self, conn: sqlite3.Connection, file_path: str, contents: List[Dict]) -> None:
        """הוספת תוכן ומילים לבסיס הנתונים"""
        for content_item in contents:
            cursor = conn.execute("""
                INSERT INTO content (file_path, location, content)
                VALUES (?, ?, ?)
            """, (
                file_path,
                str(content_item.get('page') or content_item.get('chunk')),
                content_item['content']
            ))

            content_id = cursor.lastrowid
            words = set(tokenize(content_item['content']))

            for position, word in enumerate(words):
                # עדכון טבלת מילים
                conn.execute("""
                    INSERT OR IGNORE INTO words (word, frequency, last_used)
                    VALUES (?, 0, CURRENT_TIMESTAMP)
                """, (word,))
                conn.execute("""
                    UPDATE words 
                    SET frequency = frequency + 1, last_used = CURRENT_TIMESTAMP
                    WHERE word = ?
                """, (word,))
                conn.execute("""
                    INSERT INTO word_locations (word, content_id, position)
                    VALUES (?, ?, ?)
                """, (word, content_id, position))
                
  
    def search(self, query: str, search_options: Optional[SearchOptions] = None, 
              max_results: int = 50) -> List[Dict]:
        """חיפוש עם אופטימיזצית זיכרון"""
        try:
            query_words = tokenize(query.strip().lower())
            if not query_words:
                return []

            with sqlite3.connect(self.db_path) as conn:
                params = []
                
                if search_options and search_options.exact_match:
                    # חיפוש התאמה מדויקת
                    exact_phrase = ' '.join(query_words)
                    sql = """
                        SELECT DISTINCT 
                            f.filename,
                            f.path as file_path,
                            c.location,
                            c.content,
                            1 as word_matches
                        FROM content c
                        JOIN files f ON c.file_path = f.path
                        WHERE (
                            LOWER(c.content) LIKE ? OR  -- בדיקה עם רווח בהתחלה
                            LOWER(c.content) LIKE ? OR  -- בדיקה עם רווח בסוף
                            LOWER(c.content) LIKE ? OR  -- בדיקה עם רווחים בשני הצדדים
                            LOWER(c.content) = ?        -- בדיקה למקרה של התאמה מלאה
                        )
                        GROUP BY c.id
                        LIMIT ?
                    """
                    # מוסיפים את כל האפשרויות לחיפוש המדויק
                    params = [
                        f'% {exact_phrase}',     # רווח רק בהתחלה
                        f'{exact_phrase} %',     # רווח רק בסוף
                        f'% {exact_phrase} %',   # רווחים בשני הצדדים
                        exact_phrase,            # התאמה מלאה
                        max_results
                    ]
                else:
                    # חיפוש רגיל - מילים בודדות
                    query_parts = []
                    for word in query_words:
                        if search_options and search_options.match_all_words:
                            # חייב להכיל את כל המילים
                            query_parts.append("LOWER(c.content) LIKE ?")
                            params.append(f'%{word}%')
                        else:
                            # מספיק שתכיל לפחות מילה אחת
                            query_parts.append("LOWER(c.content) LIKE ?")
                            params.append(f'%{word}%')
                    
                    sql = f"""
                        SELECT DISTINCT 
                            f.filename,
                            f.path as file_path,
                            c.location,
                            c.content,
                            1 as word_matches
                        FROM content c
                        JOIN files f ON c.file_path = f.path
                        WHERE {" AND ".join(query_parts) if search_options and search_options.match_all_words 
                              else " OR ".join(query_parts)}
                        GROUP BY c.id
                        LIMIT ?
                    """
                    params.append(max_results)
                
                results = []
                for row in conn.execute(sql, params):
                    result = {
                        "filename": row[0],
                        "file_path": row[1],
                        "location": row[2],
                        "context": self._optimize_context(
                            row[3], 
                            [' '.join(query_words)] if search_options and search_options.exact_match else query_words,
                            search_options.default_context_words if search_options else 200
                        ),
                        "relevance_score": row[4]
                    }
                    results.append(result)
                
                return results

        except Exception as e:
            logging.error(f"Search error: {e}")
            return []
    
    def _optimize_context(self, text: str, query_words: List[str], context_words: int) -> str:
        """אופטימיזציה של טקסט ההקשר"""
        words = text.split()
        best_start = 0
        max_matches = 0
        
        # מציאת המיקום הטוב ביותר
        for i in range(len(words)):
            matches = sum(1 for w in query_words if w in words[i].lower())
            if matches > max_matches:
                max_matches = matches
                best_start = i
        
        # חיתוך ההקשר
        start = max(0, best_start - context_words // 2)
        end = min(len(words), start + context_words)
        
        context = " ".join(words[start:end])
        if start > 0:
            context = "..." + context
        if end < len(words):
            context += "..."
            
        return context

    def cleanup(self):
        """ניקוי האינדקס וזיכרון"""
        try:
            # ביצוע פעולות המחיקה בטרנזקציה אחת
            with sqlite3.connect(self.db_path) as conn:
                conn.execute("""
                    DELETE FROM words 
                    WHERE frequency = 1 
                    AND last_used < datetime('now', '-30 days')
                """)
                conn.execute("""
                    DELETE FROM files 
                    WHERE path NOT IN (SELECT DISTINCT file_path FROM content)
                """)
            
            # ביצוע VACUUM בחיבור נפרד, מחוץ לטרנזקציה
            vacuum_conn = sqlite3.connect(self.db_path)
            try:
                vacuum_conn.execute("VACUUM")
            finally:
                vacuum_conn.close()
                
            logging.info("Cleanup completed successfully.")
        except Exception as e:
            logging.error(f"Cleanup error: {e}")
        finally:
            gc.collect()


    def _remove_file_content(self, conn: sqlite3.Connection, file_path: str) -> None:
        """מחיקת תוכן קודם של קובץ"""
        try:
            # מחיקת מיקומי מילים
            conn.execute("""
                DELETE FROM word_locations 
                WHERE content_id IN (
                    SELECT id FROM content WHERE file_path = ?
                )
            """, (file_path,))
            
            # מחיקת תוכן
            conn.execute("DELETE FROM content WHERE file_path = ?", (file_path,))
            
            # מחיקת הקובץ
            conn.execute("DELETE FROM files WHERE path = ?", (file_path,))
            
        except Exception as e:
            logging.error(f"Error removing file content: {e}")
            raise


        
    def debug_search(self, word: str):
        """פונקציית דיבאג להבנת הבעיה"""
        with sqlite3.connect(self.db_path) as conn:
            # בדיקת התוכן המקורי
            content_results = conn.execute("""
                SELECT c.content, c.location 
                FROM content c 
                WHERE LOWER(c.content) LIKE ?
                LIMIT 5
            """, [f'%{word}%']).fetchall()
            
            # בדיקת המילים השמורות
            word_results = conn.execute("""
                SELECT w.word, c.content, c.location
                FROM words w
                JOIN word_locations wl ON w.word = wl.word
                JOIN content c ON wl.content_id = c.id
                WHERE w.word = ?
                LIMIT 5
            """, [word.lower()]).fetchall()
            
            return {
                'content_matches': content_results,
                'word_matches': word_results
            }

from collections import OrderedDict

class LRUCache:
    """מטמון LRU לתוצאות חיפוש"""
    def __init__(self, capacity):
        self.capacity = capacity
        self._cache = OrderedDict()
        
    def get(self, key):
        if key not in self._cache:
            return None
        # העברה לסוף (הכי חדש)
        self._cache.move_to_end(key)
        return self._cache[key]
        
    def set(self, key, value):
        if key in self._cache:
            # העברה לסוף
            self._cache.move_to_end(key)
        self._cache[key] = value
        if len(self._cache) > self.capacity:
            # הסרת הפריט הישן ביותר
            self._cache.popitem(first=True)
