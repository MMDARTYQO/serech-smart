

import subprocess
import sys

def install_required_libraries():
    # רשימת הספריות שצריך להתקין
    required_libraries = [
        'flet',
        'PyPDF2',
        'python-docx',
        'PyMuPDF',
        'chardet'
    ]
    
    print("בודק ומתקין ספריות נדרשות...")
    
    for library in required_libraries:
        try:
            # מנסה לייבא את הספרייה
            __import__(library.replace('-', '_'))  # מחליף - ב_ כי בפייתון לא יכול להיות - בשם מודול
            print(f"הספרייה {library} כבר מותקנת")
        except ImportError:
            print(f"מתקין את הספרייה {library}...")
            try:
                # מתקין את הספרייה באמצעות pip
                subprocess.check_call([sys.executable, '-m', 'pip', 'install', library])
                print(f"הספרייה {library} הותקנה בהצלחה!")
            except subprocess.CalledProcessError as e:
                print(f"שגיאה בהתקנת הספרייה {library}: {e}")
            except Exception as e:
                print(f"שגיאה לא צפויה בהתקנת הספרייה {library}: {e}")

# קורא לפונקציה לפני טעינת שאר הקוד
if __name__ == "__main__":
    install_required_libraries()


import flet as ft
from flet import *
import os
import PyPDF2
from docx import Document
import subprocess
import platform
from threading import Timer
import json
import hashlib
import time
from pathlib import Path
import tempfile
import webbrowser
from datetime import datetime
import os
import re
from collections import defaultdict
import tempfile, os
import chardet
import gc
import sqlite3
import mmap
import threading
import logging
from typing import Generator, List, Dict, Set, Optional
from dataclasses import dataclass
from datetime import datetime
import logging
from optimized_index import OptimizedFileIndex
from optimized_index import OptimizedFileIndex, LRUCache


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

#---------------------------------
# היסטורית חיפושים
#---------------------------------
class SearchHistory:
    def __init__(self, max_items=10):
        self.max_items = max_items
        self.history = []
        self.history_file = Path("search_history.json")
        self.load_history()

    def add(self, search_term):
        """הוספת חיפוש חדש להיסטוריה"""
        if search_term and search_term.strip():
            search_term = search_term.strip()
            # הסר את החיפוש אם הוא כבר קיים
            self.history = [h for h in self.history if h != search_term]
            # הוסף את החיפוש החדש בהתחלה
            self.history.insert(0, search_term)
            # שמור רק את מספר הפריטים המקסימלי
            self.history = self.history[:self.max_items]
            self.save_history()

    def get_history(self):
        """קבלת רשימת החיפושים"""
        return self.history

    def clear(self):
        """ניקוי ההיסטוריה"""
        self.history = []
        self.save_history()

    def remove_item(self, search_term):
        """הסרת פריט ספציפי מההיסטוריה"""
        self.history = [h for h in self.history if h != search_term]
        self.save_history()

    def load_history(self):
        """טעינת היסטוריית החיפושים מקובץ"""
        try:
            if self.history_file.exists():
                with open(self.history_file, 'r', encoding='utf-8') as f:
                    self.history = json.load(f)
        except Exception:
            self.history = []

    def save_history(self):
        """שמירת היסטוריית החיפושים לקובץ"""
        try:
            with open(self.history_file, 'w', encoding='utf-8') as f:
                json.dump(self.history, f, ensure_ascii=False, indent=2)
        except Exception:
            pass  # במקרה של שגיאה בשמירה, נתעלם



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
        self.chunk_size = 1024 * 1024  # 1MB chunks
        self.default_context_words = 200  # חדש - מספר מילים בהקשר       

#--------------------------
#    הגדרות
#--------------------------
class AppSettings:
    def __init__(self):
        self.app_data_path = get_app_data_path()
        self.settings_file = os.path.join(self.app_data_path, 'settings.json')
        self.default_settings = {
            'theme': 'light',
            'primary_color': '#0078D4',
            'font_size': 'normal',
            'indexes': [],
            'selected_indexes': [],
            'default_context_words': 200,
            'window_maximized': True
        }
        self.settings = self.load_settings()
        self.validate_settings()

    def validate_settings(self):
        was_changed = False
        # וידוא שכל ההגדרות קיימות
        for key, default_value in self.default_settings.items():
            if key not in self.settings:
                self.settings[key] = default_value
                was_changed = True
        
        # אם אין אינדקסים נבחרים אבל יש אינדקסים מוגדרים - נבחר את כולם
        if not self.settings.get('selected_indexes') and self.settings.get('indexes'):
            self.settings['selected_indexes'] = [idx['path'] for idx in self.settings['indexes']]
            was_changed = True
        
        if was_changed:
            self.save_settings()

    def load_settings(self):
        if os.path.exists(self.settings_file):
            try:
                with open(self.settings_file, 'r', encoding='utf-8') as f:
                    loaded_settings = json.load(f)
                    settings = self.default_settings.copy()
                    settings.update(loaded_settings)
                    return settings
            except Exception as e:
                print(f"שגיאה בטעינת הגדרות: {e}")
                return self.default_settings.copy()
        return self.default_settings.copy()

    def save_settings(self):
        try:
            with open(self.settings_file, 'w', encoding='utf-8') as f:
                json.dump(self.settings, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"Error saving settings: {str(e)}")

    def add_index(self, path):
        if 'indexes' not in self.settings:
            self.settings['indexes'] = []
        if path not in [idx['path'] for idx in self.settings['indexes']]:
            self.settings['indexes'].append({
                'path': path,
                'name': os.path.basename(path),
                'created': datetime.now().isoformat()
            })
            # תמיד הוסף ל-selected_indexes כברירת מחדל
            if 'selected_indexes' not in self.settings:
                self.settings['selected_indexes'] = []
            if path not in self.settings['selected_indexes']:
                self.settings['selected_indexes'].append(path)
            self.save_settings()

    def remove_index(self, path):
        if 'indexes' in self.settings:
            self.settings['indexes'] = [idx for idx in self.settings['indexes'] if idx['path'] != path]
        if 'selected_indexes' in self.settings:
            self.settings['selected_indexes'] = [p for p in self.settings['selected_indexes'] if p != path]
        self.save_settings()

    def get_selected_indexes(self):
        return self.settings.get('selected_indexes', [])

    def get_setting(self, key, default=None):
        return self.settings.get(key, default)


#--------------------
# אינדקסים
#---------------------
class FileIndex:
    def __init__(self, folder_path):
        self.folder_path = folder_path
        self.app_data_path = get_app_data_path()
        self._optimized_index = OptimizedFileIndex(folder_path)
        self.index_file = self._optimized_index.db_path
        self.inverted_file = self._optimized_index.db_path
        self.chunk_size = self._optimized_index.chunk_size
        self.cache = LRUCache(100)

    def get_files(self):
        """מחזיר את רשימת הקבצים מהאינדקס"""
        try:
            with sqlite3.connect(self._optimized_index.db_path) as conn:
                cursor = conn.execute("SELECT path, filename FROM files")
                return {row[0]: {'filename': row[1]} for row in cursor.fetchall()}
        except Exception as e:
            logging.error(f"Error getting files: {e}")
            return {}

    def get_index_file_path(self):
        """שמירה על תאימות לאחור"""
        return self._optimized_index.db_path

    def get_inverted_file_path(self):
        """שמירה על תאימות לאחור"""
        return self._optimized_index.db_path

    def load_index(self):
        """טעינת אינדקס - מתאם לממשק הישן"""
        try:
            with sqlite3.connect(self._optimized_index.db_path) as conn:
                results = {}
                for row in conn.execute("SELECT path, hash, filename FROM files"):
                    contents = []
                    for content in conn.execute("SELECT location, content FROM content WHERE file_path = ?", (row[0],)):
                        contents.append({
                            'content': content[1],
                            'page': content[0]
                        })
                    results[row[0]] = {
                        'hash': row[1],
                        'filename': row[2],
                        'contents': contents
                    }
                return results
        except Exception as e:
            logging.error(f"Error loading index: {e}")
            return {}

    def save_index(self):
        """שמירת אינדקס - לא נדרש בגישה החדשה"""
        pass  # הכל נשמר אוטומטית ב-SQLite

    def delete_index_file(self):
        """מחיקת קובץ האינדקס"""
        try:
            if hasattr(self, '_optimized_index'):
                db_path = self._optimized_index.db_path
                if os.path.exists(db_path):
                    # סגירת כל החיבורים לבסיס הנתונים
                    import gc
                    gc.collect()

                    # ניסיון למחיקה עם מספר ניסיונות
                    max_attempts = 5
                    for attempt in range(max_attempts):
                        try:
                            # שחרור החיבורים הפתוחים
                            if hasattr(self, '_conn'):
                                self._conn.close()
                                delattr(self, '_conn')
                            
                            os.remove(db_path)
                            break
                        except (PermissionError, OSError) as e:
                            if attempt < max_attempts - 1:
                                import time
                                time.sleep(1)  # המתנה בין ניסיונות
                                gc.collect()
                            else:
                                raise
        except Exception as e:
            logging.error(f"Error deleting index: {e}")
            import traceback
            logging.error(traceback.format_exc())

    def get_file_hash(self, file_path):
        """חישוב hash של קובץ"""
        return self._optimized_index._get_file_hash(file_path)

    def needs_update(self):
        """בדיקה אם נדרש עדכון"""
        try:
            if not os.path.exists(self._optimized_index.db_path):
                return True
                
            with sqlite3.connect(self._optimized_index.db_path) as conn:
                count = conn.execute("SELECT COUNT(*) FROM files").fetchone()[0]
                if count == 0:
                    return True
                    
                # בדיקת קבצים חדשים או שהשתנו
                for file_path in self._get_indexable_files():
                    file_hash = self.get_file_hash(file_path)
                    stored_hash = conn.execute(
                        "SELECT hash FROM files WHERE path = ?", 
                        (file_path,)
                    ).fetchone()
                    
                    if not stored_hash or stored_hash[0] != file_hash:
                        return True
                        
            return False
            
        except Exception as e:
            logging.error(f"Error checking for updates: {e}")
            return True

    def _get_indexable_files(self):
        """גנרטור שמחזיר את כל הקבצים לאינדוקס"""
        for root, _, files in os.walk(self.folder_path):
            for file in files:
                if file.lower().endswith(('.pdf', '.docx', '.txt', '.doc')):
                    yield os.path.join(root, file)

    def update_index(self, callback=None):
        """עדכון האינדקס"""
        try:
            # ספירת קבצים
            total_files = sum(1 for _ in self._get_indexable_files())
            files_processed = 0
            
            # עיבוד קבצים באצוות
            batch = []
            batch_size = 10
            
            for file_path in self._get_indexable_files():
                batch.append(file_path)
                
                if len(batch) >= batch_size:
                    self._process_batch(batch, files_processed, total_files, callback)
                    files_processed += len(batch)
                    batch = []
                    gc.collect()
            
            # טיפול בשארית
            if batch:
                self._process_batch(batch, files_processed, total_files, callback)
                files_processed += len(batch)
            
        except Exception as e:
            logging.error(f"Error updating index: {e}")
        finally:
            gc.collect()

    def _process_batch(self, file_paths, current_count, total_files, callback):
        """עיבוד אצוות קבצים"""
        for file_path in file_paths:
            try:
                self._optimized_index.process_file(file_path)
                if callback:
                    callback(current_count + 1, total_files)
            except Exception as e:
                logging.error(f"Error processing file {file_path}: {e}")

    def search(self, query, search_options=None, max_results=1000):
        """חיפוש עם תאימות לממשק הקיים"""
        # בדיקת מטמון
        cache_key = f"{query}_{str(search_options.__dict__ if search_options else {})}_{max_results}"
        cached_result = self.cache.get(cache_key)
        if cached_result:
            return cached_result

        # המרת אפשרויות החיפוש
        search_params = {
            'exact_match': getattr(search_options, 'exact_match', False),
            'match_all_words': getattr(search_options, 'match_all_words', True),
            'exclude_words': getattr(search_options, 'exclude_words', []),
            'max_results': max_results,
            'context_words': getattr(search_options, 'default_context_words', 200)
        }

        # ביצוע החיפוש
        results = self._optimized_index.search(query, search_options, max_results)
        
        # התאמת פורמט התוצאות
        formatted_results = []
        for result in results:
            formatted_result = {
                "filename": result["filename"],
                "file_path": result["file_path"],
                "context": result["context"],
                "location": result["location"],
                "relevance_score": result.get("relevance_score", 0)
            }
            formatted_results.append(formatted_result)

        # שמירה במטמון
        self.cache.set(cache_key, formatted_results)
        return formatted_results

    def _optimize_context(self, text, query_words, search_options):
        """אופטימיזציה של טקסט ההקשר"""
        return self._optimized_index._optimize_context(
            text, 
            query_words, 
            getattr(search_options, 'default_context_words', 200)
        )

    # שמירת המתודות הקיימות לתאימות לאחור
    get_all_documents = lambda self: []  # לא בשימוש עם המנוע החדש
    extract_pdf_content_optimized = lambda self, fp: self._optimized_index._extract_pdf_content(fp)
    extract_txt_content_optimized = lambda self, fp: self._optimized_index._extract_txt_content(fp)
    extract_docx_content = lambda self, fp: self._optimized_index._extract_docx_content(fp)
    get_location_info = lambda self, item: self._optimized_index._format_location(item)
    get_context = lambda self, *args: self._optimized_index._optimize_context(*args)

#-------------------------------
#   מחלקה ראשית
#--------------------------------
class DocumentSearchApp:
    def __init__(self, page: Page):
        self.page = page
        self.page.title = "מנוע חיפוש מסמכים"
        self.page.rtl = True
        self.search_options = SearchOptions()
        self.status_timer = None
        self.current_book_path = None
        self.current_book_pages = []
        self.current_page_index = 0
        self.search_history = SearchHistory()
        self.app_settings = AppSettings()
        self.force_book_path = None
        self.index_list = []
        self.book_search_term = None
        self.book_search_matches = []
        self.current_search_results = []
        self.book_search_current = 0
        self.selected_file_types = self.app_settings.settings.get('file_types', [".pdf", ".docx", ".txt"])
        self.word_distance = self.app_settings.settings.get('word_distance', 0)
        self.search_options.file_types = self.selected_file_types
        self.search_options.word_distance = self.word_distance
        self.filter_row = self.create_file_type_buttons_row()
        self.last_results_scroll_key = None
        self.pinned_result_key = None
        
        self.apply_theme_settings()
        self.init_components()
        self.setup_ui()

        def schedule_cleanup():
            self.cleanup_indexes()
            Timer(24 * 60 * 60, schedule_cleanup).start()
        
        Timer(60, schedule_cleanup).start()

    def get_results_font_size(self):
        font_size_map = {
            "small": 13,
            "normal": 16,
            "large": 20
        }
        return font_size_map.get(self.app_settings.get_setting('font_size', 'normal'), 16)        

    def get_selected_file_types(self):
        """מחזיר את סוגי הקבצים הנבחרים"""
        return self.selected_file_types if hasattr(self, 'selected_file_types') else [".pdf", ".docx", ".txt"]

    def update_search_setting(self, setting_name: str, value):
        """עדכון הגדרת חיפוש"""
        self.app_settings.settings[setting_name] = value
        self.app_settings.save_settings()
        
        # עדכון אפשרויות החיפוש
        if setting_name == 'search_filenames_only':
            self.search_options.search_in_path = value
        elif setting_name == 'exact_match':
            self.search_options.exact_match = value
        elif setting_name == 'min_word_count':
            self.search_options.min_word_count = value
        
        # ביצוע חיפוש מחדש אם יש מילות חיפוש
        if hasattr(self, 'search_term') and self.search_term.value:
            self.search_documents(None)

    def create_file_type_buttons_row(self):
        """יצירת שורת סינון סוגי קבצים"""
        import flet as ft
        
        file_types = self.get_selected_file_types()
        return ft.Row([
            ft.Text("סוגי קבצים:", size=14),
            ft.ElevatedButton(
                text="PDF",
                data=".pdf",
                bgcolor=ft.Colors.PRIMARY if ".pdf" in file_types else ft.Colors.SURFACE,
                color=ft.Colors.ON_PRIMARY if ".pdf" in file_types else ft.Colors.ON_SURFACE,
                on_click=self.toggle_file_filter
            ),
            ft.ElevatedButton(
                text="Word",
                data=".docx",
                bgcolor=ft.Colors.PRIMARY if ".docx" in file_types else ft.Colors.SURFACE,
                color=ft.Colors.ON_PRIMARY if ".docx" in file_types else ft.Colors.ON_SURFACE,
                on_click=self.toggle_file_filter
            ),
            ft.ElevatedButton(
                text="Text",
                data=".txt",
                bgcolor=ft.Colors.PRIMARY if ".txt" in file_types else ft.Colors.SURFACE,
                color=ft.Colors.ON_PRIMARY if ".txt" in file_types else ft.Colors.ON_SURFACE,
                on_click=self.toggle_file_filter
            ),
            ft.Container(width=20),
            ft.Text("מרחק בין מילים:", size=14),
            ft.TextField(
                value=str(self.word_distance),
                width=60,
                on_change=self.update_word_distance,
            ),
        ], spacing=10, alignment=ft.MainAxisAlignment.END)

    def toggle_file_filter(self, e):
        """עדכון סינון סוגי קבצים"""
        file_type = e.control.data
        file_types = self.get_selected_file_types().copy()
        if file_type in file_types:
            file_types.remove(file_type)
        else:
            file_types.append(file_type)
        self.selected_file_types = file_types
        self.search_options.file_types = file_types
        self.app_settings.settings['file_types'] = file_types
        self.app_settings.save_settings()

        # עדכון שורת הכפתורים בלבד
        self.filter_row.controls = self.create_file_type_buttons_row().controls

        self.page.update()

        # בצע חיפוש אם יש טקסט
        if self.search_term.value:
            self.search_documents(None)

    def toggle_advanced_settings(self, e):
        self.advanced_settings.visible = not self.advanced_settings.visible
        # עדכן צבע בהתאם למצב
        self.toggle_advanced_button.bgcolor = ft.Colors.BLUE_GREY if self.advanced_settings.visible else ft.Colors.SURFACE
        self.toggle_advanced_button.icon_color = ft.Colors.ON_PRIMARY if self.advanced_settings.visible else ft.Colors.BLUE_GREY
        self.toggle_advanced_button.update()
        self.advanced_settings.update()
    
    def update_word_distance(self, e):
        try:
            distance = int(e.control.value)
            if distance < 0:
                e.control.value = "0"
                distance = 0
            self.word_distance = distance
            self.search_options.word_distance = distance if distance > 0 else None
            self.app_settings.settings['word_distance'] = distance
            self.app_settings.save_settings()
        except ValueError:
            e.control.value = "0"
            self.word_distance = 0
            self.search_options.word_distance = None
            self.app_settings.settings['word_distance'] = 0
            self.app_settings.save_settings()


    def init_components(self):
        """אתחול כל הרכיבים הדרושים"""
        # רכיב הודעות
        self.message_container = Container(
            content=Row(
                controls=[
                    Icon(ft.Icons.INFO_OUTLINE, color=ft.Colors.WHITE),
                    Text("", color=ft.Colors.WHITE, size=16),
                ],
                alignment=ft.MainAxisAlignment.CENTER
            ),
            visible=False,
            bgcolor=ft.Colors.BLUE,
            padding=15,
            height=50,
            alignment=ft.alignment.center,
        )
        
        # אתחול מנגנוני חיפוש
        self.file_index = None
        self.folder_path = None
        #self.search_options = SearchOptions()
        
        # בחירת תיקייה וחיפוש
        self.folder_picker = FilePicker(on_result=self.pick_folder_result)
        self.selected_folder = Text("לא נבחרה תיקייה")
        self.search_term = TextField(
            label="מילות חיפוש",
            width=400,
            prefix_icon=ft.Icons.SEARCH,
            on_submit=self.search_documents,
        )
        
        # רכיבי התקדמות
        self.index_progress = Container(
            content=Column(
                controls=[
                    ProgressRing(),
                    Text("", size=16, color=ft.Colors.BLUE)
                ],
                horizontal_alignment="center"
            ),
            alignment=ft.alignment.center,
            visible=False
        )
        
        self.search_progress = Container(
            content=Column(
                controls=[
                    ProgressRing(),
                    Text("מחפש...", size=16, color=ft.Colors.BLUE)
                ],
                horizontal_alignment="center"
            ),
            alignment=ft.alignment.center,
            visible=False
        )
        
        # יצירת תצוגות
        self.search_view = self.create_search_view()
        self.books_view = self.create_books_view()
        self.books_view.visible = False
        self.settings_view = self.create_settings_view()
        
        # סרגל ניווט
        self.navigation_bar = NavigationBar(
            destinations=[
                NavigationBarDestination(
                    icon=ft.Icons.SEARCH,
                    label="חיפוש",
                ),
                NavigationBarDestination(
                    icon=ft.Icons.BOOK,
                    label="ספרים",
                ),
                NavigationBarDestination(
                    icon=ft.Icons.SETTINGS,
                    label="הגדרות",
                ),
            ],
            on_change=self.navigation_change,
            selected_index=0,
        )

    def create_search_view(self):
        import flet as ft

        self.results_counter = ft.Text("", size=14, color=ft.Colors.BLUE_GREY)

        # פאנל הגדרות מתקדמות - צף בצד ימין
        self.advanced_settings = ft.Container(
            content=self.build_advanced_settings_panel(),
            visible=False,
            padding=10,
            border_radius=8,
            bgcolor=ft.Colors.SURFACE,
            border=ft.border.all(1, ft.Colors.OUTLINE),
            shadow=ft.BoxShadow(
                spread_radius=1,
                blur_radius=8,
                color=ft.Colors.with_opacity(0.12, ft.Colors.BLACK),
            ),
            margin=10,
            left=10,   # ימין
            top=1,     # גובה מתחת לשורת החיפוש
            alignment=ft.alignment.top_right,
            width=None,
            height=None,
        )

        self.results_list = ft.ListView(
            expand=True,
            spacing=10,
            padding=10,
        )
        self.results_container = ft.Container(
            content=ft.Column(
                controls=[
                    self.results_counter,
                    self.search_progress,
                    self.results_list
                ],
                expand=True
            ),
            expand=True,
            height=600
        )

        self.toggle_advanced_button = ft.IconButton(
            icon=ft.Icons.TUNE,
            tooltip="הגדרות מתקדמות",
            on_click=self.toggle_advanced_settings,
            bgcolor=ft.Colors.BLUE_GREY if self.advanced_settings.visible else ft.Colors.SURFACE,
            icon_color=ft.Colors.ON_PRIMARY if self.advanced_settings.visible else ft.Colors.BLUE_GREY,
        )

        self.history_popup = ft.Container(
            content=ft.Column(
                controls=[],
                spacing=2,
                scroll=ft.ScrollMode.AUTO,
                horizontal_alignment=ft.CrossAxisAlignment.STRETCH,
            ),
            bgcolor=ft.Colors.SURFACE,
            border=ft.border.all(1, ft.Colors.OUTLINE),
            border_radius=8,
            padding=ft.padding.symmetric(vertical=5),
            margin=ft.margin.only(top=5),
            visible=False,
            width=400,
            shadow=ft.BoxShadow(
                spread_radius=1,
                blur_radius=8,
                color=ft.Colors.with_opacity(0.2, ft.Colors.BLACK),
            ),
            right=20,
            top=100,
            alignment=ft.alignment.top_right,
        )


    def create_search_view(self):
        import flet as ft

        self.results_counter = ft.Text("", size=14, color=ft.Colors.BLUE_GREY)

        # פאנל הגדרות מתקדמות - צף בצד ימין
        self.advanced_settings = ft.Container(
            content=self.build_advanced_settings_panel(),
            visible=False,
            padding=10,
            border_radius=8,
            bgcolor=ft.Colors.SURFACE,
            border=ft.border.all(1, ft.Colors.OUTLINE),
            shadow=ft.BoxShadow(
                spread_radius=1,
                blur_radius=8,
                color=ft.Colors.with_opacity(0.12, ft.Colors.BLACK),
            ),
            margin=10,
            left=10,   # ימין
            top=1,     # גובה מתחת לשורת החיפוש
            alignment=ft.alignment.top_right,
            width=None,
            height=None,
        )

        self.results_list = ft.ListView(
            expand=True,
            spacing=10,
            padding=10,
        )
        self.results_container = ft.Container(
            content=ft.Column(
                controls=[
                    self.results_counter,
                    self.search_progress,
                    self.results_list
                ],
                expand=True
            ),
            expand=True,
            height=600
        )

        self.toggle_advanced_button = ft.IconButton(
            icon=ft.Icons.TUNE,
            tooltip="הגדרות מתקדמות",
            on_click=self.toggle_advanced_settings,
            bgcolor=ft.Colors.BLUE_GREY if self.advanced_settings.visible else ft.Colors.SURFACE,
            icon_color=ft.Colors.ON_PRIMARY if self.advanced_settings.visible else ft.Colors.BLUE_GREY,
        )

        self.history_popup = ft.Container(
            content=ft.Column(
                controls=[],
                spacing=2,
                scroll=ft.ScrollMode.AUTO,
                horizontal_alignment=ft.CrossAxisAlignment.STRETCH,
            ),
            bgcolor=ft.Colors.SURFACE,
            border=ft.border.all(1, ft.Colors.OUTLINE),
            border_radius=8,
            padding=ft.padding.symmetric(vertical=5),
            margin=ft.margin.only(top=5),
            visible=False,
            width=400,
            shadow=ft.BoxShadow(
                spread_radius=1,
                blur_radius=8,
                color=ft.Colors.with_opacity(0.2, ft.Colors.BLACK),
            ),
            right=20,
            top=100,
            alignment=ft.alignment.top_right,
        )

        def on_search_focus(e):
            self.history_popup.visible = True
            self.history_popup.content.controls = [
                self.create_history_item(term) for term in self.search_history.get_history()[:5]
            ]
            self.history_popup.update()

        def on_search_blur(e):
            import threading
            def hide():
                self.history_popup.visible = False
                self.history_popup.update()
            threading.Timer(0.15, hide).start()

        self.search_term = ft.TextField(
            hint_text="הקלד טקסט לחיפוש...",
            width=600,
            expand=False,
            on_focus=on_search_focus,
            on_blur=on_search_blur,
            on_submit=self.search_documents,
            border_radius=8,
            filled=True,
        )

        # קבוצה ימנית: שדה חיפוש + כפתור חיפוש + כפתור הגדרות
        right_controls = ft.Row([
            self.search_term,
            ft.IconButton(
                icon=ft.Icons.SEARCH,
                tooltip="חפש",
                on_click=self.search_documents
            ),
            self.toggle_advanced_button,
        ], spacing=10, alignment=ft.MainAxisAlignment.START, vertical_alignment=ft.CrossAxisAlignment.CENTER)

        # שורת עליונה: חיפוש מימין בלבד (בלי הגדרות מתקדמות בשורה)
        top_row = ft.Row([
            right_controls
        ], spacing=0, alignment=ft.MainAxisAlignment.SPACE_BETWEEN, vertical_alignment=ft.CrossAxisAlignment.CENTER)

        main_column = ft.Column([
            ft.Text("חיפוש בספרייה", size=30, weight="bold"),
            top_row,
            self.results_container,
        ])

        return ft.Container(
            content=ft.Stack([
                main_column,
                self.history_popup,
                self.advanced_settings,  # advanced_settings צף מעל התוצאות (צד ימין)
            ]),
            expand=True,
            padding=20,
        )

    def create_index_list(self):
        """יצירת רשימת האינדקסים"""
        index_list = ft.Column(spacing=10)
        for idx in self.app_settings.settings.get('indexes', []):
            index_list.controls.append(
                ft.Container(
                    content=ft.Row([
                        ft.Icon(ft.Icons.FOLDER),
                        ft.Column([
                            ft.Text(idx['name'], size=14, weight=ft.FontWeight.BOLD),
                            ft.Text(
                                idx['path'], 
                                size=12, 
                                color=ft.Colors.GREY_500,
                                overflow=ft.TextOverflow.ELLIPSIS
                            )
                        ], expand=True),
                        ft.IconButton(
                            icon=ft.Icons.DELETE_OUTLINE,
                            tooltip="מחק אינדקס",
                            data=idx['path'],
                            on_click=self.remove_index
                        )
                    ]),
                    padding=10,
                    border=ft.border.all(1, ft.Colors.OUTLINE),
                    border_radius=5,
                    bgcolor=ft.Colors.SURFACE
                )
            )
        return index_list    

    def update_search_setting(self, setting_name: str, value):
        """עדכון הגדרת חיפוש"""
        self.app_settings.settings[setting_name] = value
        self.app_settings.save_settings()
        
        # עדכון אפשרויות החיפוש
        if setting_name == 'search_filenames_only':
            self.search_options.search_in_path = value
        elif setting_name == 'exact_match':
            self.search_options.exact_match = value
        elif setting_name == 'min_word_count':
            self.search_options.min_word_count = value
        
        # ביצוע חיפוש מחדש אם יש מילות חיפוש
        if hasattr(self, 'search_term') and self.search_term.value:
            self.search_documents(None)
            


    def create_settings_view(self):
        """יצירת דף ההגדרות"""
        color_options = [
            ('#0078D4', 'כחול'),
            ('#107C10', 'ירוק'),
            ('#D83B01', 'כתום'),
            ('#E81123', 'אדום'),
            ('#744DA9', 'סגול'),
            ('#018574', 'טורקיז'),
            ('#C239B3', 'ורוד'),
        ]

        def create_color_button(color, is_selected):
            return ft.Container(
                content=ft.Container(
                    bgcolor=color,
                    width=30,
                    height=30,
                    border_radius=15,
                    border=ft.border.all(2, ft.Colors.BLACK if is_selected else "transparent"),
                ),
                on_click=lambda _: self.change_primary_color(color),
                padding=5,
            )

        # לשונית ניהול אינדקסים
        index_management = ft.Container(
            content=ft.Column(
                controls=[
                    ft.Text("ניהול תיקיות אינדקס", size=16, weight=ft.FontWeight.BOLD),
                    ft.Row([
                        ft.IconButton(
                            icon=ft.Icons.FOLDER_OPEN,
                            tooltip="הוסף תיקייה",
                            on_click=lambda _: self.folder_picker.get_directory_path()
                        ),
                        ft.IconButton(
                            icon=ft.Icons.REFRESH,
                            tooltip="רענן אינדקס",
                            on_click=self.refresh_index
                        )
                    ]),
                    self.index_progress,
                    ft.Divider(),
                    ft.Text("אינדקסים קיימים:", size=14),
                    self.create_index_list(),
                ],
                scroll=ft.ScrollMode.AUTO  # מאפשר גלילה עבור תוכן ארוך
            ),
            padding=20
        )

        # לשונית הגדרות חיפוש
        search_settings = ft.Container(
            content=ft.Column(
                controls=[
                    ft.Text("הגדרות חיפוש", size=16, weight=ft.FontWeight.BOLD),
                    ft.Text("בחר אינדקסים לחיפוש:", size=14),
                    ft.Container(  # Container ייעודי לתיבות הסימון
                        data="checkbox_list",  # מזהה ייחודי
                        content=self.create_index_checkbox_list()
                    ),
                    ft.Divider(),
                    ft.Text("אפשרויות חיפוש נוספות:", size=14),
                    ft.Container(
                        content=ft.Column([
                            ft.Text("מיון תוצאות", size=14),
                            ft.Dropdown(
                                width=200,
                                value=self.app_settings.get_setting('results_sort', 'score'),
                                options=[
                                    ft.dropdown.Option("score", "תוצאות מובילות"),
                                    ft.dropdown.Option("abc", "א-ב (שם ספר)"),
                                    ft.dropdown.Option("index_order", "סדר האינדקסים"),
                                ],
                                on_change=self.change_results_sort
                            ),
                            ft.Divider(),
                            ft.Text("הגבלת מספר תוצאות", size=14),
                            ft.TextField(
                                value=str(self.app_settings.get_setting('max_results', 100)),
                                width=60,
                                keyboard_type=ft.KeyboardType.NUMBER,
                                on_change=self.change_max_results
                            ),
                        ]),
                        padding=10
                    )
                ],
                scroll=ft.ScrollMode.AUTO
            ),
            padding=20
        )


        # לשונית עיצוב
        theme_settings = ft.Container(
            content=ft.Column(
                controls=[
                    ft.Text("ערכת נושא", size=16, weight=ft.FontWeight.BOLD),
                    ft.RadioGroup(
                        content=ft.Column([
                            ft.Radio(value="light", label="בהיר"),
                            ft.Radio(value="dark", label="כהה"),
                            ft.Radio(value="system", label="לפי מערכת ההפעלה")
                        ]),
                        value=self.app_settings.get_setting('theme'),
                        on_change=self.change_theme
                    ),
                    ft.Divider(),
                    ft.Text("צבע ראשי", size=14),
                    ft.Row(
                        controls=[
                            create_color_button(
                                color,
                                color == self.app_settings.get_setting('primary_color')
                            ) for color, _ in color_options
                        ],
                        wrap=True,
                    ),
                    ft.Divider(),
                    ft.Text("גודל טקסט בתצוגת תוצאות", size=14),
                        ft.Dropdown(
                            width=200,
                            value=self.app_settings.get_setting('font_size'),
                            options=[
                                ft.dropdown.Option("small", text="קטן"),
                                ft.dropdown.Option("normal", text="רגיל"),
                                ft.dropdown.Option("large", text="גדול")
                            ],
                            on_change=self.change_font_size
                    ),
                    ft.Divider(),
                    ft.Text("מספר מילים סביב ההתאמה בתוצאה", size=14),
                    ft.Row([
                        ft.Text("הצג סביב כל התאמה:", size=13),
                        ft.TextField(
                            value=str(self.app_settings.get_setting('default_context_words', 12)),
                            width=60,
                            keyboard_type=ft.KeyboardType.NUMBER,
                            on_change=self.change_context_words
                        ),
                        ft.Text("מילים", size=13)
                    ], spacing=8),
                    ft.Switch(
                        label="הפעל חלון במקסימום (בעת ההפעלה הבאה)",
                        value=self.app_settings.get_setting('window_maximized', True),
                        on_change=self.change_window_maximized
                    ),
                ],
                scroll=ft.ScrollMode.AUTO  # מאפשר גלילה עבור תוכן ארוך
            ),
            padding=20
        )

        # יצירת המכל הראשי עם כל הלשוניות
        return ft.Container(
            content=ft.Column([
                ft.Container(
                    content=ft.Text("הגדרות", size=30, weight="bold"),
                    margin=ft.margin.only(bottom=20)
                ),
                ft.Tabs(
                    selected_index=0,
                    animation_duration=300,
                    tabs=[
                        ft.Tab(text="תיקיות אינדקס", content=index_management),
                        ft.Tab(text="הגדרות חיפוש", content=search_settings),
                        ft.Tab(text="עיצוב", content=theme_settings),
                    ],
                    expand=True
                )
            ]),
            visible=False,
            expand=True,
            padding=20
        )

    def setup_ui(self):
        self.create_views()
        self.main_stack = ft.Stack([
            self.search_view,
            self.books_view,
            self.settings_view,
        ], expand=True)
        self.main_container = ft.Container(
            content=ft.Column([
                self.main_stack,
                self.navigation_bar,
                self.message_container,
            ]),
            expand=True,
        )
        self.page.padding = 0
        self.page.spacing = 0
        self.page.overlay.append(self.folder_picker)
        self.page.add(self.main_container)

    def create_views(self):
        # כל פעם שמרעננים, בונים מחדש את כל ה־views!
        self.search_view = self.create_search_view()
        self.books_view = self.create_books_view()
        self.settings_view = self.create_settings_view()
        self.search_view.visible = self.navigation_bar.selected_index == 0
        self.books_view.visible = self.navigation_bar.selected_index == 1
        self.settings_view.visible = self.navigation_bar.selected_index == 2
        
    def refresh_all_views(self):
        # קרא את זה בכל שינוי אינדקס!
        self.create_views()
        self.main_stack.controls.clear()
        self.main_stack.controls.extend([
            self.search_view,
            self.books_view,
            self.settings_view,
        ])
        self.page.update()

    def show_history(self, e):
        """הצגת או הסתרת היסטוריית החיפושים"""
        # מחליף את המצב הנוכחי - אם מוצג מסתיר, אם מוסתר מציג
        self.history_popup.visible = not self.history_popup.visible
        self.history_popup.update()

    def hide_history(self, e):
        """הסתרת היסטוריית החיפושים"""
        self.history_popup.visible = False
        self.history_popup.update()
        
    def select_history_item(self, term):
        """בחירת פריט מההיסטוריה"""
        self.search_term.value = term
        self.search_term.update()
        self.history_popup.visible = False
        self.history_popup.update()
        self.search_documents(None)  # ביצוע חיפוש אוטומטי

    def remove_from_history(self, term):
        """הסרת פריט מההיסטוריה"""
        self.search_history.remove_item(term)
        # עדכון תצוגת ההיסטוריה
        self.history_popup.content.controls = [
            self.create_history_item(term) 
            for term in self.search_history.get_history()
        ]
        self.history_popup.update()

    def apply_theme_settings(self):
        """החלת הגדרות העיצוב"""
        try:
            # החלת ערכת נושא
            theme = self.app_settings.get_setting('theme', 'light')
            if theme == "dark":
                self.page.theme_mode = ThemeMode.DARK
            elif theme == "light":
                self.page.theme_mode = ThemeMode.LIGHT
            else:  # system
                self.page.theme_mode = ThemeMode.SYSTEM

            # החלת צבע ראשי
            primary_color = self.app_settings.get_setting('primary_color', '#0078D4')
            self.page.theme = Theme(color_scheme_seed=primary_color)
            
            # החלת גודל טקסט
            font_size = self.app_settings.get_setting('font_size', 'normal')
            font_sizes = {
                'small': 0.8,
                'normal': 1.0,
                'large': 1.2
            }
            self.font_scale = font_sizes.get(font_size, 1.0)
            
        except Exception as e:
            print(f"שגיאה בהחלת הגדרות עיצוב: {str(e)}")        

    def navigation_change(self, e):
        selected_index = e.control.selected_index

        # שמירת מיקום גלילה – עדיף לנעוץ אם יש
        if self.pinned_result_key:
            self.last_results_scroll_key = self.pinned_result_key
        elif self.results_list.controls:
            self.last_results_scroll_key = self.results_list.controls[0].key
        else:
            self.last_results_scroll_key = None

        self.search_view.visible = selected_index == 0
        self.books_view.visible = selected_index == 1
        self.settings_view.visible = selected_index == 2

        self.message_container.visible = False

        if selected_index == 1:  # תצוגת ספרים
            books = []
            for idx in self.app_settings.get_selected_indexes():
                try:
                    file_index = FileIndex(idx)
                    files = file_index.get_files()
                    for file_path, file_data in files.items():
                        if file_path.lower().endswith('.pdf'):
                            books.append((file_path, file_data))
                except Exception as e:
                    print(f"Error loading index {idx}: {str(e)}")
                    continue

            books.sort(key=lambda x: x[1]['filename'])
            if books:
                if self.force_book_path:
                    self.select_book(self.force_book_path)
                    self.force_book_path = None
                else:
                    self.select_book(books[0][0])

        # גלילה לנעץ בכל מעבר לדף החיפוש
        if selected_index == 0 and self.pinned_result_key:
            from threading import Timer
            Timer(0.9, lambda: self.results_list.scroll_to(key=self.pinned_result_key, duration=200)).start()

        self.page.update()                

        
    def update_search_options(self, e):
        """עדכון אפשרויות החיפוש"""
        controls = self.search_controls.controls
        self.search_options.exact_match = controls[0].value
        self.search_options.search_in_path = controls[1].value
        self.page.update()

    def update_file_filters(self, e):
        """עדכון סינון סוגי קבצים"""
        # עדכון אפשרויות החיפוש
        selected_types = []
        for checkbox in self.filter_panel.controls[1].content.controls:
            if checkbox.value:
                selected_types.append(checkbox.data)
        
        self.search_options.file_types = selected_types
        
        # ביצוע חיפוש מחדש אם יש מילות חיפוש
        if self.search_term.value:
            self.search_documents(None)
            
    def create_history_item(self, search_term):
        return ft.Container(
            content=ft.TextButton(
                content=ft.Row([
                    ft.Container(
                        content=ft.Icon(ft.Icons.HISTORY, size=16, color=ft.Colors.GREY_500),
                        margin=ft.margin.only(right=10)
                    ),
                    ft.Text(
                        search_term,
                        size=14,
                        expand=True,
                        no_wrap=True,
                        overflow=ft.TextOverflow.ELLIPSIS
                    ),
                    ft.Container(
                        content=ft.IconButton(
                            icon=ft.Icons.CLOSE,
                            icon_size=16,
                            tooltip="הסר מההיסטוריה",
                            on_click=lambda e, term=search_term: self.remove_from_history(term)
                        ),
                        margin=ft.margin.only(left=10)
                    )
                ],
                alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                spacing=5
                ),
                # חיפוש מיידי בלחיצה!
                on_click=lambda _, term=search_term: self.select_history_item(term),
                style=ft.ButtonStyle(
                    padding=ft.padding.all(10),
                    bgcolor=ft.Colors.SURFACE,
                    shape=ft.RoundedRectangleBorder(radius=8),
                ),
                expand=True,
            ),
            padding=ft.padding.symmetric(horizontal=5),
            margin=ft.margin.only(bottom=2),
        )

    def select_history_item(self, term):
        self.search_term.value = term
        self.search_term.update()
        self.history_popup.visible = False
        self.history_popup.update()
        self.search_documents(None)  # חיפוש מיידי!

    def search_documents(self, e):
        self.search_options.exact_match = self.app_settings.get_setting('exact_match', False)
        self.search_options.match_all_words = True  # או לפי הגדרה אם יש
        self.search_options.word_distance = self.app_settings.get_setting('word_distance', 0)
        self.search_options.file_types = self.app_settings.get_setting('file_types', [".pdf", ".docx", ".txt"])
        self.search_options.default_context_words = self.app_settings.get_setting('default_context_words', 12)
        search_term = self.search_term.value
        if search_term and search_term.strip():
            self.search_history.add(search_term)
            self.history_popup.content.controls = [
                self.create_history_item(term) 
                for term in self.search_history.get_history()
            ]
            self.history_popup.update()
        
        self.results_list.controls.clear()
        self.results_counter.value = ""
        
        if not self.search_term.value:
            self.show_status("נא להזין טקסט לחיפוש", True)
            return

        self.search_progress.visible = True
        self.page.update()

        all_results = []  # ←←← אתחול בכל מקרה
        self.current_search_results = all_results  # ← זה הקריטי!
        self.results_list.controls = [
            self.create_result_container(result, idx)
            for idx, result in enumerate(all_results)
        ]
        self.results_list.update()

        try:
            selected_indexes = self.app_settings.get_selected_indexes()
            
            if self.search_options.search_in_path:
                # חיפוש בשמות קבצים בלבד
                for index_path in selected_indexes:
                    file_index = FileIndex(index_path)
                    with sqlite3.connect(file_index.index_file) as conn:
                        cursor = conn.execute("""
                            SELECT path, filename 
                            FROM files 
                            WHERE filename LIKE ?
                        """, (f"%{search_term}%",))
                        for row in cursor.fetchall():
                            all_results.append({
                                'file_path': row[0],
                                'filename': row[1],
                                'context': 'שם קובץ',
                                'location': 'שם קובץ',
                                'score': 50  # ניקוד בסיסי עבור חיפוש בשם
                            })
            else:
                # חיפוש בתוכן הקבצים
                for index_path in selected_indexes:
                    file_index = FileIndex(index_path)
                    results = file_index.search(self.search_term.value, self.search_options)
                    # הוסף index_path לכל תוצאה (חשוב למיון לפי אינדקס)
                    for res in results:
                        res['index_path'] = index_path
                    all_results.extend(results)

            # דירוג חכם לחיפוש בתוכן
            if not self.search_options.search_in_path:
                query_words = [w.lower() for w in self.search_term.value.split()]
                for res in all_results:
                    score = 0
                    if res.get("location", "") == "שם קובץ":
                        score += 30
                    if self.search_options.exact_match:
                        if all(qw in res['context'].lower().split() for qw in query_words):
                            score += 100
                    count = sum(res['context'].lower().count(qw) for qw in query_words)
                    score += count * 10
                    if self.search_term.value.strip().lower() in res['context'].lower():
                        score += 50
                    res['score'] = score

            # מיון התוצאות
            sort_type = self.app_settings.get_setting('results_sort', 'score')
            if sort_type == 'score':
                all_results.sort(key=lambda r: r['score'], reverse=True)
            elif sort_type == 'abc':
                # קודם ממיינים לפי שם הקובץ
                all_results.sort(key=lambda r: r['filename'])
                
                # אחר כך, מקבצים לפי שם קובץ וממיינים כל קבוצה לפי מספר העמוד
                from itertools import groupby
                sorted_results = []
                for filename, group in groupby(all_results, key=lambda r: r['filename']):
                    group_list = list(group)
                    # מיון לפי מספר העמוד (אם קיים)
                    group_list.sort(key=lambda r: int(r['location'].split()[-1]) if r['location'].split()[-1].isdigit() else 0)
                    sorted_results.extend(group_list)
                all_results = sorted_results

            elif sort_type == 'index_order':
                index_order = {idx['path']: i for i, idx in enumerate(self.app_settings.settings['indexes'])}
                all_results.sort(key=lambda r: (
                    index_order.get(r.get('index_path', ''), 999),
                    r['filename'],
                    int(r['location'].split()[-1]) if r['location'].split()[-1].isdigit() else 0
                ))

            max_results = self.app_settings.get_setting('max_results', 100)
            all_results = all_results[:max_results]

            if self.search_options.file_types:
                filtered_results = []
                for result in all_results:
                    for file_type in self.search_options.file_types:
                        if result['file_path'].lower().endswith(file_type.lower()):
                            filtered_results.append(result)
                            break
                all_results = filtered_results

            self.results_list.controls = [
                self.create_result_container(result, idx)
                for idx, result in enumerate(all_results)
            ]

            # גלול אוטומטית למיקום הנעוץ (אם יש)
            if self.pinned_result_key:
                def restore_pinned():
                    self.results_list.scroll_to(key=self.pinned_result_key, duration=300)
                Timer(0.15, restore_pinned).start()
    
            results_count = len(all_results)
            if results_count == 0:
                self.show_status(f"לא נמצאו תוצאות עבור '{self.search_term.value}'")
            else:
                self.results_counter.value = f"נמצאו {results_count} תוצאות"
                self.hide_status()

        finally:
            self.search_progress.visible = False
            self.page.update()

    def change_results_sort(self, e):
        """שינוי אופן מיון התוצאות"""
        sort_type = e.control.value
        self.app_settings.settings['results_sort'] = sort_type
        self.app_settings.save_settings()
        
        # במקום לרענן את כל התצוגה, נעדכן רק את התצוגה הנוכחית
        current_tab = None
        for control in self.settings_view.content.controls:
            if isinstance(control, ft.Tabs):
                current_tab = control.tabs[control.selected_index]
                break
                
        if current_tab:
            current_tab.update()
        
        self.page.update()

    def change_max_results(self, e):
        """שינוי מספר תוצאות מקסימלי"""
        try:
            value = int(e.control.value)
            if value < 1:
                value = 1
                e.control.value = "1"
                
            self.app_settings.settings['max_results'] = value
            self.app_settings.save_settings()
            
            # עדכון השדה עצמו בלבד
            e.control.update()
            
        except ValueError:
            e.control.value = str(self.app_settings.get_setting('max_results', 100))
            e.control.update()
                
    def change_theme(self, e):
        """שינוי ערכת הנושא"""
        theme = e.control.value
        if theme == "dark":
            self.page.theme_mode = ThemeMode.DARK
        elif theme == "light":
            self.page.theme_mode = ThemeMode.LIGHT
        else:  # system
            self.page.theme_mode = ThemeMode.SYSTEM
        
        self.app_settings.settings['theme'] = theme
        self.app_settings.save_settings()
        self.page.update()

    def change_primary_color(self, color):
        self.app_settings.settings['primary_color'] = color
        self.app_settings.save_settings()
        self.page.theme = Theme(color_scheme_seed=color)
        self.page.update()

    def refresh_results(self):
        try:
            # וידוא שכל רכיב מכיל נתונים תקפים
            all_results = [control.data for control in self.results_list.controls if hasattr(control, 'data')]
            
            if not all_results:
                print("DEBUG: No valid results to refresh.")
                return

            # יצירת תוצאות מעוצבות מחדש
            self.results_list.controls = [
                self.create_result_container(result) for result in all_results
            ]
            
            # עדכון התצוגה
            self.results_list.update()
            print("DEBUG: Results refreshed successfully.")
        except Exception as e:
            print(f"ERROR in refresh_results: {e}")
            
    def change_font_size(self, e):
        try:
            value = e.control.value
            self.app_settings.settings['font_size'] = value
            self.app_settings.save_settings()
            self.refresh_results()
        except Exception as ex:
            print(f"ERROR in change_font_size: {ex}")

        def is_valid_number(self, value):
            """בדיקה אם הערך הוא מספר"""
            try:
                int(value)
                return True
            except ValueError:
                return False

    def change_context_words(self, e):
        """שינוי מספר המילים סביב תוצאת החיפוש"""
        try:
            value = int(e.control.value)
            if value < 1:
                value = 1
                e.control.value = "1"
            
            # עדכון ההגדרות
            self.app_settings.settings['default_context_words'] = value
            self.app_settings.save_settings()
            
            # עדכון התצוגה של השדה עצמו בלבד
            e.control.update()
            
            # אם יש צורך בעדכון תוצאות החיפוש
            if hasattr(self, 'search_term') and self.search_term.value:
                self.search_documents(None)  # שימוש בפונקציה הקיימת במקום refresh_search_results
                
        except ValueError:
            # במקרה של ערך לא תקין
            e.control.value = str(self.app_settings.get_setting('default_context_words', 12))
            e.control.update()



    def create_result_container(self, result, idx):
        file_path = result['file_path']
        location = result.get('location', '')
        context = result['context']
        results_font_size = 16  # או לפי הגדרות משתמש
        exact_match = getattr(self.search_options, 'exact_match', False)
        spans = []
        pointer = 0
        text_lower = context.lower()
        search_term = self.search_term.value.strip()
        is_pinned = self.pinned_result_key == f"result_{idx}"


        if exact_match:
            # הדגשה רק של מופע מדויק כמילה שלמה
            pattern = r'\b' + re.escape(search_term) + r'\b'
            for match in re.finditer(pattern, context, re.IGNORECASE):
                start, end = match.span()
                if start > pointer:
                    spans.append(ft.TextSpan(text=context[pointer:start]))
                spans.append(ft.TextSpan(
                    text=context[start:end],
                    style=ft.TextStyle(
                        color=ft.Colors.RED,
                        weight=ft.FontWeight.BOLD,
                        size=results_font_size
                    )
                ))
                pointer = end
            if pointer < len(context):
                spans.append(ft.TextSpan(text=context[pointer:]))
        else:
            # הדגשה של כל מופע של המחרוזת גם אם היא חלק ממילה
            search_words = search_term.lower().split()
            positions = []
            for word in search_words:
                start = 0
                while True:
                    pos = text_lower.find(word, start)
                    if pos == -1:
                        break
                    positions.append((pos, pos + len(word)))
                    start = pos + len(word)
            positions.sort()
            pointer = 0
            for start, end in positions:
                if start > pointer:
                    spans.append(ft.TextSpan(text=context[pointer:start]))
                spans.append(ft.TextSpan(
                    text=context[start:end],
                    style=ft.TextStyle(
                        color=ft.Colors.RED,
                        weight=ft.FontWeight.BOLD,
                        size=results_font_size
                    )
                ))
                pointer = end
            if pointer < len(context):
                spans.append(ft.TextSpan(text=context[pointer:]))

        # אייקון "נעץ"
        pin_icon = ft.IconButton(
            icon=ft.Icons.PUSH_PIN,
            icon_size=20,
            tooltip="נעץ מיקום זה",
            icon_color=ft.Colors.RED if is_pinned else ft.Colors.GREY_500,
            on_click=lambda e, idx=idx: self.set_pinned_result(idx)
        )


        # אייקון עין לפתיחה מהירה
        preview_icon = ft.IconButton(
            icon=ft.Icons.VISIBILITY,
            icon_size=24,
            tooltip="תצוגה מקדימה/פתח במיקום",
            on_click=lambda e, file_path=file_path, location=location: self.open_book_at_search_result(
                file_path, location, self.search_term.value
            )
        )

        return ft.Container(
            key=f"result_{idx}",
            content=ft.Column([
                ft.Row([
                    ft.Icon(ft.Icons.DESCRIPTION, color=ft.Colors.BLUE),
                    ft.Text(
                        f"{result['filename']} ({location})",
                        size=results_font_size,
                        weight=ft.FontWeight.BOLD,
                        expand=True
                    ),
                    pin_icon,
                    preview_icon,
                ]),
                ft.Container(
                    content=ft.SelectionArea(
                        content=ft.Text(spans=spans, size=results_font_size)
                    ),
                    margin=ft.margin.only(left=20, top=5),
                    bgcolor=ft.Colors.BLUE_50,
                    padding=10,
                    border_radius=5,
                    expand=True,
                    on_click=lambda e: self.open_book_at_search_result(file_path, location)
                )
            ], expand=True),
            bgcolor=ft.Colors.WHITE,
            padding=10,
            border_radius=10,
            border=ft.border.all(1, ft.Colors.BLUE_GREY_200),
            expand=True
        )
    
    def set_pinned_result(self, idx):
        key = f"result_{idx}"
        if self.pinned_result_key == key:
            self.pinned_result_key = None
        else:
            self.pinned_result_key = key

        # בנה מחדש את הרשימה
        self.results_list.controls = [
            self.create_result_container(result, i)
            for i, result in enumerate(self.current_search_results)
        ]
        self.results_list.update()

        # הדפסה לdebug:
        print("כל ה-keys ברשימה:",
              [c.key for c in self.results_list.controls])
        print("גלילה אל:", self.pinned_result_key)

        # גלילה אוטומטית
        if self.pinned_result_key:
            def restore_pinned():
                print("מנסה לגלול אל:", self.pinned_result_key)
                self.results_list.scroll_to(key=self.pinned_result_key, duration=200)
            Timer(0.15, restore_pinned).start()
    
    def update_progress(self, current, total):
        """עדכון התקדמות האינדוקס"""
        self.index_progress.content.controls[1].value = f"מאנדקס {current}/{total} קבצים..."
        self.page.update()

    def pick_folder_result(self, e):
        if e.path:
            self.folder_path = e.path
            folder_name = os.path.basename(e.path)
            self.app_settings.add_index(e.path)
            file_index = FileIndex(e.path)
            try:
                if file_index.needs_update():
                    self.show_status("מאנדקס קבצים...")
                    self.index_progress.visible = True
                    self.page.update()
                    file_index.update_index(callback=self.update_progress)
                    self.index_progress.visible = False
                    self.show_status(f"האינדקס הושלם")
                else:
                    self.show_status(f"נטען אינדקס קיים")
            except Exception as e:
                self.show_status(f"שגיאה בעדכון האינדקס: {str(e)}", True)
            self.refresh_all_views()
            
    def remove_index(self, e):
        path = e.control.data
        self.app_settings.remove_index(path)
        file_index = FileIndex(path)
        file_index.delete_index_file()
        self.refresh_all_views()

    def cleanup_indexes(self):
        """ניקוי תקופתי של האינדקסים"""
        try:
            for idx in self.app_settings.settings.get('indexes', []):
                file_index = FileIndex(idx['path'])
                file_index._optimized_index.cleanup()
        except Exception as e:
            logging.error(f"Error during cleanup: {e}")
        

    def refresh_index(self, e=None):
        """מרענן את כל האינדקסים"""
        indexes = self.app_settings.settings.get('indexes', [])
        for idx in indexes:
            file_index = FileIndex(idx['path'])
            if file_index.needs_update():
                self.show_status(f"מעדכן אינדקס: {idx['name']}")
                self.index_progress.visible = True
                self.page.update()
                file_index.update_index(callback=self.update_progress)
                self.index_progress.visible = False
                self.show_status(f"האינדקס {idx['name']} עודכן בהצלחה")
                self.refresh_all_views() 
        self.page.update()


    def create_index_checkbox_list(self):
        import flet as ft
        from flet import Column, Container, Row, Checkbox, Icon, Text, border, ElevatedButton
        #print(f"Creating checkbox list with selected indexes: {self.app_settings.settings.get('selected_indexes', [])}")
        checkbox_list = Column(spacing=10)
        self.index_checkboxes = [] 
        selected_indexes = self.app_settings.settings.get('selected_indexes', [])
        all_indexes = [idx['path'] for idx in self.app_settings.settings['indexes']]

        # כפתורי בחר בכל / בטל הכל
        select_all_row = Row([
            ElevatedButton(
                text="בחר בכל",
                on_click=lambda e: self.select_all_indexes(True)
            ),
            ElevatedButton(
                text="בטל הכל",
                on_click=lambda e: self.select_all_indexes(False)
            )
        ], spacing=10)
        checkbox_list.controls.append(select_all_row)

        for idx in self.app_settings.settings['indexes']:
            is_selected = idx['path'] in selected_indexes
            checkbox = Checkbox(  # שמירת תיבת הסימון במשתנה
                value=is_selected,
                data=idx['path'],
                on_change=self.toggle_index_selection
            )
            self.index_checkboxes.append(checkbox)  # הוספת תיבת הסימון לרשימה
            
            checkbox_list.controls.append(
                Container(
                    content=Row([
                        checkbox,  # שימוש בתיבת הסימון שיצרנו
                        Icon(ft.Icons.FOLDER),
                        Text(idx['name'], expand=True),
                        Text(idx['path'], color=ft.Colors.GREY_500, size=12),
                    ]),
                    padding=10,
                    border=border.all(1, ft.Colors.BLUE_GREY_200),
                    border_radius=5
                )
            )

        if len(checkbox_list.controls) == 1:
            checkbox_list.controls.append(
                Text("אין אינדקסים מוגדרים", color=ft.Colors.GREY_500)
            )
        return checkbox_list
    def debug_settings_view(self):
        """Debug the structure of settings_view."""
        print("Debugging settings_view structure:")
        for control in self.settings_view.content.controls:
            print(f"Control: {type(control)}")
            if isinstance(control, ft.Tabs):
                for tab in control.tabs:
                    print(f"  Tab: {tab.text}")
                    if isinstance(tab.content, ft.Column):
                        for item in tab.content.controls:
                            print(f"    Item: {type(item)}, Data: {getattr(item, 'data', None)}")
                            
    def select_all_indexes(self, state):
        """Select or deselect all indexes."""
        for checkbox in self.index_checkboxes:
            checkbox.value = state
            checkbox.update()  # עדכון ויזואלי של כל תיבת סימון
            self.toggle_index_selection(ft.ControlEvent(target=checkbox, name="change", control=checkbox, data=str(state), page=self.page))
        
        # עדכון הרכיב האב שמכיל את כל תיבות הסימון
        self.settings_view.update()        
        # Instead of self.index_list.update(), you might want to do something like:
        # If you need to perform any operation on the index_list, do it here
        # For example, if you want to collect selected indexes:
        if state:
            self.index_list.extend([checkbox.value for checkbox in self.index_checkboxes if checkbox.value])
        else:
            self.index_list.clear()  # Clear the list if deselecting

    def toggle_index_selection(self, e):
        """טיפול בשינוי בחירת אינדקס"""
        index_path = e.control.data
        selected_indexes = self.app_settings.settings.get('selected_indexes', [])

        if e.control.value:  # אם האינדקס נבחר
            if index_path not in selected_indexes:
                selected_indexes.append(index_path)
        else:  # אם האינדקס בוטל
            if index_path in selected_indexes:
                selected_indexes.remove(index_path)

        self.app_settings.settings['selected_indexes'] = selected_indexes
        self.app_settings.save_settings()
        self.update_search_indexes()  # אופציונלי: עדכון לוגיקת מנוע החיפוש
        
        e.control.update()  # עדכון ויזואלי של תיבת הסימון הספציפית
        self.settings_view.update()  # עדכון הרכיב האב
        
    def show_status(self, message, is_error=False):
        """הצגת הודעת סטטוס עם טיימר"""
        if hasattr(self, 'status_timer') and self.status_timer:
            self.status_timer.cancel()
            self.status_timer = None

        self.message_container.bgcolor = ft.Colors.RED if is_error else ft.Colors.BLUE
        self.message_container.content.controls[1].value = message
        self.message_container.visible = True
        self.page.update()

        if not is_error:
            self.status_timer = Timer(3.0, self.hide_status)
            self.status_timer.start()

    def update_search_indexes(self):
        """עדכון האינדקסים לחיפוש במנוע החיפוש"""
        selected_indexes = self.app_settings.settings.get('selected_indexes', [])
        # אם אין אינדקסים נבחרים, נשתמש בכל האינדקסים
        if not selected_indexes:
            selected_indexes = [idx['path'] for idx in self.app_settings.settings['indexes']]
        
        # כאן נעדכן את הלוגיקה של החיפוש לפי האינדקסים שנבחרו
        self.search_options.selected_indexes = selected_indexes            

    def hide_status(self, e=None):
        """הסתרת הודעת סטטוס"""
        if hasattr(self, 'status_timer') and self.status_timer:
            self.status_timer.cancel()
            self.status_timer = None
        
        if hasattr(self, 'message_container'):
            self.message_container.visible = False
            self.page.update()



    def update_search_setting(self, setting_name: str, value):
        """עדכון הגדרת חיפוש"""
        self.app_settings.settings[setting_name] = value
        self.app_settings.save_settings()
        
        # עדכון אפשרויות החיפוש
        if setting_name == 'search_filenames_only':
            self.search_options.search_in_path = value
        elif setting_name == 'exact_match':
            self.search_options.exact_match = value
        elif setting_name == 'min_word_count':
            self.search_options.min_word_count = value
        
        # ביצוע חיפוש מחדש אם יש מילות חיפוש
        if hasattr(self, 'search_term') and self.search_term.value:
            self.search_documents(None)    

    def build_advanced_settings_panel(self):
        """בניית פאנל ההגדרות המתקדמות"""
        import flet as ft
        self.filter_row = self.create_file_type_buttons_row() 
        # בניית הפאנל המלא
        return ft.Column([
            self.filter_row, 
            ft.Switch(
                label="חיפוש בשמות קבצים בלבד",
                value=self.app_settings.get_setting('search_filenames_only', False),
                on_change=lambda e: self.update_search_setting('search_filenames_only', e.control.value)
            ),
            ft.Switch(
                label="התאמה מדויקת",
                value=self.app_settings.get_setting('exact_match', False),
                on_change=lambda e: self.update_search_setting('exact_match', e.control.value)
            ),
        ], spacing=10)
        
    def change_window_maximized(self, e):
        self.app_settings.settings['window_maximized'] = e.control.value
        self.app_settings.save_settings()
        self.show_status("ההגדרה תיכנס לתוקף בהרצה הבאה")


        
#-----------------
#  ספרים
#------------------

                
    def open_book_at_search_result(self, file_path: str, location: str = "", search_term: str = ""):
        self.force_book_path = file_path
        self.navigation_bar.selected_index = 1
        self.navigation_bar.update()

        class DummyEvent:
            def __init__(self, control):
                self.control = control
        self.navigation_change(DummyEvent(self.navigation_bar))

        # קפיצה לעמוד
        try:
            if location:
                location = location.replace("עמוד", "").strip()
                page_num = int(location) - 1
                if 0 <= page_num < len(self.current_book_pages):
                    self.current_page_index = page_num
                    self.update_book_page()
        except Exception as ex:
            print(f"Error in open_book_at_search_result: {ex}")

        # הדבקת החיפוש לדף הספרים והפעלת הדגשה
        if hasattr(self, "book_search_term"):
            self.book_search_term.value = search_term
            # אם יש פונקציה book_search_reset מנקה ומדגישה
            if hasattr(self, "book_search_reset"):
                self.book_search_reset()
            elif hasattr(self, "update_book_page"):
                self.update_book_page()

        self.page.update()                           

    def create_books_view(self):
        self.book_font_size = 16  # קודם קובע את הגודל
        self.book_page_text = ft.Text(
            '',
            selectable=True,
            size=self.book_font_size,  # משתמש בגודל כאן
            max_lines=None,
            overflow=ft.TextOverflow.CLIP,
            color=ft.Colors.BLACK,
            text_align=ft.TextAlign.RIGHT,
        )
        # המשך הקוד כרגיל...
        # ודא אתחול משתנים קריטיים
        if not hasattr(self, "current_book_path"):
            self.current_book_path = None
        if not hasattr(self, "current_book_pages"):
            self.current_book_pages = []
        if not hasattr(self, "current_page_index"):
            self.current_page_index = 0

        # --- איסוף כל הספרים מכל האינדקסים הנבחרים ---
        self.books = []
        selected_indexes = self.app_settings.get_selected_indexes()
        for idx_path in selected_indexes:
            try:
                file_index = FileIndex(idx_path)
                with sqlite3.connect(file_index._optimized_index.db_path) as conn:
                    cursor = conn.execute("""
                        SELECT DISTINCT f.path, f.filename
                        FROM files f
                        INNER JOIN content c ON f.path = c.file_path
                        WHERE f.path LIKE '%.pdf' OR f.path LIKE '%.docx' OR f.path LIKE '%.txt'
                        ORDER BY f.filename
                    """)
                    for row in cursor.fetchall():
                        file_path, filename = row
                        if os.path.exists(file_path):
                            self.books.append((file_path, {'filename': filename}))
            except Exception as e:
                print(f"Error loading index {idx_path}: {str(e)}")
                import traceback
                print(traceback.format_exc())

        self.books.sort(key=lambda x: x[1]['filename'].lower())

        self.book_title = ft.Text('', size=22, weight='bold', color=ft.Colors.PRIMARY)
        self.page_indicator = ft.Text(
            '',
            size=14,
            color=ft.Colors.BLUE_GREY_700,
            text_align=ft.TextAlign.CENTER,
            weight=ft.FontWeight.W_500
        )
        self.book_page_text = ft.Text(
            '',
            selectable=True,
            size=16,
            max_lines=None,
            overflow=ft.TextOverflow.CLIP,
            color=ft.Colors.BLACK,
            text_align=ft.TextAlign.RIGHT,
        )

        # ----------- חיפוש בתוך הספר -----------
        self.book_search_term = ft.TextField(
            hint_text="חפש בספר...",
            width=200,
            dense=True,
            border_radius=7,
            on_change=lambda e: self.book_search_reset(),
            on_submit=lambda e: self.next_book_search_result(),
        )
        self.book_search_matches = []
        self.book_search_current = 0

        # ---------- כפתורי ניווט ----------
        self.prev_page_btn = ft.IconButton(
            icon=ft.Icons.ARROW_BACK,
            tooltip="עמוד קודם",
            icon_size=22,
            bgcolor=ft.Colors.BLUE_50,
            on_click=lambda e: self.prev_page(e),
            disabled=True,
            style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=12))
        )
        self.next_page_btn = ft.IconButton(
            icon=ft.Icons.ARROW_FORWARD,
            tooltip="עמוד הבא",
            icon_size=22,
            bgcolor=ft.Colors.BLUE_50,
            on_click=lambda e: self.next_page(e),
            disabled=True,
            style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=12))
        )

        # בניית רשימת ספרים (כפי שיש אצלך)
        def build_books_buttons():
            controls = []
            if not self.books:
                controls.append(
                    ft.Container(
                        content=ft.Column([
                            ft.Icon(ft.Icons.LIBRARY_BOOKS, size=40, color=ft.Colors.GREY_400),
                            ft.Text(
                                "לא נמצאו ספרים",
                                size=16,
                                color=ft.Colors.GREY_400,
                                text_align=ft.TextAlign.CENTER
                            ),
                        ], alignment=ft.MainAxisAlignment.CENTER),
                        padding=20
                    )
                )
            else:
                for file_path, file_data in self.books:
                    selected = file_path == self.current_book_path
                    controls.append(
                        ft.Container(
                            content=ft.Row([
                                ft.Icon(self.get_icon_for_file(file_path), color=ft.Colors.BLUE_400, size=18),
                                ft.Text(
                                    file_data['filename'],
                                    max_lines=1,
                                    overflow=ft.TextOverflow.ELLIPSIS,
                                    size=15,
                                    expand=True,
                                ),
                            ], vertical_alignment=ft.CrossAxisAlignment.CENTER),
                            height=38,
                            bgcolor=ft.Colors.BLUE_50 if selected else ft.Colors.SURFACE,
                            border_radius=7,
                            padding=ft.padding.symmetric(horizontal=10, vertical=0),
                            ink=True,
                            on_click=lambda e, path=file_path: self.select_book(path),
                            alignment=ft.alignment.center_left,
                            border=ft.border.all(1, ft.Colors.with_opacity(0.025, ft.Colors.BLUE)) if selected else None,
                        )
                    )
            return controls

        self.build_books_buttons = build_books_buttons

        self.books_column = ft.Column(
            controls=build_books_buttons(),
            scroll=ft.ScrollMode.AUTO,
            spacing=2,
            horizontal_alignment=ft.CrossAxisAlignment.STRETCH,
            expand=True,
        )

        books_list_container = ft.Container(
            content=self.books_column,
            bgcolor=ft.Colors.SURFACE,
            border_radius=10,
            padding=ft.padding.all(10),
            width=230,
            expand=False,
            alignment=ft.alignment.top_center,
            border=ft.border.all(1, ft.Colors.OUTLINE),
            shadow=ft.BoxShadow(
                spread_radius=0.5,
                blur_radius=6,
                color=ft.Colors.with_opacity(0.04, ft.Colors.BLACK)
            ),
            margin=ft.margin.only(top=8, left=8, bottom=8, right=4)
        )

        # -------------------- פאנל תצוגת הספר ---------------------
        left_panel = ft.Container(
            content=ft.Column([
                # שורה אחת: תיבת החיפוש, שם הספר, מונה עמודים
                ft.Row([
                    # קצה ימין: כפתורי נקה וחץ + תיבת חיפוש
                    ft.Row([
                        self.book_search_term,
                        ft.IconButton(icon=ft.Icons.ARROW_DOWNWARD, tooltip="מעבר לתוצאה הבאה", on_click=lambda e: self.next_book_search_result()),
                        ft.IconButton(icon=ft.Icons.CLEAR, tooltip="נקה חיפוש", on_click=lambda e: self.clear_book_search()),
                    ], spacing=6),

                    # רווח גמיש
                    ft.Container(expand=True),

                    # מונה עמוד במרכז (או איפה שתרצה)
                    self.page_indicator,

                    # רווח גמיש
                    ft.Container(expand=True),

                    # שם הספר בצד שמאל
                    self.book_title,
                ], 
                    alignment=ft.MainAxisAlignment.CENTER, 
                    vertical_alignment=ft.CrossAxisAlignment.CENTER, 
                    spacing=12
                ),

                # כפתורי ניווט עמודים (למטה או היכן שרצית)
                ft.Row([
                    self.prev_page_btn,
                    self.next_page_btn,
                    ft.Container(expand=True),  # רווח גמיש
                    ft.IconButton(
                        icon=ft.Icons.ADD, 
                        tooltip="הגדל טקסט", 
                        on_click=lambda e: self.increase_book_font_size()
                    ),
                    ft.IconButton(
                        icon=ft.Icons.REMOVE, 
                        tooltip="הקטן טקסט", 
                        on_click=lambda e: self.decrease_book_font_size()
                    ),
                ], alignment=ft.MainAxisAlignment.START, vertical_alignment=ft.CrossAxisAlignment.CENTER),

                ft.Divider(height=1),

                ft.ListView(
                    controls=[
                        ft.Container(
                            content=self.book_page_text,
                            padding=20,
                            bgcolor=ft.Colors.WHITE,
                            border_radius=7,
                            border=ft.border.all(1, ft.Colors.with_opacity(0.08, ft.Colors.BLUE)),
                            shadow=ft.BoxShadow(
                                spread_radius=0.5,
                                blur_radius=6,
                                color=ft.Colors.with_opacity(0.04, ft.Colors.BLACK)
                            ),
                        )
                    ],
                    expand=True,
                    spacing=10
                ),
            ],
            expand=True,
            alignment=ft.MainAxisAlignment.START,
            spacing=11),
            expand=True,
            padding=ft.padding.all(10),
            bgcolor=ft.Colors.SURFACE,
            border_radius=10,
            border=ft.border.all(1, ft.Colors.OUTLINE),
            shadow=ft.BoxShadow(
                spread_radius=0.5,
                blur_radius=8,
                color=ft.Colors.with_opacity(0.07, ft.Colors.BLACK)
            ),
            margin=ft.margin.only(top=8, right=8, bottom=8, left=4)
        )


        vertical_divider = ft.Container(
            content=ft.VerticalDivider(
                width=1,
                color=ft.Colors.OUTLINE,
                thickness=1,
            ),
            margin=ft.margin.symmetric(vertical=12)
        )

        main_view = ft.Container(
            content=ft.Column([
                ft.Text("חיפוש בספרים", size=30, weight="bold"),
                ft.Divider(height=3),
                ft.Row([
                    books_list_container,
                    vertical_divider,  # כאן הוא בשימוש
                    left_panel
                ], expand=True, spacing=0, alignment=ft.MainAxisAlignment.START)
            ], expand=True, spacing=5),
            padding=ft.padding.all(6),
            bgcolor=ft.Colors.SURFACE,
            expand=True
        )

        # --------------- פונקציות עזר ---------------

        def book_search_reset():
            term = self.book_search_term.value.strip()
            self.book_search_matches = []
            self.book_search_current = 0
            if not term or not self.current_book_pages:
                self.update_book_page()
                return
            # מציאת כל המופעים בכל הדפים
            matches = []
            term_lc = term.lower()
            for page_idx, page_text in enumerate(self.current_book_pages):
                for m in re.finditer(re.escape(term_lc), page_text.lower()):
                    matches.append((page_idx, m.start(), m.end()))
            self.book_search_matches = matches
            self.book_search_current = 0
            self.update_book_page()

        self.book_search_reset = book_search_reset

        def next_book_search_result():
            if not self.book_search_matches:
                return
            self.book_search_current = (self.book_search_current + 1) % len(self.book_search_matches)
            # עבור למופע הבא
            page_idx, _, _ = self.book_search_matches[self.book_search_current]
            self.current_page_index = page_idx
            self.update_book_page()

        self.next_book_search_result = next_book_search_result

        def clear_book_search():
            self.book_search_term.value = ""
            self.book_search_matches = []
            self.book_search_current = 0
            self.update_book_page()

        self.clear_book_search = clear_book_search

        def update_book_page():
            if not self.current_book_pages:
                self.book_page_text.value = ""
                self.book_page_text.spans = None
                self.page_indicator.value = ""
            else:
                page_text = self.current_book_pages[self.current_page_index]
                term = self.book_search_term.value.strip()
                if term:
                    # הדגשת כל המופעים של החיפוש
                    spans = []
                    text_lower = page_text.lower()
                    term_lower = term.lower()
                    last = 0
                    for m in re.finditer(re.escape(term_lower), text_lower):
                        start, end = m.start(), m.end()
                        if start > last:
                            spans.append(ft.TextSpan(page_text[last:start]))
                        # קבע צבע: מופע נוכחי (אדום כהה), אחרים (אדום בהיר)
                        is_current = False
                        count = 0
                        for idx, s, e in self.book_search_matches:
                            if idx == self.current_page_index and s == start and e == end:
                                if count == self.book_search_current:
                                    is_current = True
                                count += 1
                        color = ft.Colors.RED if is_current else "#d32f2f"
                        spans.append(ft.TextSpan(page_text[start:end], style=ft.TextStyle(bgcolor="#ffcccc", color=color, weight=ft.FontWeight.BOLD)))
                        last = end
                    if last < len(page_text):
                        spans.append(ft.TextSpan(page_text[last:]))
                    self.book_page_text.value = None
                    self.book_page_text.spans = spans
                else:
                    self.book_page_text.value = page_text
                    self.book_page_text.spans = None
                self.page_indicator.value = f"עמוד {self.current_page_index + 1} מתוך {len(self.current_book_pages)}"
            self.book_page_text.update()
            self.page_indicator.update()
            self.update_nav_buttons()

        self.update_book_page = update_book_page

        return main_view

    def next_page(self, e=None):
        if self.current_book_pages and self.current_page_index < len(self.current_book_pages) - 1:
            self.current_page_index += 1
            self.update_book_page()

    def prev_page(self, e=None):
        if self.current_book_pages and self.current_page_index > 0:
            self.current_page_index -= 1
            self.update_book_page()    

    def update_nav_buttons(self):
        self.prev_page_btn.disabled = (self.current_page_index == 0)
        self.next_page_btn.disabled = (
            not self.current_book_pages or self.current_page_index >= len(self.current_book_pages) - 1
        )
        self.prev_page_btn.update()
        self.next_page_btn.update()

    def get_icon_for_file(self, file_path):
        import flet as ft
        Icons_MAP = {
            ".pdf": ft.Icons.PICTURE_AS_PDF,
            ".txt": ft.Icons.DESCRIPTION,
            ".docx": ft.Icons.ARTICLE,
            ".doc": ft.Icons.ARTICLE
        }
        ext = os.path.splitext(file_path.lower())[1]
        return Icons_MAP.get(ext, ft.Icons.INSERT_DRIVE_FILE)

    def select_book(self, file_path):
        file_data = None
        try:
            for idx in self.app_settings.get_selected_indexes():
                file_index = FileIndex(idx)
                files = file_index.get_files()
                if file_path in files:
                    with sqlite3.connect(file_index._optimized_index.db_path) as conn:
                        cursor = conn.execute("""
                            SELECT c.content
                            FROM content c
                            WHERE c.file_path = ?
                            ORDER BY c.id
                        """, (file_path,))
                        contents = [{'content': row[0]} for row in cursor.fetchall()]
                        
                        file_data = {
                            'filename': os.path.basename(file_path),
                            'contents': contents
                        }
                    break
                    
            if not file_data:
                self.book_title.value = "לא נמצא ספר"
                self.book_page_text.value = ""
                self.page_indicator.value = ""
                self.current_book_path = None
                self.current_book_pages = []
            else:
                self.current_book_path = file_path
                self.current_book_pages = [page['content'] for page in file_data['contents']]
                self.current_page_index = 0
                self.book_title.value = file_data['filename']
                self.update_book_page()
            
            self.books_column.controls = self.build_books_buttons()
            self.books_column.update()
            self.update_nav_buttons()
            self.page.update()
            
        except Exception as e:
            print(f"Error selecting book: {str(e)}")
            import traceback
            print(traceback.format_exc())



    def increase_book_font_size(self):
        if not hasattr(self, "book_font_size"):
            self.book_font_size = 16
        self.book_font_size = min(self.book_font_size + 2, 48)
        self.book_page_text.size = self.book_font_size
        self.book_page_text.update()

    def decrease_book_font_size(self):
        if not hasattr(self, "book_font_size"):
            self.book_font_size = 16
        self.book_font_size = max(self.book_font_size - 2, 8)
        self.book_page_text.size = self.book_font_size
        self.book_page_text.update()            

            
#-----פונקצייה ראשית------        
def main(page: ft.Page):
    app_settings = AppSettings()
    if app_settings.get_setting('window_maximized', True):
        page.window.maximized = True
    app = DocumentSearchApp(page)
    if app_settings.get_setting('window_maximized', True):
        page.update()

if __name__ == "__main__":
    ft.app(target=main)
