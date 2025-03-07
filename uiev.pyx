cimport cython
cimport numpy as np
from ast import literal_eval
from collections import defaultdict
from collections.abc import Iterable
from contextlib import suppress as contextlib_suppress
from functools import lru_cache
from functools import reduce
from io import StringIO,BytesIO
from itertools import takewhile
from libc.stdint cimport int64_t,uint8_t
from libc.stdio cimport fputc,fclose,fprintf,fopen,FILE
from libcpp.string cimport string,npos
from libcpp.unordered_map cimport unordered_map
from libcpp.utility cimport pair
from libcpp.vector cimport vector
from operator import getitem as operator_getitem
from operator import itemgetter as operator_itemgetter
from os import environ as os_environ
from pandas import isna as pdisna
from pandas import read_csv
from pandas.core.base import PandasObject
from pandas.core.frame import DataFrame, Series, Index
from platform import platform
from random import randint as random_randint
from string import printable as string_printable
from struct import Struct
from struct import pack as structpack
from subprocess import PIPE, DEVNULL
from subprocess import Popen as subprocess_Popen
from subprocess import run as subprocess_run
from tempfile import NamedTemporaryFile
from time import sleep as timesleep
from types import GeneratorType
from unicodedata import name as unicodedata_name
from zlib import compress as zlib_compress
from zlib import crc32 as zlib_crc32
from random import uniform
from base64 import b64encode
import collections
import ctypes
import cython
import numpy as np
import os
import pandas as pd
import re as repy
import regex as re
import requests
import shutil
import subprocess
import sys, subprocess
import typing
import warnings
import zipfile
import traceback
from pandas import DataFrame as pd_DataFrame


re.cache_all(True)
warnings.simplefilter(action='ignore', category=pd.errors.PerformanceWarning)


ctypedef struct color_rgb_with_coords_and_count:
    Py_ssize_t x
    Py_ssize_t y
    Py_ssize_t count
    uint8_t r
    uint8_t g
    uint8_t b

ctypedef vector[color_rgb_with_coords_and_count] vec_rgbxycount

cdef:
    dict[str,bytes] latin_keycombination = {

        # ascii

        "!":b"input text '!'",
        '"':b"""input text '"'""",
        "#":b"input text '#'",
        "$":b"input text '$'",
        "%":b"input text '%'",
        "&":b"input text '&'",
        "'":b'''input text "'"''',
        "(":b"input text '('",
        ")":b"input text ')'",
        "*":b"input text '*'",
        "+":b"input text '+'",
        ",":b"input text ','",
        "-":b"input text '-'",
        ".":b"input text '.'",
        "/":b"input text '/'",
        "0":b"input text '0'",
        "1":b"input text '1'",
        "2":b"input text '2'",
        "3":b"input text '3'",
        "4":b"input text '4'",
        "5":b"input text '5'",
        "6":b"input text '6'",
        "7":b"input text '7'",
        "8":b"input text '8'",
        "9":b"input text '9'",
        ":":b"input text ':'",
        ";":b"input text ';'",
        "<":b"input text '<'",
        "=":b"input text '='",
        ">":b"input text '>'",
        "?":b"input text '?'",
        "@":b"input text '@'",
        "A":b"input text 'A'",
        "B":b"input text 'B'",
        "C":b"input text 'C'",
        "D":b"input text 'D'",
        "E":b"input text 'E'",
        "F":b"input text 'F'",
        "G":b"input text 'G'",
        "H":b"input text 'H'",
        "I":b"input text 'I'",
        "J":b"input text 'J'",
        "K":b"input text 'K'",
        "L":b"input text 'L'",
        "M":b"input text 'M'",
        "N":b"input text 'N'",
        "O":b"input text 'O'",
        "P":b"input text 'P'",
        "Q":b"input text 'Q'",
        "R":b"input text 'R'",
        "S":b"input text 'S'",
        "T":b"input text 'T'",
        "U":b"input text 'U'",
        "V":b"input text 'V'",
        "W":b"input text 'W'",
        "X":b"input text 'X'",
        "Y":b"input text 'Y'",
        "Z":b"input text 'Z'",
        "[":b"input text '['",
        "\\":b"input text '\\'",
        "]":b"input text ']'",
        "^":b"input text '^'",
        "_":b"input text '_'",
        "`":b"input text '`'",
        "a":b"input text 'a'",
        "b":b"input text 'b'",
        "c":b"input text 'c'",
        "d":b"input text 'd'",
        "e":b"input text 'e'",
        "f":b"input text 'f'",
        "g":b"input text 'g'",
        "h":b"input text 'h'",
        "i":b"input text 'i'",
        "j":b"input text 'j'",
        "k":b"input text 'k'",
        "l":b"input text 'l'",
        "m":b"input text 'm'",
        "n":b"input text 'n'",
        "o":b"input text 'o'",
        "p":b"input text 'p'",
        "q":b"input text 'q'",
        "r":b"input text 'r'",
        "s":b"input text 's'",
        "t":b"input text 't'",
        "u":b"input text 'u'",
        "v":b"input text 'v'",
        "w":b"input text 'w'",
        "x":b"input text 'x'",
        "y":b"input text 'y'",
        "z":b"input text 'z'",
        "{":b"input text '{'",
        "|":b"input text '|'",
        "}":b"input text '}'",
        "~":b"input text '~'",

        # https://www.ut.edu/academics/college-of-arts-and-letters/department-of-languages-and-linguistics/typing-accented-characters
        # á, é, í, ó, ú, ý, Á, É, Í, Ó, Ú, Ý
        "á":b"input keycombination 58 33;input text 'a'",
        "é":b"input keycombination 58 33;input text 'e'",
        "í":b"input keycombination 58 33;input text 'i'",
        "ó":b"input keycombination 58 33;input text 'o'",
        "ú":b"input keycombination 58 33;input text 'u'",
        "ý":b"input keycombination 58 33;input text 'y'",
        "Á":b"input keycombination 58 33;input text 'A'",
        "É":b"input keycombination 58 33;input text 'E'",
        "Í":b"input keycombination 58 33;input text 'I'",
        "Ó":b"input keycombination 58 33;input text 'O'",
        "Ú":b"input keycombination 58 33;input text 'U'",
        "Ý":b"input keycombination 58 33;input text 'Y'",

        # ç, Ç
        "Ç" :b"input keycombination 59 57 31",
        "ç" :b"input keycombination 57 31",

        # â, ê, î, ô, û, Â, Ê, Î, Ô, Û
        "â":b"input keycombination 57 37;input text 'a'",
        "ê":b"input keycombination 57 37;input text 'e'",
        "î":b"input keycombination 57 37;input text 'i'",
        "ô":b"input keycombination 57 37;input text 'o'",
        "û":b"input keycombination 57 37;input text 'u'",
        "Â":b"input keycombination 57 37;input text 'A'",
        "Ê":b"input keycombination 57 37;input text 'E'",
        "Î":b"input keycombination 57 37;input text 'I'",
        "Ô":b"input keycombination 57 37;input text 'O'",
        "Û":b"input keycombination 57 37;input text 'U'",

        # ã, ñ, õ, Ã, Ñ, Õ
        "ã":b"input keycombination 57 42;input text 'a'",
        "ñ":b"input keycombination 57 42;input text 'n'",
        "õ":b"input keycombination 57 42;input text 'o'",
        "Ã":b"input keycombination 57 42;input text 'A'",
        "Ñ":b"input keycombination 57 42;input text 'N'",
        "Õ":b"input keycombination 57 42;input text 'O'",

        # ß, ẞ
        "ß": b"input keycombination 57 47",
        "ẞ": b"input keycombination 59 57 47",

        # ä, ë, ï, ö, ü, ÿ, Ä, Ë, Ï, Ö, Ü, Ÿ
        "ä":b"input keycombination 57 49;input text 'a'",
        "ë":b"input keycombination 57 49;input text 'e'",
        "ï":b"input keycombination 57 49;input text 'i'",
        "ö":b"input keycombination 57 49;input text 'o'",
        "ü":b"input keycombination 57 49;input text 'u'",
        "ÿ":b"input keycombination 57 49;input text 'y'",
        "Ä":b"input keycombination 57 49;input text 'A'",
        "Ë":b"input keycombination 57 49;input text 'E'",
        "Ï":b"input keycombination 57 49;input text 'I'",
        "Ö":b"input keycombination 57 49;input text 'O'",
        "Ü":b"input keycombination 57 49;input text 'U'",
        "Ÿ":b"input keycombination 57 49;input text 'Y'",

        # à, è, ì, ò, ù, À, È, Ì, Ò, Ù
        "à":b"input keycombination 57 68;input text 'a'",
        "è":b"input keycombination 57 68;input text 'e'",
        "ì":b"input keycombination 57 68;input text 'i'",
        "ò":b"input keycombination 57 68;input text 'o'",
        "ù":b"input keycombination 57 68;input text 'u'",
        "À":b"input keycombination 57 68;input text 'A'",
        "È":b"input keycombination 57 68;input text 'E'",
        "Ì":b"input keycombination 57 68;input text 'I'",
        "Ò":b"input keycombination 57 68;input text 'O'",
        "Ù":b"input keycombination 57 68;input text 'U'",

        #todo
        "å":b"input text 'a'",
        "Å":b"input text 'a'",
        "æ":b"input text 'ae'",
        "Æ":b"input text 'Ae'",
        "œ":b"input text 'oe'",
        "Œ":b"input text 'Oe'",
        "ð":b"input text 'd'",
        "Ð":b"input text 'D'",
        "ø":b"input text 'o'",
        "Ø":b"input text 'O'",
        "¿":b"input text '?'",
        "¡":b"input text '!'",

    }
    string cpp_distance_metric=<string>b"Euclidean"
    dict letter_lookup_dict = {}
    string emptystring = <string>b""
    vector[string] emptystringvec = [b""]
    string ppm_header=<string>b"P6\n%d %d\n%d\n"
    string write_binary=<string>b"wb"
    int SIG_BOOLEAN = ord("Z")
    int SIG_BYTE = ord("B")
    int SIG_SHORT = ord("S")
    int SIG_INT = ord("I")
    int SIG_LONG = ord("J")
    int SIG_FLOAT = ord("F")
    int SIG_DOUBLE = ord("D")
    int SIG_STRING = ord("R")
    int SIG_MAP = ord("M")
    int SIG_END_MAP = 0
    str PYTHON_STRUCT_UNPACK_SIG_BOOLEAN = "?"
    str PYTHON_STRUCT_UNPACK_SIG_BYTE = "b"
    str PYTHON_STRUCT_UNPACK_SIG_SHORT = "h"
    str PYTHON_STRUCT_UNPACK_SIG_INT = "i"
    str PYTHON_STRUCT_UNPACK_SIG_LONG = "q"
    str PYTHON_STRUCT_UNPACK_SIG_FLOAT = "f"
    str PYTHON_STRUCT_UNPACK_SIG_DOUBLE = "d"
    str PYTHON_STRUCT_UNPACK_SIG_STRING = "s"
    str LITTLE_OR_BIG = ">"
    object STRUCT_UNPACK_SIG_BOOLEAN = Struct(
        f"{LITTLE_OR_BIG}{PYTHON_STRUCT_UNPACK_SIG_BOOLEAN}"
    ).unpack
    object STRUCT_UNPACK_SIG_BYTE = Struct(
        f"{LITTLE_OR_BIG}{PYTHON_STRUCT_UNPACK_SIG_BYTE}"
    ).unpack
    object STRUCT_UNPACK_SIG_SHORT = Struct(
        f"{LITTLE_OR_BIG}{PYTHON_STRUCT_UNPACK_SIG_SHORT}"
    ).unpack
    object STRUCT_UNPACK_SIG_INT = Struct(
        f"{LITTLE_OR_BIG}{PYTHON_STRUCT_UNPACK_SIG_INT}"
    ).unpack
    object STRUCT_UNPACK_SIG_LONG = Struct(
        f"{LITTLE_OR_BIG}{PYTHON_STRUCT_UNPACK_SIG_LONG}"
    ).unpack
    object STRUCT_UNPACK_SIG_FLOAT = Struct(
        f"{LITTLE_OR_BIG}{PYTHON_STRUCT_UNPACK_SIG_FLOAT}"
    ).unpack
    object STRUCT_UNPACK_SIG_DOUBLE = Struct(
        f"{LITTLE_OR_BIG}{PYTHON_STRUCT_UNPACK_SIG_DOUBLE}"
    ).unpack

    object asciifunc = np.frompyfunc(ascii, 1, 1)
    object reprfunc = np.frompyfunc(repr, 1, 1)
    str ResetAll = "\033[0m"
    str LightRed = "\033[91m"
    str LightGreen = "\033[92m"
    str LightYellow = "\033[93m"
    str LightBlue = "\033[94m"
    str LightMagenta = "\033[95m"
    str LightCyan = "\033[96m"
    str White = "\033[97m"
    str this_folder = os.path.dirname(__file__)
    bint iswindows = "win" in platform().lower()

    str url_fragment_parser = "https://github.com/hansalemaos/android_fragment_parser/raw/refs/heads/main/fragmentdumper.cpp"
    str cpp_file_pure_fragment = "fragmentdumper.cpp"
    str cpp_file_fragment = os.path.join(this_folder, cpp_file_pure_fragment)
    str exe_file_pure_fragment = "fragmentdumper.exe" if iswindows else "fragmentdumper_exe"
    str exe_file_fragment = os.path.join(this_folder, exe_file_pure_fragment)

    str url_ui2_parser = "https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/uiautomator2parser.cpp"
    str cpp_file_pure_ui2 = "uiautomator2parser.cpp"
    str cpp_file_ui2 = os.path.join(this_folder, cpp_file_pure_ui2)
    str exe_file_pure_ui2 = "uiautomator2parser.exe" if iswindows else "uiautomator2parser_exe"
    str exe_file_ui2 = os.path.join(this_folder, exe_file_pure_ui2)

    str url_ui1_parser = "https://raw.githubusercontent.com/hansalemaos/uiautomator_dump_to_csv/refs/heads/main/uiautomatornolimit.cpp"
    str cpp_file_pure_ui1 = "uiautomatornolimit.cpp"
    str cpp_file_ui1 = os.path.join(this_folder, cpp_file_pure_ui1)
    str exe_file_pure_ui1 = "uiautomatornolimit.exe" if iswindows else "uiautomatornolimit_exe"
    str exe_file_ui1 = os.path.join(this_folder, exe_file_pure_ui1)

    str url_tesser_parser = "https://github.com/hansalemaos/tesseract_hocr_to_csv/raw/refs/heads/main/hocr2csv.cpp"
    str cpp_file_pure_tesser = "hocr2csv.cpp"
    str cpp_file_tesser = os.path.join(this_folder, cpp_file_pure_tesser)
    str exe_file_pure_tesser = "hocr2csv.exe"  if iswindows else "hocr2csv_exe"
    str exe_file_tesser = os.path.join(this_folder, exe_file_pure_tesser)


    dict[str,object] invisibledict = {"shell":False, "env":os_environ}
    dict cache_apply_literal_eval_to_tuple = {}
    list[str] columns_ui2 = [
        "aa_index",
        "aa_indent",
        "aa_text",
        "aa_resource_id",
        "aa_clazz",
        "aa_package",
        "aa_content_desc",
        "aa_checkable",
        "aa_checked",
        "aa_clickable",
        "aa_enabled",
        "aa_focusable",
        "aa_focused",
        "aa_scrollable",
        "aa_long_clickable",
        "aa_password",
        "aa_selected",
        "aa_visible_to_user",
        "aa_bounds",
        "aa_drawing_order",
        "aa_hint",
        "aa_display_id",
        "aa_line_index",
        "aa_children",
        "aa_parents",
        "aa_start_x",
        "aa_start_y",
        "aa_end_x",
        "aa_end_y",
        "aa_center_x",
        "aa_center_y",
        "aa_width",
        "aa_height",
        "aa_area",
        "aa_w_h_relation",
    ]
    list[str] columns_fragments = [
    "aa_my_id",
    "aa_my_group_id",
    "aa_my_element_id",
    "aa_my_direct_parent_id",
    "aa_my_parent_ids",
    "aa_original_string",
    "aa_center_x",
    "aa_center_y",
    "aa_area",
    "aa_start_x",
    "aa_start_y",
    "aa_end_x",
    "aa_end_y",
    "aa_height",
    "aa_width",
    "aa_is_sqare",
    "aa_rel_width_height",
    "aa_hashcode_int",
    "aa_mid_int",
    "aa_spaces",
    "aa_classname",
    "aa_element_id",
    "aa_hashcode",
    "aa_mid",
    "aa_start_x_relative",
    "aa_end_x_relative",
    "aa_start_y_relative",
    "aa_end_y_relative",
    "aa_clickable",
    "aa_context_clickable",
    "aa_drawn",
    "aa_enabled",
    "aa_focusable",
    "aa_long_clickable",
    "aa_pflag_activated",
    "aa_pflag_dirty_mask",
    "aa_pflag_focused",
    "aa_pflag_hovered",
    "aa_pflag_invalidated",
    "aa_pflag_is_root_namespace",
    "aa_pflag_prepressed",
    "aa_pflag_selected",
    "aa_scrollbars_horizontal",
    "aa_scrollbars_vertical",
    "aa_visibility",
    ]
    object windll=None
    object ntdll=None
    object kernel32=None
    object _GetShortPathNameW=None

if iswindows:
    from ctypes import wintypes
    startupinfo = subprocess.STARTUPINFO()
    startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
    startupinfo.wShowWindow = subprocess.SW_HIDE
    creationflags = subprocess.CREATE_NO_WINDOW
    invisibledict = {
        "startupinfo": startupinfo,
        "creationflags": creationflags,
        "start_new_session": True,
    }
    windll = ctypes.LibraryLoader(ctypes.WinDLL)
    ntdll = windll.ntdll
    kernel32 = windll.kernel32
    _GetShortPathNameW = kernel32.GetShortPathNameW
    _GetShortPathNameW.argtypes = [wintypes.LPCWSTR, wintypes.LPWSTR, wintypes.DWORD]
    _GetShortPathNameW.restype = wintypes.DWORD


class JustColors:
    def __init__(self):
        self.BOLD = "\033[1m"
        self.ITALIC = "\033[3m"
        self.UNDERLINE = "\033[4m"
        self.UNDERLINE_THICK = "\033[21m"
        self.HIGHLIGHTED = "\033[7m"
        self.HIGHLIGHTED_BLACK = "\033[40m"
        self.HIGHLIGHTED_RED = "\033[41m"
        self.HIGHLIGHTED_GREEN = "\033[42m"
        self.HIGHLIGHTED_YELLOW = "\033[43m"
        self.HIGHLIGHTED_BLUE = "\033[44m"
        self.HIGHLIGHTED_PURPLE = "\033[45m"
        self.HIGHLIGHTED_CYAN = "\033[46m"
        self.HIGHLIGHTED_GREY = "\033[47m"
        self.HIGHLIGHTED_GREY_LIGHT = "\033[100m"
        self.HIGHLIGHTED_RED_LIGHT = "\033[101m"
        self.HIGHLIGHTED_GREEN_LIGHT = "\033[102m"
        self.HIGHLIGHTED_YELLOW_LIGHT = "\033[103m"
        self.HIGHLIGHTED_BLUE_LIGHT = "\033[104m"
        self.HIGHLIGHTED_PURPLE_LIGHT = "\033[105m"
        self.HIGHLIGHTED_CYAN_LIGHT = "\033[106m"
        self.HIGHLIGHTED_WHITE_LIGHT = "\033[107m"
        self.STRIKE_THROUGH = "\033[9m"
        self.MARGIN_1 = "\033[51m"
        self.MARGIN_2 = "\033[52m"
        self.BLACK = "\033[30m"
        self.RED_DARK = "\033[31m"
        self.GREEN_DARK = "\033[32m"
        self.YELLOW_DARK = "\033[33m"
        self.BLUE_DARK = "\033[34m"
        self.PURPLE_DARK = "\033[35m"
        self.CYAN_DARK = "\033[36m"
        self.GREY_DARK = "\033[37m"
        self.BLACK_LIGHT = "\033[90m"
        self.RED = "\033[91m"
        self.GREEN = "\033[92m"
        self.YELLOW = "\033[93m"
        self.BLUE = "\033[94m"
        self.PURPLE = "\033[95m"
        self.CYAN = "\033[96m"
        self.WHITE = "\033[97m"
        self.DEFAULT = "\033[0m"


mycolors = JustColors()

cpdef printincolor(values, color=None, print_to_stderr=False):
    s1 = "GOT AN ERROR DURING PRINTING"
    if color:
        try:
            s1 = "%s%s%s" % (color, values, mycolors.DEFAULT)
        except Exception:
            if isinstance(values, bytes):
                s1 = "%s%s%s" % (
                    color,
                    values.decode("utf-8", "backslashreplace"),
                    mycolors.DEFAULT,
                )
            else:
                s1 = "%s%s%s" % (color, repr(values), mycolors.DEFAULT)
        if print_to_stderr:
            sys.stderr.flush()
            sys.stderr.write(f"{s1}\n")
            sys.stderr.flush()
        else:
            print(s1)

    else:
        try:
            s1 = "%s%s" % (values, mycolors.DEFAULT)
        except Exception:
            if isinstance(values, bytes):
                s1 = "%s%s" % (
                    values.decode("utf-8", "backslashreplace"),
                    mycolors.DEFAULT,
                )
            else:
                s1 = "%s%s" % (repr(values), mycolors.DEFAULT)
        if print_to_stderr:
            sys.stderr.flush()
            sys.stderr.write(f"{s1}\n")
            sys.stderr.flush()
        else:
            print(s1)


def errwrite(*args, **kwargs):
    symbol_top = kwargs.pop("symbol_top", "╦")
    symbol_bottom = kwargs.pop("symbol_bottom", "╩")
    len_top = kwargs.pop("len_top", "60")
    len_bottom = kwargs.pop("len_bottom", "60")
    color_top = kwargs.pop("color_top", "YELLOW_DARK")
    color_bottom = kwargs.pop("color_bottom", "RED_DARK")
    print_to_stderr = kwargs.pop("print_to_stderr", False)
    color_exception = kwargs.pop("color_exception", "CYAN")
    color2print_top = None
    color2print_bottom = None
    color_exceptionmiddle = None
    try:
        color2print_top = mycolors.__dict__.get(
            color_top, mycolors.__dict__.get("YELLOW_DARK")
        )
        color2print_bottom = mycolors.__dict__.get(
            color_bottom, mycolors.__dict__.get("RED_DARK")
        )
        color_exceptionmiddle = mycolors.__dict__.get(
            color_exception, mycolors.__dict__.get("CYAN")
        )
    except Exception as e:
        print(e)

    printincolor(
        values="".join(symbol_top * int(len_top)),
        color=color2print_top,
        print_to_stderr=print_to_stderr,
    )
    etype, value, tb = sys.exc_info()
    lines = traceback.format_exception(etype, value, tb)
    try:
        if print_to_stderr:
            sys.stderr.flush()

            sys.stderr.write("".join(lines))
            sys.stderr.flush()
        else:
            printincolor(
                "".join(lines),
                color=color_exceptionmiddle,
                print_to_stderr=print_to_stderr,
            )
    except Exception:
        print("".join(lines))
    printincolor(
        "".join(symbol_bottom * int(len_bottom)),
        color=color2print_bottom,
        print_to_stderr=print_to_stderr,
    )


cdef extern from "fuzzmatcher.h" nogil :
    cdef cppclass StringMatcher:
        StringMatcher(vector[string]&, vector[string]&)
        void _load_vecs_for_cython(vector[string]*, vector[string]*)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_longest_common_substring_v1(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_longest_common_substring_v1(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_hemming_distance_1way(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_hemming_distance_1way(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_hemming_distance_2ways(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_hemming_distance_2ways(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_longest_common_substring_v0(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_longest_common_substring_v0(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_longest_common_subsequence_v0(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_longest_common_subsequence_v0(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_damerau_levenshtein_distance_2ways(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_damerau_levenshtein_distance_2ways(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_damerau_levenshtein_distance_1way(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_damerau_levenshtein_distance_1way(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_levenshtein_distance_1way(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_levenshtein_distance_1way(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_levenshtein_distance_2ways(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_levenshtein_distance_2ways(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_jaro_distance_1way(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_jaro_distance_1way(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_jaro_winkler_distance_1way(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_jaro_winkler_distance_1way(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_jaro_winkler_distance_2ways(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_jaro_winkler_distance_2ways(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_jaro_2ways(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_jaro_2ways(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_subsequence_v1(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_subsequence_v1(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ab_map_subsequence_v2(bint print_results, bint convert_to_csv, string file_path)
        unordered_map[int64_t, unordered_map[int64_t, pair[double, int64_t]]] ba_map_subsequence_v2(bint print_results, bint convert_to_csv, string file_path)
        StringMatcher& to_upper()
        StringMatcher& to_lower()
        StringMatcher& to_without_non_alphanumeric()
        StringMatcher& to_without_non_printable()
        StringMatcher& to_100_percent_copy()
        StringMatcher& to_without_whitespaces()
        StringMatcher& to_with_normalized_whitespaces()
        void _str__for_cython();


cdef extern from "fuzzmatcher.h" namespace "stringhelpers" nogil :
    vector[string] read_file_to_vector_lines(const string& filename)
    void _repr__for_cython(vector[string]*v);


cdef void convert_to_stdvec(object stri, vector[string]& outvector):
    cdef:
        Py_ssize_t i
        string converted_cpp
    if isinstance(stri, (str, bytes)):
        stri = [stri]
    outvector.resize(len(stri))
    outvector.clear()
    for i in range(len(stri)):
        converted_cpp=convert_python_object_to_cpp_string(stri[i])
        outvector.emplace_back(converted_cpp)


@cython.final
cdef class PyStringMatcher:
    cdef:
        StringMatcher*sm
        vector[string] stri1list
        vector[string] stri2list

    def __cinit__(self):
        self.sm = new StringMatcher(emptystringvec,emptystringvec)
        self.stri1list=[]
        self.stri2list=[]

    def __init__(self, object stri1, object stri2):
        convert_to_stdvec(stri1,self.stri1list)
        convert_to_stdvec(stri2,self.stri2list)
        self.sm._load_vecs_for_cython(<vector[string]*>(&self.stri1list),<vector[string]*>(&self.stri2list))

    def __dealloc__(self):
        del self.sm

    def _filter_results(self, dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r, bint ab = True, bint sort_reverse=False):
        cdef:
            dict[str,object] outdict={}
            list sorteddict
            Py_ssize_t index
            bytes pystri1, pystri2
        sorteddict=sorted([[tuple(x[1].values())[0][0],x] for x in r.items()], key=lambda y: y[0],reverse=sort_reverse)
        for index in range(len(sorteddict)):
            if ab:
                pystri1=(self.stri1list[0][sorteddict[index][1][0]])
                pystri2=(self.stri2list[0][tuple(sorteddict[index][1][1].keys())[0]])
                outdict[index]={
                    "aa_match":sorteddict[index][0],
                    "aa_1_is_sub":tuple(sorteddict[index][1][1].values())[0][1],
                    "aa_index_1":sorteddict[index][1][0],
                    "aa_index_2":tuple(sorteddict[index][1][1].keys())[0],
                    "aa_str_1":pystri1.decode('utf-8','backslashreplace'),
                    "aa_str_2":pystri2.decode('utf-8','backslashreplace'),
                }
            else:
                pystri1=(self.stri2list[0][sorteddict[index][1][0]])
                pystri2=(self.stri1list[0][tuple(sorteddict[index][1][1].keys())[0]])
                outdict[index]={
                    "aa_match":sorteddict[index][0],
                    "aa_2_is_sub":tuple(sorteddict[index][1][1].values())[0][1],
                    "aa_index_2":sorteddict[index][1][0],
                    "aa_index_1":tuple(sorteddict[index][1][1].keys())[0],
                    "aa_str_2":pystri1.decode('utf-8','backslashreplace'),
                    "aa_str_1":pystri2.decode('utf-8','backslashreplace'),
                }
        return outdict

    cpdef ab_map_damerau_levenshtein_distance_1way(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_damerau_levenshtein_distance_1way(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=False)

    cpdef ab_map_damerau_levenshtein_distance_2ways(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_damerau_levenshtein_distance_2ways(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=False)

    cpdef ab_map_hemming_distance_1way(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_hemming_distance_1way(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=False)

    cpdef ab_map_hemming_distance_2ways(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_hemming_distance_2ways(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=False)

    cpdef ab_map_jaro_2ways(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_jaro_2ways(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=True)

    cpdef ab_map_jaro_distance_1way(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_jaro_distance_1way(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=True)

    cpdef ab_map_jaro_winkler_distance_1way(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_jaro_winkler_distance_1way(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=True)

    cpdef ab_map_jaro_winkler_distance_2ways(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_jaro_winkler_distance_2ways(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=True)

    cpdef ab_map_levenshtein_distance_1way(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_levenshtein_distance_1way(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=False)

    cpdef ab_map_levenshtein_distance_2ways(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_levenshtein_distance_2ways(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=False)

    cpdef ab_map_longest_common_subsequence_v0(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_longest_common_subsequence_v0(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=True)

    cpdef ab_map_longest_common_substring_v0(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_longest_common_substring_v0(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=True)

    cpdef ab_map_longest_common_substring_v1(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_longest_common_substring_v1(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=True)

    cpdef ab_map_subsequence_v1(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_subsequence_v1(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=True)

    cpdef ab_map_subsequence_v2(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ab_map_subsequence_v2(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=True,sort_reverse=True)

    cpdef ba_map_damerau_levenshtein_distance_1way(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_damerau_levenshtein_distance_1way(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=False)

    cpdef ba_map_damerau_levenshtein_distance_2ways(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_damerau_levenshtein_distance_2ways(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=False)

    cpdef ba_map_hemming_distance_1way(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_hemming_distance_1way(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=False)

    cpdef ba_map_hemming_distance_2ways(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_hemming_distance_2ways(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=False)

    cpdef ba_map_jaro_2ways(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_jaro_2ways(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=True)

    cpdef ba_map_jaro_distance_1way(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_jaro_distance_1way(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=True)

    cpdef ba_map_jaro_winkler_distance_1way(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_jaro_winkler_distance_1way(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=True)

    cpdef ba_map_jaro_winkler_distance_2ways(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_jaro_winkler_distance_2ways(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=True)

    cpdef ba_map_levenshtein_distance_1way(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_levenshtein_distance_1way(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=False)

    cpdef ba_map_levenshtein_distance_2ways(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_levenshtein_distance_2ways(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=False)

    cpdef ba_map_longest_common_subsequence_v0(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_longest_common_subsequence_v0(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=True)

    cpdef ba_map_longest_common_substring_v0(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_longest_common_substring_v0(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=True)

    cpdef ba_map_longest_common_substring_v1(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_longest_common_substring_v1(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=True)

    cpdef ba_map_subsequence_v1(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_subsequence_v1(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=True)

    cpdef ba_map_subsequence_v2(self, bint print_cpp=False):
        cdef:
            dict[int64_t,dict[int64_t,tuple[double,int64_t]]] r
        r =self.sm.ba_map_subsequence_v2(print_cpp,False,emptystring)
        return self._filter_results(r=r,ab=False,sort_reverse=True)

    cpdef cpp_data_to_upper(self):
        self.sm.to_upper()
        return self

    cpdef cpp_data_to_lower(self):
        self.sm.to_lower()
        return self

    cpdef cpp_data_to_without_non_alphanumeric(self):
        self.sm.to_without_non_alphanumeric()
        return self

    cpdef cpp_data_to_without_non_printable(self):
        self.sm.to_without_non_printable()
        return self

    cpdef cpp_data_to_100_percent_copy(self):
        self.sm.to_100_percent_copy()
        return self

    cpdef cpp_data_to_without_whitespaces(self):
        self.sm.to_without_whitespaces()
        return self

    cpdef cpp_data_to_with_normalized_whitespaces(self):
        self.sm.to_with_normalized_whitespaces()
        return self



cdef str get_tmpfile(str suffix):
    cdef:
        object tfp
        str filename
    tfp = NamedTemporaryFile(delete=False, suffix=suffix)
    filename = tfp.name
    filename = os.path.normpath(filename)
    tfp.close()
    return filename

cdef string convert_python_object_to_cpp_string(object shell_command):
    cdef:
        string cpp_shell_command
        bytes tmp_bytes
    if isinstance(shell_command,bytes):
        cpp_shell_command=<string>shell_command
    elif isinstance(shell_command,str):
        tmp_bytes=shell_command.encode()
        cpp_shell_command=<string>(tmp_bytes)
    else:
        tmp_bytes=str(shell_command).encode()
        cpp_shell_command=<string>(tmp_bytes)
    return cpp_shell_command


cpdef take_screenshot(list[str] cmd, int width, int height, dict kwargs):
    try:
        if iswindows:
            return np.frombuffer(subprocess_run(cmd,**{**invisibledict,**kwargs, 'capture_output':True}).stdout.replace(b"\r\n",b"\n"), dtype=np.uint8,offset=16).reshape((height, width, 4))[...,[0,1,2]]
        else:
            return np.frombuffer(subprocess_run(cmd,**{**invisibledict,**kwargs, 'capture_output':True}).stdout, dtype=np.uint8,offset=16).reshape((height, width, 4))[...,[0,1,2]]
    except Exception:
        errwrite()
        return np.array([],dtype=np.uint8)
################################################# START Pandas Printer ####################################################################

@cython.nonecheck(True)
cpdef pdp(
    object df,
    Py_ssize_t column_rep=70,
    Py_ssize_t max_lines=0,
    Py_ssize_t max_colwidth=300,
    Py_ssize_t ljust_space=2,
    str sep=" | ",
    bint vtm_escape=True,
):
    cdef:
        dict[Py_ssize_t, np.ndarray] stringdict= {}
        dict[Py_ssize_t, Py_ssize_t] stringlendict= {}
        list[str] df_columns, allcolumns_as_string
        list[str] colors2rotate=[
        LightRed,
        LightGreen,
        LightYellow,
        LightBlue,
        LightMagenta,
        LightCyan,
        White,
        ]
        Py_ssize_t i, len_a, len_df_columns, lenstr, counter, j, len_stringdict0, k, len_stringdict
        str stringtoprint, dashes, dashesrep
        np.ndarray a
    if vtm_escape:
        print('\033[12:2p')
    if len(df) > max_lines and max_lines > 0:
        a = df.iloc[:max_lines].reset_index(drop=False).T.__array__()
    else:
        a = df.iloc[:len(df)].reset_index(drop=False).T.__array__()
    try:
        df_columns = ["iloc"] + [str(x) for x in df.columns]
    except Exception:
        try:
            df_columns = ["iloc",str(df.name)]
        except Exception:
            df_columns = ["iloc",str(0)]
    len_a=len(a)
    for i in range(len_a):
        try:
            stringdict[i] = reprfunc(a[i]).astype("U")
        except Exception:
            stringdict[i] = asciifunc(a[i]).astype("U")
        stringlendict[i] = (stringdict[i].dtype.itemsize // 4) + ljust_space
    for i in range(len_a):
        lenstr = len(df_columns[i])
        if lenstr > stringlendict[i]:
            stringlendict[i] = lenstr + ljust_space
        if max_colwidth > 0:
            if stringlendict[i] > max_colwidth:
                stringlendict[i] = max_colwidth

    allcolumns_as_string = []
    len_df_columns=len(df_columns)
    for i in range(len_df_columns):
        stringtoprint = str(df_columns[i])[: stringlendict[i]].ljust(stringlendict[i])
        allcolumns_as_string.append(stringtoprint)
    allcolumns_as_string_str = sep.join(allcolumns_as_string) + sep
    dashes = "-" * (len(allcolumns_as_string_str) + 2)
    dashesrep = dashes + "\n" + allcolumns_as_string_str + "\n" + dashes
    counter = 0
    len_stringdict0 = len(stringdict[0])
    len_stringdict=len(stringdict)
    for j in range(len_stringdict0):
        if column_rep > 0:
            if counter % column_rep == 0:
                print(dashesrep)
        counter += 1
        for k in range(len_stringdict):
            print((
                colors2rotate[k % len(colors2rotate)] + stringdict[k][j][: stringlendict[k]].replace("\n",
            "\\n").replace("\r", "\\r").ljust(stringlendict[k]) + ResetAll
            ), end=sep)
        print()
    return ""

cpdef print_col_width_len(object df):
    try:
        pdp(
            pd_DataFrame(
                [df.shape[0], df.shape[1]], index=["rows", "columns"]
            ).T.rename(
                {0: "DataFrame"},
            ),
        )
    except Exception:
        pdp(
            pd_DataFrame([df.shape[0]], index=["rows"]).T.rename({0: "Series"}),
        )


cpdef pandasprintcolor(self):
    pdp(pd_DataFrame(self.reset_index().__array__(), columns=['index']+[str(x) for x in self.columns],copy=False))
    print_col_width_len(self.__array__())

    return ""


def copy_func(f):
    cdef:
        object g
        list t
        Py_ssize_t i
    g = lambda *args: f(*args)
    t = list(filter(lambda prop: not ("__" in prop), dir(f)))
    i = 0
    while i < len(t):
        setattr(g, t[i], getattr(f, t[i]))
        i += 1
    return g


cpdef pandasprintcolor_s(self):
    return pandasprintcolor(self.to_frame())

cpdef pandasindexcolor(self):
    pdp(pd_DataFrame(self.__array__()[: self.print_stop].reshape((-1, 1))))
    return ""


cpdef reset_print_options():
    PandasObject.__str__ = copy_func(PandasObject.old__str__)
    PandasObject.__repr__ = copy_func(PandasObject.old__repr__)
    DataFrame.__repr__ = copy_func(DataFrame.old__repr__)
    DataFrame.__str__ = copy_func(DataFrame.old__str__)
    Series.__repr__ = copy_func(Series.old__repr__)
    Series.__str__ = copy_func(Series.old__str__)
    Index.__repr__ = copy_func(Index.old__repr__)
    Index.__str__ = copy_func(Index.old__str__)


def substitute_print_with_color_print(
    print_stop: int = 69, max_colwidth: int = 300, repeat_cols: int = 70
):
    if not hasattr(pd, "color_printer_active"):
        PandasObject.old__str__ = copy_func(PandasObject.__str__)
        PandasObject.old__repr__ = copy_func(PandasObject.__repr__)
        DataFrame.old__repr__ = copy_func(DataFrame.__repr__)
        DataFrame.old__str__ = copy_func(DataFrame.__str__)
        Series.old__repr__ = copy_func(Series.__repr__)
        Series.old__str__ = copy_func(Series.__str__)
        Index.old__repr__ = copy_func(Index.__repr__)
        Index.old__str__ = copy_func(Index.__str__)

    PandasObject.__str__ = lambda x: pandasprintcolor(x)
    PandasObject.__repr__ = lambda x: pandasprintcolor(x)
    PandasObject.print_stop = print_stop
    PandasObject.max_colwidth = max_colwidth
    PandasObject.repeat_cols = repeat_cols
    DataFrame.__repr__ = lambda x: pandasprintcolor(x)
    DataFrame.__str__ = lambda x: pandasprintcolor(x)
    DataFrame.print_stop = print_stop
    DataFrame.max_colwidth = max_colwidth
    DataFrame.repeat_cols = repeat_cols
    Series.__repr__ = lambda x: pandasprintcolor_s(x)
    Series.__str__ = lambda x: pandasprintcolor_s(x)
    Series.print_stop = print_stop
    Series.max_colwidth = max_colwidth
    Series.repeat_cols = repeat_cols
    Index.__repr__ = lambda x: pandasindexcolor(x)
    Index.__str__ = lambda x: pandasindexcolor(x)
    Index.print_stop = print_stop
    Index.max_colwidth = max_colwidth
    Index.repeat_cols = 10000000
    pd.color_printer_activate = substitute_print_with_color_print
    pd.color_printer_reset = reset_print_options
    pd.color_printer_active = True

def qq_ds_print_nolimit(self, **kwargs):
    try:
        pdp(
            pd_DataFrame(self.reset_index().__array__(), columns=['index']+[str(x) for x in self.columns],copy=False),
            max_lines=0,
            **kwargs,
        )
        print_col_width_len(self.__array__())
    except Exception:
        try:
            pdp(
                pd_DataFrame(self.reset_index().__array__(), columns=['index',self.name],copy=False),
                max_lines=0,
            )
        except Exception:
            pdp(
                pd_DataFrame(self.__array__(),copy=False),
                max_lines=0,
            )
        print_col_width_len(self.__array__())
    return ""


def qq_d_print_columns(self, **kwargs):
    pdp(
        pd_DataFrame(self.columns.__array__().reshape((-1, 1))),
        max_colwidth=0,
        max_lines=0,
        **kwargs,
    )
    return ""


def qq_ds_print_index(self, **kwargs):
    pdp(pd_DataFrame(self.index.__array__().reshape((-1, 1))),    max_lines=0, max_colwidth=0, **kwargs)
    return ""


cpdef add_printer(overwrite_pandas_printer=False):

    PandasObject.ds_color_print_all = qq_ds_print_nolimit
    DataFrame.d_color_print_columns = qq_d_print_columns
    DataFrame.d_color_print_index = qq_ds_print_index
    if overwrite_pandas_printer:
        substitute_print_with_color_print()

################################################# END Pandas Printer ####################################################################

cdef object run_ui2_server(str adb_exe, str device_id, dict[str,object] kwargs):
    cdef:
        object p
    if iswindows:
        p = subprocess_Popen(
            [
                adb_exe,
                "-s",
                device_id,
                "shell",
            ],
            **{
                **invisibledict,
                **kwargs,
                "stdin": PIPE,
                "stdout": DEVNULL,
                "stderr": DEVNULL,
            },
        )
    else:
        p = subprocess_Popen(
            ' '.join([
                adb_exe,
                "-s",
                device_id,
                "shell",
            ]),
            **{
                **invisibledict,
                **kwargs,
                "stdin": PIPE,
                "stdout": DEVNULL,
                "stderr": DEVNULL,
                "shell": True
            },
        )
    p.stdin.write(
        b"am instrument -w -r -e debug false -e class com.github.uiautomator.stub.Stub com.github.uiautomator.test/androidx.test.runner.AndroidJUnitRunner\n"
    )
    p.stdin.flush()
    p.stdin.close()
    return p


cdef bint compile_any_parser(str cpp_file_pure, str exe_file_pure,str exe_file):
    cdef:
        str old_folder
    if os.path.exists(exe_file):
        return True
    old_folder = os.getcwd()
    os.chdir(this_folder)
    try:
        import ziglang
        subprocess_run(
            [
                sys.executable,
                "-m",
                "ziglang",
                "c++",
                "-std=c++2a",
                "-O3",
                "-g0",
                cpp_file_pure,
                "-o",
                exe_file_pure,
            ],
            **{"env":os.environ,**invisibledict},
        )
        if not os.path.exists(exe_file):
            raise OSError("Zig compilation failed")
    except Exception:
        errwrite()
        subprocess_run(
            [
                "g++",
                "-std=c++2a",
                "-O3",
                "-g0",
                cpp_file_pure,
                "-o",
                exe_file_pure,
            ],
            **{"env":os.environ,**invisibledict},
        )

    timesleep(1)
    os.chdir(old_folder)
    return os.path.exists(exe_file)

cdef download_any_parser(str cpp_file, str url):
    if not os.path.exists(cpp_file):
        with requests.get(url) as r:
            if r.status_code == 200:
                with open(cpp_file, mode="wb") as f:
                    f.write(r.content)



cpdef apply_literal_eval_to_tuple(object x):
    if not x:
        return ()
    try:
        if x in cache_apply_literal_eval_to_tuple:
            return cache_apply_literal_eval_to_tuple[x]
    except Exception:
        return ()
    try:
        result = literal_eval(x)
    except Exception:
        result = ()
    if isinstance(result, int):
        result = (result,)
    cache_apply_literal_eval_to_tuple[x] = result
    return result


@cython.boundscheck(True)
cdef object get_ui2_data(str exe_link, str cmd2send, int timeout, dict kwargs):
    cdef:
        object dff,subp
    try:
        dff = read_csv(
            StringIO(
                (
                    b"".join(
                        subprocess_run(
                        [exe_link, cmd2send],
                        **{
                            "env": os_environ,
                            "timeout": timeout,
                            **invisibledict,
                            **kwargs,
                            "capture_output": True,
                        },
                    ).stdout.splitlines(keepends=True)[1:]
                    ).replace(b"\x00",b'')
                ).decode("utf-8", "backslashreplace")
            ),
            engine="python",
            on_bad_lines="warn",
            sep=",",
            na_filter=False,
            quoting=1,
            encoding_errors="backslashreplace",
            index_col=False,
            names=columns_ui2,
        )

        dff.loc[:, "aa_children"] = dff.loc[:, "aa_children"].apply(
            apply_literal_eval_to_tuple
        )
        dff.loc[:, "aa_parents"] = dff.loc[:, "aa_parents"].apply(
            apply_literal_eval_to_tuple
        )
        return dff
    except Exception:
        return pd_DataFrame()

@cython.boundscheck(True)
cdef object get_ui2_data_posix(str cmd2send, int timeout, dict kwargs):
    cdef:
        object dff
    try:
        dff = read_csv(
            StringIO(
                (
                    b"".join(
                        subprocess_run(
                        cmd2send,
                        **{
                            "env": os_environ,
                            "timeout": timeout,
                            "shell": True,
                            **kwargs,
                            "capture_output": True,
                        },).stdout.splitlines(keepends=True)[1:]
                    ).replace(b"\x00",b'')
                ).decode("utf-8", "backslashreplace")
            ),
            engine="python",
            on_bad_lines="warn",
            sep=",",
            na_filter=False,
            quoting=1,
            encoding_errors="backslashreplace",
            index_col=False,
            names=columns_ui2,
        )

        dff.loc[:, "aa_children"] = dff.loc[:, "aa_children"].apply(
            apply_literal_eval_to_tuple
        )
        dff.loc[:, "aa_parents"] = dff.loc[:, "aa_parents"].apply(
            apply_literal_eval_to_tuple
        )
        return dff
    except Exception:
        errwrite()
        return pd_DataFrame()

@cython.final
cdef class InputTapper:
    cdef:
        object x
        object y
        str adb_exe
        str device_id
        str input_tap
        dict kwargs

    def __init__(self, object x, object  y, str device_id, str adb_exe, str input_tap, dict kwargs):
        self.x = x
        self.y = y
        self.adb_exe = adb_exe
        self.device_id = device_id
        self.input_tap = input_tap
        self.kwargs = kwargs if kwargs else {}

    def __repr__(self):
        return "(offset_x=0, offset_y=0)"

    def __str__(self):
        return self.__repr__()

    def __call__(self, int offset_x=0, int offset_y=0):
        if pdisna(self.x) or pdisna(self.y):
            return False
        subprocess_run(
            [
                self.adb_exe,
                "-s",
                self.device_id,
                "shell",
                f"{self.input_tap} {int(self.x + offset_x)} {int(self.y + offset_y)}"
            ],
            **{
                "env": os_environ,
                **invisibledict,
                **self.kwargs,
            },
        )
        return True

@cython.final
cdef class InputTapperLong:
    cdef:
        object x
        object y
        str adb_exe
        str device_id
        str input_tap
        dict kwargs

    def __init__(self, object x, object  y, str device_id, str adb_exe, str input_tap, dict kwargs):
        self.x = x
        self.y = y
        self.adb_exe = adb_exe
        self.device_id = device_id
        self.input_tap = input_tap
        self.kwargs = kwargs if kwargs else {}

    def __repr__(self):
        return "(offset_x=0, offset_y=0, duration=100)"

    def __str__(self):
        return self.__repr__()

    def __call__(self, int offset_x=0, int offset_y=0, int duration=100):
        if pdisna(self.x) or pdisna(self.y):
            return False
        subprocess_run(
            [
                self.adb_exe,
                "-s",
                self.device_id,
                "shell",
                f"{self.input_tap} {int(self.x + offset_x)} {int(self.y + offset_y)} {int(self.x + offset_x)} {int(self.y + offset_y)} {duration}"
            ],
            **{
                "env": os_environ,
                **invisibledict,
                **self.kwargs,
            },
        )
        return True

@cython.final
cdef class InputSwipe:
    cdef:
        int x_start
        int y_start
        int x_end
        int y_end
        str adb_exe
        str device_id
        str input_tap
        dict kwargs
        int duration

    def __init__(self, int x_start, int y_start, int x_end, int y_end, str device_id, str adb_exe, str input_tap, dict kwargs, int duration):
        self.x_start = x_start
        self.y_start = y_start
        self.x_end = x_end
        self.y_end = y_end
        self.adb_exe = adb_exe
        self.device_id = device_id
        self.input_tap = input_tap
        self.kwargs = kwargs if kwargs else {}
        self.duration = duration

    def __repr__(self):
        return "(duration=None, offset_start_x=0, offset_start_y=0, offset_end_x=0, offset_end_y=0)"

    def __str__(self):
        return self.__repr__()

    def __call__(self,object duration=None, int offset_start_x=0, int offset_start_y=0, int offset_end_x=0, int offset_end_y=0):
        return subprocess_run(
            [
                self.adb_exe,
                "-s",
                self.device_id,
                "shell",
                f"{self.input_tap} {int(self.x_start + offset_start_x)} {int(self.y_start + offset_start_y)} {int(self.x_end + offset_end_x)} {int(self.y_end + offset_end_y)} {duration if duration is not None else self.duration}"
            ],
            **{
                "env": os_environ,
                **invisibledict,
                **self.kwargs,
            },
        )

cdef int convert_coord_to_int(object o):
    if isinstance(o,int):
        return int(o)
    if pdisna(o):
        return -1
    try:
        return int(o)
    except Exception:
        return -1


cdef (int,int,int,int) convert_to_c_tuple(object o, int width, int height):
    cdef:
        (int,int,int,int) result=(-1,-1,-1,-1)
    if len(o)!=4:
        return result
    result[0]=convert_coord_to_int(o[0])
    if result[0] < 0 or result[0] > width:
        return (-1,-1,-1,-1)
    result[1]=convert_coord_to_int(o[1])
    if result[1] < 0 or result[1] > height:
        return (-1,-1,-1,-1)
    result[2]=convert_coord_to_int(o[2])
    if result[2] < 0 or result[2] > width:
        return (-1,-1,-1,-1)
    result[3]=convert_coord_to_int(o[3])
    if result[3] < 0 or result[3] > height:
        return (-1,-1,-1,-1)
    if result[3]<=result[1]:
        return (-1,-1,-1,-1)
    if result[2]<=result[0]:
        return (-1,-1,-1,-1)
    return result

cpdef get_part_of_screenshot(list[str] cmd, int width, int height, list coords, dict kwargs, object taken_screenshot=None):
    cdef:
        object image=taken_screenshot if taken_screenshot is not None else take_screenshot(cmd=cmd, width=width, height=height,kwargs=kwargs)
        dict[object,tuple[int,int,int,int]] lookup_dict1={}
        dict[tuple[int,int,int,int],list] lookup_dict2={}
        dict[tuple[int,int,int,int],object] cropped_numpy_arrays={}
        list[object] resultlist_images = []
        object empty_numpy_array=np.array([],dtype=np.uint8)
        Py_ssize_t coordindex

    try:
        if len(image)==0:
            raise Exception("Screenshot empty")
        for coordindex in range(len(coords)):
            lookup_dict1[coords[coordindex]]= convert_to_c_tuple(coords[coordindex],width,height)
            if lookup_dict1[coords[coordindex]] not in lookup_dict2:
                lookup_dict2[lookup_dict1[coords[coordindex]]]=[]
            lookup_dict2[lookup_dict1[coords[coordindex]]].append(coords[coordindex])

        for key in lookup_dict2:
            if key[0]==-1:
                cropped_numpy_arrays[key]=empty_numpy_array
                continue
            cropped_numpy_arrays[key]=image[key[1] : key[3], key[0] : key[2]]

        for coordindex in range(len(coords)):
            for key, item in lookup_dict2.items():
                if coords[coordindex] in item:
                    resultlist_images.append(cropped_numpy_arrays[key])
        return np.asarray(resultlist_images, dtype="object")
    except Exception:
        return np.asarray([[] for _ in range(len(coords))], dtype="object")

cdef add_events_to_dataframe(object df, str device_id, str adb_exe, str input_cmd, dict kwargs, str input_cmd_swipe):
    try:
        df.loc[:, "aa_input_tap"] = df.apply(
            lambda x: InputTapper(x.aa_center_x, x.aa_center_y, device_id, adb_exe, input_cmd, kwargs), axis=1
        )
        df.loc[:, "aa_input_tap_long"] = df.apply(
            lambda x: InputTapperLong(x.aa_center_x, x.aa_center_y, device_id, adb_exe, input_cmd_swipe, kwargs), axis=1
        )
    except Exception:
        errwrite()

@cython.final
cdef class UiAutomator2:
    cdef:
        str adb_exe
        str device_id
        str download_link1
        str download_link2
        str save_path1
        str save_path2
        int timeout
        bint add_input_tap
        str touch_device
        int touch_device_max
        str input_cmd
        str sendevent_path
        int screen_height
        int screen_width
        dict kwargs
        object thread
        str cmd2send
        str input_cmd_swipe

    def __init__(
        self,
        str adb_exe,
        str device_id,
        str download_link1="https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator-test_with_hidden_elements.apk",
        str download_link2="https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator_with_hidden_elements.apk",
        int timeout=30,
        bint add_input_tap=True,
        str touch_device="/dev/input/event4",
        int touch_device_max=32767,
        str input_cmd="input tap",
        int screen_height=1280,
        int screen_width=720,
        object kwargs=None,
        str input_cmd_swipe="input swipe"
    ):
        self.adb_exe = adb_exe
        self.device_id = device_id
        self.download_link1 = download_link1
        self.download_link2 = download_link2
        self.save_path1 = os.path.join(this_folder, "app-uiautomator-test_with_hidden_elements.apk")
        self.save_path2 = os.path.join(this_folder, "app-uiautomator_with_hidden_elements.apk")
        self.timeout = timeout
        self.add_input_tap = add_input_tap
        self.touch_device = touch_device
        self.touch_device_max = touch_device_max
        self.input_cmd = input_cmd
        self.screen_height = screen_height
        self.screen_width = screen_width
        self.kwargs = {} if not kwargs else kwargs
        self.thread=None
        self.input_cmd_swipe=input_cmd_swipe
        if iswindows:
            self.cmd2send = rf'''"{adb_exe} -s {device_id} shell \\"echo cHJpbnRmICJQT1NUIC9qc29ucnBjLzAgSFRUUC8xLjFcclxuSG9zdDogMTI3LjAuMC4xOjkwMDhcclxuQ29udGVudC1UeXBlOiBhcHBsaWNhdGlvbi9qc29uXHJcbkNvbnRlbnQtTGVuZ3RoOiAlZFxyXG5cclxuJXMiICQocHJpbnRmICd7Impzb25ycGMiOiAiMi4wIiwgImlkIjogIjEiLCAibWV0aG9kIjogImR1bXBXaW5kb3dIaWVyYXJjaHkiLCAicGFyYW1zIjogW3RydWUsIDEwMDAwXX0nIHwgd2MgLWMpICd7Impzb25ycGMiOiAiMi4wIiwgImlkIjogIjEiLCAibWV0aG9kIjogImR1bXBXaW5kb3dIaWVyYXJjaHkiLCAicGFyYW1zIjogW3RydWUsIDEwMDAwXX0nIHwgbmMgMTI3LjAuMC4xIDkwMDg= | base64 -d | sh\\""'''
        else:
            # self.cmd2send = rf'''{exe_file_ui2} '{adb_exe} -s {device_id} shell "curl -X POST -d '\''{{\"jsonrpc\": \"2.0\", \"id\": \"1\", \"method\": \"dumpWindowHierarchy\", \"params\": [true, 10000]}}'\'' '\''http://127.0.0.1:9008/jsonrpc/0'\'' 2>/dev/null"' '''
            self.cmd2send=fr'''{exe_file_ui2} "{adb_exe} -s {device_id} shell 'printf \"POST /jsonrpc/0 HTTP/1.1\r\nHost: 127.0.0.1:9008\r\nContent-Type: application/json\r\nContent-Length: %d\r\n\r\n%s\" \$(printf '\\''{{\"jsonrpc\": \"2.0\", \"id\": \"1\", \"method\": \"dumpWindowHierarchy\", \"params\": [true, 10000]}}'\\'' | wc -c) '\\''{{\"jsonrpc\": \"2.0\", \"id\": \"1\", \"method\": \"dumpWindowHierarchy\", \"params\": [true, 10000]}}'\\'' | nc 127.0.0.1 9008'"'''
    cpdef download_apks(self):
        with requests.get(self.download_link1) as r:
            if r.status_code == 200:
                with open(self.save_path1, "wb") as f:
                    f.write(r.content)
            else:
                raise ValueError("Failed to download app-uiautomator-test.apk")
        with requests.get(self.download_link2) as r:
            if r.status_code == 200:
                with open(self.save_path2, "wb") as f:
                    f.write(r.content)
            else:
                raise ValueError("Failed to download app-uiautomator.apk")

    cpdef install_apks(self):
        subprocess_run(
            [self.adb_exe, "-s", self.device_id, "pm", "install", "-g", self.save_path1],
            **{"env":os_environ,**invisibledict,**self.kwargs}
        )
        subprocess_run(
            [self.adb_exe, "-s", self.device_id, "pm", "install", "-g", self.save_path2],
            **{"env":os_environ,**invisibledict,**self.kwargs}
        )

    def start_server(self, **kwargs):
        self.thread = run_ui2_server(self.adb_exe, self.device_id, kwargs)

    cpdef stop_server(self):
        if not iswindows:
            subprocess_run(rf"""{self.adb_exe} -s {self.device_id} shell 'top -b -n1 | grep -F "com.github.uiautomator.test" | grep -vF "grep" | awk '\''{{system("kill "$1)}}'\'''""",shell=True,env=os_environ)
            timesleep(1)
        self.thread.terminate()

    cpdef get_df(
        self,
        bint with_screenshot=True,
        object timeout=None
    ):
        cdef:
            object df
        try:
            if iswindows:
                df=get_ui2_data(exe_file_ui2, self.cmd2send, timeout if timeout is not None else self.timeout, self.kwargs)
            else:
                df=get_ui2_data_posix(self.cmd2send, timeout if timeout is not None else self.timeout, self.kwargs)
            if self.add_input_tap:
                add_events_to_dataframe(df=df, device_id=self.device_id, adb_exe=self.adb_exe, input_cmd=self.input_cmd, kwargs=self.kwargs, input_cmd_swipe=self.input_cmd_swipe)
        except Exception:
            errwrite()
            df=pd_DataFrame()
            with_screenshot=False
        if with_screenshot:
            df.loc[:, "aa_screenshot"] = get_part_of_screenshot(cmd=[self.adb_exe, "-s", self.device_id, "shell","screencap",], width=self.screen_width, height=self.screen_height, coords=list(zip(df["aa_start_x"], df["aa_start_y"], df["aa_end_x"], df["aa_end_y"])), kwargs=self.kwargs)
        return df


cdef bytes png_pack(bytes png_tag, bytes data):
    return (
        structpack("!I", len(data))
        + png_tag
        + data
        + structpack("!I", 0xFFFFFFFF & zlib_crc32(png_tag + data))
    )


def write_png(object pic):
    cdef:
        int height, width, channels
        bytes buf
        int width_byte_4
    if len(pic.shape) != 3:
        return b""
    height, width, channels = pic.shape
    if channels not in (3,4):
        return b""
    if channels==3:
        buf = np.flipud(
        np.dstack((pic, np.full(pic.shape[:2], 0xFF, dtype=np.uint8)))
        ).tobytes()
    else:
        buf = np.flipud(
        pic
        ).tobytes()
    width_byte_4 = width * 4
    return b"".join(
        (
            b"\x89PNG\r\n\x1a\n",
            png_pack(b"IHDR", structpack("!2I5B", width, height, 8, 6, 0, 0, 0)),
            png_pack(
                b"IDAT",
                zlib_compress(
                    b"".join(
                        b"\x00" + buf[span : span + width_byte_4]
                        for span in range(
                            (height - 1) * width_byte_4, -1, -width_byte_4
                        )
                    ),
                    9,
                ),
            ),
            png_pack(b"IEND", b""),
        )
    )


cdef list parsedata(
    bytes sbytes,
):
    cdef:
        list resultlist = []
        object restofstringasbytes = BytesIO(sbytes)
        object restofstringasbytes_read=restofstringasbytes.read
        int ordnextbyte
        object nextbyte
    while nextbyte := restofstringasbytes_read(1):
        with contextlib_suppress(Exception):
            ordnextbyte = ord(nextbyte)
            if ordnextbyte == SIG_STRING:
                bytes2convert2 = restofstringasbytes_read(2)
                bytes2convert = restofstringasbytes_read(
                    bytes2convert2[len(bytes2convert2) - 1]
                )
                resultlist.append(bytes2convert.decode("utf-8", errors="ignore"))
            elif ordnextbyte == SIG_SHORT:
                bytes2convert = restofstringasbytes_read(2)
                resultlist.append( STRUCT_UNPACK_SIG_SHORT(bytes2convert)[0])
            elif ordnextbyte == SIG_BOOLEAN:
                bytes2convert = restofstringasbytes_read(1)
                resultlist.append( STRUCT_UNPACK_SIG_BOOLEAN(bytes2convert)[0])

            elif ordnextbyte == SIG_BYTE:
                bytes2convert = restofstringasbytes_read(1)
                resultlist.append(STRUCT_UNPACK_SIG_BYTE(bytes2convert)[0])

            elif ordnextbyte == SIG_INT:
                bytes2convert = restofstringasbytes_read(4)
                resultlist.append( STRUCT_UNPACK_SIG_INT(bytes2convert)[0])

            elif ordnextbyte == SIG_FLOAT:
                bytes2convert = restofstringasbytes_read(4)
                resultlist.append(STRUCT_UNPACK_SIG_FLOAT(bytes2convert)[0])

            elif ordnextbyte == SIG_DOUBLE:
                bytes2convert = restofstringasbytes_read(8)
                resultlist.append(STRUCT_UNPACK_SIG_DOUBLE(bytes2convert)[0])

            elif ordnextbyte == SIG_LONG:
                bytes2convert = restofstringasbytes_read(8)
                resultlist.append(STRUCT_UNPACK_SIG_LONG(bytes2convert)[0])

    return resultlist

cdef list[tuple] extract_files_from_zip(object zipfilepath):
    cdef:
        bytes data=b""
        object ioby
        list[tuple] single_files_extracted
        Py_ssize_t len_single_files, single_file_index
    if isinstance(zipfilepath, str) and os.path.exists(zipfilepath):
        with open(zipfilepath, "rb") as f:
            data = f.read()
    else:
        data = zipfilepath
    ioby = BytesIO(data)
    single_files_extracted = []
    with zipfile.ZipFile(ioby, "r") as zip_ref:
        single_files = zip_ref.namelist()
        len_single_files = len(single_files)
        for single_file_index in range(len_single_files):
            with contextlib_suppress(Exception):
                single_files_extracted.append(
                    (
                        single_files[single_file_index],
                        zip_ref.read(single_files[single_file_index]),
                    )
                )
    return single_files_extracted

def parse_window_elements_to_list(
    list[str] dump_cmd,
    **kwargs
):
    cdef:
        bytes zipfilepath
        list[tuple] zipname_zipdata
        Py_ssize_t zip_index
        list result_dicts
    zipfilepath=subprocess_run(dump_cmd,**{**invisibledict, **kwargs,**{'capture_output':True}}).stdout
    if iswindows:
        zipfilepath=zipfilepath.replace(b"\r\n",b"\n")
    zipname_zipdata = extract_files_from_zip(zipfilepath)
    result_dicts=[]
    for zip_index in range(len(zipname_zipdata)):
        with contextlib_suppress(Exception):
            result_dicts.append([parsedata(sbytes=zipname_zipdata[zip_index][1]),zipname_zipdata[zip_index][0]])
    return result_dicts

@cython.boundscheck(True)
cdef object get_fragment_data(
    str android_fragment_parser_exe,
    str parse_cmd,
    int timeout=30,
    object kwargs=None,

):
    cdef:
        object dff
        dict kwargs_add = kwargs if kwargs else {}
    try:
        dff = read_csv(
            StringIO(
                (
                    b"".join(
                        subprocess_run(
                            [android_fragment_parser_exe,parse_cmd],
                            **{'env':os_environ,'timeout':timeout,**invisibledict,**kwargs_add,'capture_output':True}
                        ).stdout.splitlines(keepends=True)[1:]
                    ).replace(b"\x00", b'')
                ).decode("utf-8", "backslashreplace")
            ),
            engine="python",
            on_bad_lines="warn",
            sep=",",
            na_filter=False,
            quoting=1,
            encoding_errors="backslashreplace",
            index_col=False,
            names=columns_fragments,
        ).assign(aa_is_child=False)
        dff.loc[
            (~dff.aa_my_parent_ids.str.endswith(","))
            & (dff.aa_my_parent_ids.str.len() > 0),
            "aa_is_child",
        ] = True
        return dff
    except Exception:
        errwrite()
        return pd_DataFrame()

@cython.boundscheck(True)
cdef object get_fragment_data_posix(
    str parse_cmd,
    int timeout=30,
    object kwargs=None,

):
    cdef:
        object dff
        dict kwargs_add = kwargs if kwargs else {}
    try:
        dff = read_csv(
            StringIO(
                (
                    b"".join(
                        subprocess_run(
                            parse_cmd,
                            **{'env':os_environ,'timeout':timeout,**invisibledict,**kwargs_add,'capture_output':True,"shell":True}
                        ).stdout.splitlines(keepends=True)[1:]
                    ).replace(b"\x00", b'')
                ).decode("utf-8", "backslashreplace")
            ),
            engine="python",
            on_bad_lines="warn",
            sep=",",
            na_filter=False,
            quoting=1,
            encoding_errors="backslashreplace",
            index_col=False,
            names=columns_fragments,
        ).assign(aa_is_child=False)
        dff.loc[
            (~dff.aa_my_parent_ids.str.endswith(","))
            & (dff.aa_my_parent_ids.str.len() > 0),
            "aa_is_child",
        ] = True
        return dff
    except Exception:
        errwrite()
        return pd_DataFrame()

@cython.final
cdef class FragMentDumper:
    cdef:
        str device_id
        str adb_exe
        int timeout
        bint add_input_tap
        str input_cmd
        int screen_height
        int screen_width
        dict kwargs
        str cmd2send
        str input_cmd_swipe
    def __init__(
        self,
        str adb_exe,
        str device_id,
        int timeout=30,
        bint add_input_tap=True,
        str input_cmd="input tap",
        int screen_height=1280,
        int screen_width=720,
        object kwargs=None,
        str input_cmd_swipe="input swipe"
    ):
        self.adb_exe = adb_exe
        self.device_id = device_id
        self.timeout = timeout
        self.add_input_tap = add_input_tap
        self.input_cmd = input_cmd
        self.screen_height = screen_height
        self.screen_width = screen_width
        self.kwargs = kwargs if kwargs else {}
        if iswindows:
            self.cmd2send = rf'''"{adb_exe} -s {device_id} shell dumpsys activity top -a -c --checkin"'''
        else:
            self.cmd2send = rf'''{exe_file_fragment} "{adb_exe} -s {device_id} shell dumpsys activity top -a -c --checkin"'''
        self.input_cmd_swipe=input_cmd_swipe
    def get_df(
        self,
        bint with_screenshot=True,
        object timeout=None,
    ):
        cdef:
            object df

        try:
            if iswindows:
                df = get_fragment_data(
                    android_fragment_parser_exe=exe_file_fragment,
                    parse_cmd=self.cmd2send,
                    timeout=timeout if timeout is not None else self.timeout,
                    kwargs=self.kwargs
                )
            else:
                df = get_fragment_data_posix(
                    parse_cmd=self.cmd2send,
                    timeout=timeout if timeout is not None else self.timeout,
                    kwargs=self.kwargs
                )
            if self.add_input_tap:
                add_events_to_dataframe(df=df, device_id=self.device_id, adb_exe=self.adb_exe, input_cmd=self.input_cmd, kwargs=self.kwargs, input_cmd_swipe=self.input_cmd_swipe)
        except Exception:
            df=pd_DataFrame()
            errwrite()
            with_screenshot=False
        if with_screenshot:
            df.loc[:, "aa_screenshot"] = get_part_of_screenshot(cmd=[self.adb_exe, "-s", self.device_id, "shell","screencap",], width=self.screen_width, height=self.screen_height, coords=list(zip(df["aa_start_x"], df["aa_start_y"], df["aa_end_x"], df["aa_end_y"])), kwargs=self.kwargs)
        return df

@cython.final
cdef class WindowDumper:
    cdef:
        str adb_exe
        str device_id
        int timeout
        bint add_input_tap
        str input_cmd
        int screen_height
        int screen_width
        object kwargs
        list[str] android_window_parser_cmd
        str cmd2send
        str input_cmd_swipe

    def __init__(
        self,
        str adb_exe,
        str device_id,
        int timeout=30,
        bint add_input_tap=True,
        str input_cmd="input tap",
        int screen_height=1280,
        int screen_width=720,
        dict kwargs=None,
        str input_cmd_swipe="input swipe"
    ):

        self.adb_exe = adb_exe
        self.device_id = device_id
        self.timeout = timeout
        self.add_input_tap = add_input_tap
        self.input_cmd = input_cmd
        self.screen_height = screen_height
        self.screen_width = screen_width
        self.kwargs = kwargs if kwargs else {}
        self.android_window_parser_cmd = [adb_exe, "-s", device_id, "shell", "cmd window dump-visible-window-views"]
        if iswindows:
            self.cmd2send = rf'''"{adb_exe} -s {device_id} shell dumpsys activity top -a -c --checkin"'''
        else:
            self.cmd2send = rf'''{exe_file_fragment} "{adb_exe} -s {device_id} shell dumpsys activity top -a -c --checkin"'''
        self.input_cmd_swipe=input_cmd_swipe


    @cython.nonecheck(True)
    @cython.boundscheck(True)
    @cython.wraparound(True)
    @cython.initializedcheck(True)
    @cython.nonecheck(True)
    def get_df(
        self,
        bint with_screenshot=True,
        object timeout=None,
    ):

        cdef:
            object df2,q,df1
            Py_ssize_t qidx,counter,last_index_alldata,mydata,each_key,i,j
            dict mappingdict,mapping_dict,rename_dict
            str newkey
            set allpossible_keys_set
            list aa_start_x, aa_start_y,aa_end_x,aa_end_y,aa_center_x,aa_center_y,alldfs,allpossible_keys,iti,alldata,allmydata
            np.ndarray hashcodes_df1_full, hashcodes_df2_full
            int64_t[:] hashcodes_df1,hashcodes_df2
            bint isgood
        df=pd_DataFrame()
        if iswindows:
            df2=get_fragment_data(
                android_fragment_parser_exe=exe_file_fragment,
                parse_cmd=self.cmd2send,
                timeout=timeout if timeout else self.timeout,
                kwargs=self.kwargs
            )
        else:
            df2=get_fragment_data_posix(
                parse_cmd=self.cmd2send,
                timeout=timeout if timeout else self.timeout,
                kwargs=self.kwargs
            )
        df2=df2.drop_duplicates(
            subset=["aa_hashcode_int"], keep="first"
        )
        q = parse_window_elements_to_list(
                dump_cmd=self.android_window_parser_cmd,
                **{'timeout':timeout if timeout else self.timeout,'env':os_environ,**invisibledict,**self.kwargs},
            )
        alldfs = []
        for qidx in range(len(q)):
            with contextlib_suppress(Exception):
                iti = q[qidx][0]
                itiname = q[qidx][1]
                propindex = iti.index("propertyIndex")
                mappingdata = iti[propindex : len(iti) - 1][1:]
                mappingdict = {
                    k: v
                    for k, v in sorted(
                        dict(zip(mappingdata[::2], mappingdata[1::2])).items(),
                        key=lambda item: item[0],
                    )
                }
                counter = 0
                iti2 = iti[: propindex - 1]
                alldata = [[[]]]
                last_index_alldata = 0
                for qq in iti2:
                    if qq == "END":
                        counter = 0
                        alldata.append("END")
                        alldata.append([[]])
                    else:
                        if counter % 2 == 0 and qq != 0:
                            mykey = mappingdict.get(qq, None)
                            if mykey is None:
                                last_index_alldata = len(alldata[len(alldata) - 1]) - 1
                                alldata[len(alldata) - 1][last_index_alldata].append(qq)
                            else:
                                alldata[len(alldata) - 1].append([mykey])
                        elif counter % 2 == 1:
                            last_index_alldata = len(alldata[len(alldata) - 1]) - 1
                            alldata[len(alldata) - 1][last_index_alldata].append(qq)
                        if counter % 2 == 0 and qq == 0:
                            alldata.append([])
                            continue
                        counter += 1

                allmydata = []
                for aa in alldata:
                    if aa == "END":
                        continue
                    else:
                        if aa:
                            aa2 = [x for x in aa if x]
                            if not aa2:
                                continue
                            if len(aa2) > 1 and aa2[-1][0].startswith("meta:__child__"):
                                allmydata.append(aa2[: len(aa2) - 1])
                                allmydata.append(aa2[len(aa2) - 1])
                            else:
                                allmydata.append(aa2)
                newkey = "-1"
                mapping_dict = {}
                mapping_dict[newkey] = []
                allpossible_keys_set = set()
                for mydata in range(len(allmydata)):
                    if (
                        allmydata[mydata]
                        and isinstance(allmydata[mydata][0], str)
                        and allmydata[mydata][0].startswith("meta:__child__")
                        and len(allmydata[mydata]) > 2
                    ):
                        newkey = hex(allmydata[mydata][4])[2:]
                        mapping_dict[newkey] = []
                        allpossible_keys_set.add("CHILD_META")
                        mapping_dict[newkey].append(("CHILD_META", tuple(allmydata[mydata])))
                        mapping_dict[newkey].append(("aa_hashcode_int", allmydata[mydata][4]))
                    else:
                        mapping_dict[newkey].extend(
                            (tuple(x) if len(x) == 2 else (x[0], tuple(x[1:])) for x in allmydata[mydata])
                        )
                for values in mapping_dict.values():
                    for value in values:
                        allpossible_keys_set.add(value[0])
                allpossible_keys = sorted(allpossible_keys_set)
                for key in mapping_dict:
                    mapping_dict[key] = dict(mapping_dict[key])
                    for each_key in range(len(allpossible_keys)):
                        if allpossible_keys[each_key] not in mapping_dict[key]:
                            mapping_dict[key][allpossible_keys[each_key]] = None
                df1 = pd_DataFrame.from_dict(mapping_dict, orient="index")
                hashcodes_df1_full = df1["aa_hashcode_int"].fillna(-1).astype(np.int64).__array__()
                hashcodes_df2_full = df2["aa_hashcode_int"].astype(np.int64).__array__()
                hashcodes_df1=hashcodes_df1_full
                hashcodes_df2=hashcodes_df2_full
                aa_start_x = []
                aa_start_y = []
                aa_end_x = []
                aa_end_y = []
                aa_center_x = []
                aa_center_y = []
                isgood = False
                for j in range(len(hashcodes_df1)):
                    for i in range(len(hashcodes_df2)):
                        if hashcodes_df2[i] == hashcodes_df1[j]:
                            aa_start_x.append(df2["aa_start_x"].iloc[i])
                            aa_start_y.append(df2["aa_start_y"].iloc[i])
                            aa_end_x.append(df2["aa_end_x"].iloc[i])
                            aa_end_y.append(df2["aa_end_y"].iloc[i])
                            aa_center_x.append(df2["aa_center_x"].iloc[i])
                            aa_center_y.append(df2["aa_center_y"].iloc[i])
                            isgood = True
                            break
                    else:
                        aa_start_x.append(-1)
                        aa_start_y.append(-1)
                        aa_end_x.append(-1)
                        aa_end_y.append(-1)
                        aa_center_x.append(-1)
                        aa_center_y.append(-1)

                if not isgood:
                    continue
                rename_dict = {x: "aa_" + x.replace(":", "_") for x in df1.columns}
                df1 = df1.rename(columns=rename_dict, inplace=False)
                df1.loc[:, "aa_start_x"] = aa_start_x
                df1.loc[:, "aa_start_y"] = aa_start_y
                df1.loc[:, "aa_end_x"] = aa_end_x
                df1.loc[:, "aa_end_y"] = aa_end_y
                df1.loc[:, "aa_center_x"] = aa_center_x
                df1.loc[:, "aa_center_y"] = aa_center_y
                df1.loc[:, "aa_window_name"] = itiname
                alldfs.append(df1)
                break
        try:
            if len(alldfs)>0:
                df=alldfs[0]
            else:
                return pd_DataFrame()
            df["aa_hashcode_hex"]=df.index.__array__().copy()
            df=df.reset_index(drop=True)
            if self.add_input_tap:
                add_events_to_dataframe(df=df, device_id=self.device_id, adb_exe=self.adb_exe, input_cmd=self.input_cmd, kwargs=self.kwargs, input_cmd_swipe=self.input_cmd_swipe)
        except Exception:
            errwrite()

            with_screenshot=False
        if with_screenshot:
            df.loc[:, "aa_screenshot"] = get_part_of_screenshot(cmd=[self.adb_exe, "-s", self.device_id, "shell","screencap",], width=self.screen_width, height=self.screen_height, coords=list(zip(df["aa_start_x"], df["aa_start_y"], df["aa_end_x"], df["aa_end_y"])), kwargs=self.kwargs)
        return df


@cython.final
cdef class UiAutomatorClassic:
    cdef:
        str adb_exe
        str device_id
        list[str] uiautomator_parser
        int timeout
        bint add_input_tap
        str input_cmd
        int screen_height
        int screen_width
        str dump_path
        str dump_path_local
        list[str] cmd_del_dump
        list[str] cmd_pull_dump
        dict kwargs
        str input_cmd_swipe

    def __init__(
        self,
        str adb_exe,
        str device_id,
        int timeout=30,
        bint add_input_tap=True,
        str input_cmd="input tap",
        int screen_height=768,
        int screen_width=1024,
        object kwargs=None,
        str input_cmd_swipe="input swipe"
    ):
        self.adb_exe = adb_exe
        self.device_id = device_id
        self.timeout = timeout
        self.add_input_tap = add_input_tap
        self.input_cmd = input_cmd
        self.screen_height = screen_height
        self.screen_width = screen_width
        self.dump_path = "/sdcard/window_dump.xml"
        self.dump_path_local=os.path.join(this_folder,"window_dump.xml")
        self.cmd_del_dump = [adb_exe, "-s", device_id, "shell", f"rm -f {self.dump_path};uiautomator dump"]
        self.cmd_pull_dump = [adb_exe, "-s", device_id, "pull", self.dump_path]
        self.uiautomator_parser = [exe_file_ui1,self.dump_path_local]
        self.kwargs=kwargs if kwargs else {}
        self.input_cmd_swipe=input_cmd_swipe

    def get_df(
        self,
        bint with_screenshot=True,
        object timeout=None,
    ):
        cdef:
            object df
            str current_folder
        df=pd_DataFrame()
        current_folder=os.getcwd()
        try:
            if os.path.exists(self.dump_path_local):
                try:
                    os.remove(self.dump_path_local)
                except Exception:
                    errwrite()
            os.chdir(this_folder)
            subprocess_run(
                self.cmd_del_dump,
                **{'env':os_environ,'timeout':timeout,**invisibledict,**self.kwargs}
            )
            subprocess_run(
                self.cmd_pull_dump,
                **{'env':os_environ,'timeout':timeout,**invisibledict,**self.kwargs}
            )
            df = read_csv(
                StringIO(subprocess_run(
                self.uiautomator_parser,
                **{'env':os_environ,'timeout':timeout,**invisibledict,**self.kwargs,'capture_output':True}
            ).stdout.decode("utf-8","backslashreplace")),
                engine="python",
                on_bad_lines="warn",
                encoding="utf-8",
                sep=",",
                quoting=1,
                na_filter=False,
                encoding_errors="backslashreplace",
                index_col=False,
                header=0,
            )
        except Exception:
            errwrite()

            return df
        finally:
            os.chdir(current_folder)
        df.columns=[f"aa_{col}" if not col.startswith("aa_") else col for col in df.columns]
        if self.add_input_tap:
            add_events_to_dataframe(df=df, device_id=self.device_id, adb_exe=self.adb_exe, input_cmd=self.input_cmd, kwargs=self.kwargs, input_cmd_swipe=self.input_cmd_swipe)
        if with_screenshot:
            df.loc[:, "aa_screenshot"] = get_part_of_screenshot(cmd=[self.adb_exe, "-s", self.device_id, "shell","screencap",], width=self.screen_width, height=self.screen_height, coords=list(zip(df["aa_start_x"], df["aa_start_y"], df["aa_end_x"], df["aa_end_y"])), kwargs=self.kwargs)
        return df

cpdef write_numpy_array_to_ppm_pic(str path, uint8_t[:] flat_pic, int width, int height):
    cdef:
        Py_ssize_t i
        Py_ssize_t len_flat_pic=len(flat_pic)
        string cpp_path = convert_python_object_to_cpp_string(path)
        FILE *f
    f=fopen(cpp_path.c_str(),write_binary.c_str())
    if not f:
        return False
    fprintf(f, ppm_header.c_str(), width, height, 255)
    for i in range(len_flat_pic):
        fputc(flat_pic[i],f)
    fclose(f)
    return True


cdef vec_rgbxycount search_colors_rgb_with_count(Py_ssize_t start_x, Py_ssize_t start_y, uint8_t[:,:,:] image, uint8_t[:,:] colors) noexcept nogil:
    cdef:
        vec_rgbxycount results
        Py_ssize_t i,j, k
        Py_ssize_t color_count
    for k in range(colors.shape[0]):
        color_count=0
        for i in range(image.shape[0]):
            for j in range(image.shape[1]):
                if colors[k][0]==image[i][j][2] and colors[k][1]==image[i][j][1] and colors[k][2]==image[i][j][0]:
                    results.emplace_back(color_rgb_with_coords_and_count(start_x+j,start_y+i,0,colors[k][0],colors[k][1],colors[k][2]))
                    color_count+=1
        if color_count==0:
            continue
        for i in range(results.size()-1, <Py_ssize_t>results.size()-color_count-1,-1):
            results[i].count=color_count
    return results

cpdef search_for_colors_in_elements(
    object df,
    uint8_t[:,:] colors,
    str result_column="aa_colorsearch",
    str screenshot_column="aa_screenshot",
    str start_x="aa_start_x",
    str start_y="aa_start_y",
    str end_x="aa_end_x",
    str end_y="aa_end_y",
    ):
    cdef:
        list allresults = []
        dict alreadydone = {}
        object indextuple,item
        object allresults_append=allresults.append
    for _, item in df.iterrows():
        if not np.any(item[screenshot_column]):
            allresults_append([])
            continue
        indextuple = (
            item[start_x],
            item[start_y],
            item[end_x],
            item[end_y],
        )
        if indextuple in alreadydone:
            allresults_append(alreadydone[indextuple])
            continue
        alreadydone[indextuple] = search_colors_rgb_with_count(
            start_x=item[start_x],
            start_y=item[start_y],
            image=item[screenshot_column],
            colors=colors,
        )
        allresults_append(alreadydone[indextuple])

    df.loc[:,result_column] = np.asarray(allresults, dtype="object")

cdef list[list[Py_ssize_t]] _tesser_group_words(
    object df,
    Py_ssize_t limit_x,
    object col_start_x="aa_start_x",
    object col_end_x="aa_end_x",
    object col_start_y="aa_start_y",
    object col_end_y="aa_end_y",
):
    cdef:
        np.ndarray a_start_x_full = df[col_start_x].astype(np.int64).__array__() - limit_x
        np.ndarray a_start_y_full = df[col_start_y].astype(np.int64).__array__()
        np.ndarray a_end_x_full = df[col_end_x].astype(np.int64).__array__() + limit_x
        np.ndarray a_end_y_full = df[col_end_y].astype(np.int64).__array__()
        int64_t[:] a_start_x=a_start_x_full
        int64_t[:] a_start_y=a_start_y_full
        int64_t[:] a_end_x=a_end_x_full
        int64_t[:] a_end_y=a_end_y_full
        Py_ssize_t len_startx = a_start_x.shape[0]
        Py_ssize_t i,j,k, inters,inter
        vector[vector[Py_ssize_t]] intersecting
        bint invector
        vector[Py_ssize_t] last_values_size, now_value_size
        dict[Py_ssize_t,set[Py_ssize_t]] intersecting_dict = {}
        list[list[Py_ssize_t]] groups = []
        list[Py_ssize_t] h

    intersecting.reserve(len_startx)
    for i in range(len_startx):
        intersecting.emplace_back()
        for j in range(len_startx):
            if not (
                a_end_x[i] < a_start_x[j]
                or a_start_x[i] > a_end_x[j]
                or a_end_y[i] < a_start_y[j]
                or a_start_y[i] > a_end_y[j]
            ):
                if intersecting[intersecting.size() - 1].empty():
                    intersecting[intersecting.size() - 1].emplace_back(j)
                    continue
                invector=False
                for k in range(intersecting[intersecting.size() - 1].size()):
                    if intersecting[intersecting.size() - 1][k]==j:
                        invector=True
                        break
                if not invector:
                    intersecting[intersecting.size() - 1].emplace_back(j)


    for inters in range(intersecting.size()):
        for inter in range(intersecting[inters].size()):
            if intersecting[inters][inter] not in intersecting_dict:
                intersecting_dict[intersecting[inters][inter]] = set()
            intersecting_dict[intersecting[inters][inter]].update((intersecting[inters]))

    for item in intersecting_dict.values():
        now_value_size.emplace_back(len(item))
    while check_vec_equal(last_values_size,now_value_size):
        last_values_size.clear()
        for j in range(now_value_size.size()):
            last_values_size.emplace_back(now_value_size[j])
        now_value_size.clear()
        for key in intersecting_dict:
            for key2 in intersecting_dict[key]:
                intersecting_dict[key2].update(intersecting_dict[key])

        for item in intersecting_dict.values():
            now_value_size.emplace_back(len(item))

    for value in intersecting_dict.values():
        h=sorted(value)
        if h not in groups:
            groups.append(h)
    return groups

cdef object tesser_group_words(
    object df,
    Py_ssize_t limit_x = 20,
    object col_start_x = "aa_start_x",
    object col_end_x = "aa_end_x",
    object col_start_y = "aa_start_y",
    object col_end_y = "aa_end_y",
    object col_text = "aa_text",
):
    cdef:
        object df2
        list[list[Py_ssize_t]] iloc_groups
        list[list[Py_ssize_t]] loc_groups = []
        list[str] text_data = []
        Py_ssize_t linecounter,group,text_iloc,item

    df2 = df.loc[
        (df[col_text] != "")
        & (~df[col_start_x].isna())
        & (~df[col_end_x].isna())
        & (~df[col_start_y].isna())
        & (~df[col_end_y].isna())
    ]
    iloc_groups = _tesser_group_words(
        df=df2,
        limit_x=limit_x,
        col_start_x=col_start_x,
        col_end_x=col_end_x,
        col_start_y=col_start_y,
        col_end_y=col_end_y,
    )
    text_iloc = df2.columns.to_list().index("aa_text")
    df.insert(0, column="aa_text_group", value=-1)
    df.insert(0, column="aa_text_line", value="")
    linecounter = 0
    for group in range(len(iloc_groups)):
        loc_groups.append([])
        for item in range(len(iloc_groups[group])):
            loc_groups[len(loc_groups) - 1].append(df2.index[iloc_groups[group][item]])
            text_data.append(df2.iat[iloc_groups[group][item], text_iloc])
        df.loc[loc_groups[len(loc_groups) - 1], "aa_text_line"] = " ".join(text_data)
        df.loc[loc_groups[len(loc_groups) - 1], "aa_text_group"] = linecounter
        linecounter += 1
        text_data.clear()
    df.rename(columns={"aa_text": "aa_word"}, inplace=True)
    return df.rename(columns={"aa_text_line": "aa_text"}, inplace=False)

cdef bint check_vec_equal(vector[Py_ssize_t]& v1,vector[Py_ssize_t]& v2):
    cdef:
        Py_ssize_t i
    if v1.size()!=v2.size():
        return False
    for i in range(v1.size()):
        if v1[i]!=v2[i]:
            return False
    return True

cpdef object tesseract_np_array(np.ndarray pic,dict kwargs,str tesseract_path='tesseract', object tesseract_args=("-l", "por+eng", "--oem", "3"),Py_ssize_t word_group_limit=20,bint delete_tmp_files=True):
    cdef:
        object df

        str path=get_tmpfile(suffix=".ppm")
        str path_pure=path[:len(path)-4]
        str path_hocr=f"{path_pure}.hocr"
        list[str] tmp_files=[path,path_pure,path_hocr]
        Py_ssize_t tmpindex
        uint8_t[:] flat_pic = pic.ravel()
        int width=pic.shape[1]
        int height=pic.shape[0]
        list[str] tesseract_cmd=[tesseract_path, path, path_pure, *tesseract_args , "-c", "tessedit_create_hocr=1", "-c", "hocr_font_info=1"]
    write_numpy_array_to_ppm_pic(path=path, flat_pic=flat_pic, width=width, height=height)
    subprocess_run(tesseract_cmd, **{**invisibledict, **kwargs})
    df=pd_DataFrame()
    try:
        df = read_csv(
            StringIO(subprocess_run([exe_file_tesser,path_hocr], **{**invisibledict, **kwargs, 'capture_output':True}).stdout.decode("utf-8")),
            engine="python",
            on_bad_lines="warn",
            sep=",",
            na_filter=False,
            quoting=1,
            encoding_errors="backslashreplace",
            index_col=False,
        )
    except Exception:
        errwrite()
    df.columns=[f"aa_{col}" if not col.startswith("aa_") else col for col in df.columns]
    if delete_tmp_files:
        for tmpindex in range(len(tmp_files)):
            with contextlib_suppress(Exception):
                os.remove(tmp_files[tmpindex])
    if df.empty:
        return df
    return tesser_group_words(
        df=df,
        limit_x = word_group_limit,
        col_start_x = "aa_start_x",
        col_end_x = "aa_end_x",
        col_start_y = "aa_start_y",
        col_end_y = "aa_end_y",
        col_text = "aa_text",
    )

cpdef object get_tesseract_df(list[str] cmd, int width, int height ,dict kwargs,str tesseract_path='tesseract', object tesseract_args=("-l", "por+eng", "--oem", "3"),Py_ssize_t word_group_limit=20,bint delete_tmp_files=True):
    cdef:
        np.ndarray pic = take_screenshot(cmd=cmd, width=width, height=height, kwargs=kwargs)
        object df
    df=tesseract_np_array(pic=pic,kwargs=kwargs,tesseract_path=tesseract_path, tesseract_args=tesseract_args, word_group_limit=word_group_limit,delete_tmp_files=delete_tmp_files)
    df.loc[:, "aa_screenshot"] = get_part_of_screenshot(cmd=["",], width=width, height=height, coords=list(zip(df["aa_start_x"], df["aa_start_y"], df["aa_end_x"], df["aa_end_y"])), kwargs={},taken_screenshot=pic)
    return df

cdef list[str,str] get_name_not_in_cols(np.ndarray columns1, np.ndarray columns2):
    cdef:
        str idxtmp1 = "___IDXTMP{number2replace}___"
        str idxtmp2 = "___IDXTMP{number2replace}___"
        Py_ssize_t startnumber_1 = 0
        Py_ssize_t startnumber_2 = 1
        str newcol1,newcol2
    newcol1 = idxtmp1.format(number2replace=startnumber_1)
    newcol2 = idxtmp2.format(number2replace=startnumber_2)
    while newcol1 in columns1:
        startnumber_1 += 2
        newcol1 = idxtmp1.format(number2replace=startnumber_1)
    while newcol2 in columns2:
        startnumber_2 += 2
        newcol2 = idxtmp2.format(number2replace=startnumber_2)
    return [newcol1, newcol2]


def fuzzmatch(
    df1,
    df2,
    left_on,
    right_on,
    result_column="aa_match",
    idx_column2="fuzzidx2",
    function="ab_map_damerau_levenshtein_distance_2ways",
):

    cdef:
        object df11,df22,result1,result2,finalresult1,finalresult2,dffinal
        str idxtmp1,idxtmp2
        PyStringMatcher pysm
        dict q
        list maplist1 = []
        list maplist2 = []
        list matchlist = []
        list notfound
    if not isinstance(df2, DataFrame):
        df2 = pd_DataFrame(df2, columns=[right_on])
    df11 = df1.copy()
    df22 = df2.copy()
    df1 = (
        df1.loc[(df1[left_on].str.strip() != "")]
        .dropna(subset=[left_on])
        .drop_duplicates(subset=[left_on])
        .reset_index(drop=True)
        .copy()
    )
    df2 = (
        df2.loc[(df2[right_on].str.strip() != "")]
        .dropna(subset=[right_on])
        .drop_duplicates(subset=[right_on])
        .reset_index(drop=True)
        .copy()
    )
    idxtmp1, idxtmp2 = get_name_not_in_cols(df1.columns.__array__(), df2.columns.__array__())
    pysm = PyStringMatcher(
        df1[left_on],
        df2[right_on],
    )
    q = getattr(pysm, function)()

    # print(df1)
    # print(df2)
    for x in q.values():
        with contextlib_suppress(Exception):
            realstring1 = df1.loc[x["aa_index_1"], left_on]
            realstring2 = df2.loc[x["aa_index_2"], right_on]
            result1 = df11.loc[df11[left_on] == realstring1].index
            result2 = df22.loc[df22[right_on] == realstring2].index[0]
            maplist1.extend(result1)
            maplist2.extend([result2 for _ in range(len(result1))])
            matchlist.extend((x["aa_match"] for _ in range(len(result1))))

    finalresult1 = (
        df11.loc[maplist1].assign(**{idxtmp1: maplist1}).reset_index(drop=True)
    )
    finalresult2 = (
        df22.loc[maplist2]
        .assign(**{idxtmp2: maplist2, result_column: matchlist})
        .reset_index(drop=True)
    )
    dffinal = pd.concat([finalresult1, finalresult2], axis=1)
    dffinal.index = dffinal[idxtmp1].__array__().copy()
    dffinal.drop(idxtmp1, axis=1, inplace=True)
    notfound = sorted(set(df11.index) - set(maplist1))
    dffinal2 = pd.concat([dffinal, df11.loc[notfound]], axis=0).loc[df11.index]
    try:
        dffinal2.loc[:,idxtmp2] = dffinal2[idxtmp2].astype("Int64")
    except Exception:
        errwrite()
    return dffinal2.rename(columns={idxtmp2: idx_column2})

@cython.final
cdef class TesserParser:
    cdef:
        str device_id
        str adb_exe
        bint add_input_tap
        str input_cmd
        int screen_height
        int screen_width
        dict kwargs
        list[str] cmd2send
        str tesseract_path
        list[str] tesseract_args
        int word_group_limit
        bint delete_tmp_files
        str input_cmd_swipe

    def __init__(
        self,
        str adb_exe,
        str device_id,
        str tesseract_path='tesseract',
        int word_group_limit=20,
        bint delete_tmp_files=True,
        object tesseract_args=("-l", "por+eng", "--oem", "3"),
        bint add_input_tap=True,
        str input_cmd="input tap",
        int screen_height=1280,
        int screen_width=720,
        object kwargs=None,
        str input_cmd_swipe="input swipe"

    ):
        self.adb_exe = adb_exe
        self.device_id = device_id
        self.tesseract_path=tesseract_path
        self.add_input_tap = add_input_tap
        self.input_cmd = input_cmd
        self.screen_height = screen_height
        self.screen_width = screen_width
        self.kwargs = kwargs if kwargs else {}
        self.cmd2send = [adb_exe,"-s", device_id, "shell", "screencap"]
        self.tesseract_args=list(tesseract_args)
        self.word_group_limit=word_group_limit
        self.delete_tmp_files=delete_tmp_files
        self.input_cmd_swipe=input_cmd_swipe

    def get_df(
        self,
        object tesseract_args=None,
        object word_group_limit=None,
        object delete_tmp_files=None,
    ):
        cdef:
            object df
        df= get_tesseract_df(
                cmd=self.cmd2send,
                width=self.screen_width,
                height=self.screen_height,
                kwargs=self.kwargs,
                tesseract_path=self.tesseract_path,
                tesseract_args=tesseract_args if tesseract_args is not None else self.tesseract_args,
                word_group_limit=word_group_limit if word_group_limit is not None else self.word_group_limit,
                delete_tmp_files=delete_tmp_files if delete_tmp_files is not None else self.delete_tmp_files
                )
        if self.add_input_tap:
            add_events_to_dataframe(df=df, device_id=self.device_id, adb_exe=self.adb_exe, input_cmd=self.input_cmd, kwargs=self.kwargs, input_cmd_swipe=self.input_cmd_swipe)
        return df

cpdef d_fm_damerau_levenshtein_distance_1way(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="damerau_levenshtein_distance_1way_match",
        idx_column2="damerau_levenshtein_distance_1way_idx",
        function="ab_map_damerau_levenshtein_distance_1way",
    )


cpdef d_fm_damerau_levenshtein_distance_2ways(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="damerau_levenshtein_distance_2ways_match",
        idx_column2="damerau_levenshtein_distance_2ways_idx",
        function="ab_map_damerau_levenshtein_distance_2ways",
    )


cpdef d_fm_hemming_distance_1way(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="hemming_distance_1way_match",
        idx_column2="hemming_distance_1way_idx",
        function="ab_map_hemming_distance_1way",
    )


cpdef d_fm_hemming_distance_2ways(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="hemming_distance_2ways_match",
        idx_column2="hemming_distance_2ways_idx",
        function="ab_map_hemming_distance_2ways",
    )


cpdef d_fm_jaro_2ways(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="jaro_2ways_match",
        idx_column2="jaro_2ways_idx",
        function="ab_map_jaro_2ways",
    )


cpdef d_fm_jaro_distance_1way(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="jaro_distance_1way_match",
        idx_column2="jaro_distance_1way_idx",
        function="ab_map_jaro_distance_1way",
    )


cpdef d_fm_jaro_winkler_distance_1way(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="jaro_winkler_distance_1way_match",
        idx_column2="jaro_winkler_distance_1way_idx",
        function="ab_map_jaro_winkler_distance_1way",
    )


cpdef d_fm_jaro_winkler_distance_2ways(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="jaro_winkler_distance_2ways_match",
        idx_column2="jaro_winkler_distance_2ways_idx",
        function="ab_map_jaro_winkler_distance_2ways",
    )


cpdef d_fm_levenshtein_distance_1way(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="levenshtein_distance_1way_match",
        idx_column2="levenshtein_distance_1way_idx",
        function="ab_map_levenshtein_distance_1way",
    )


cpdef d_fm_levenshtein_distance_2ways(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="levenshtein_distance_2ways_match",
        idx_column2="levenshtein_distance_2ways_idx",
        function="ab_map_levenshtein_distance_2ways",
    )


cpdef d_fm_longest_common_subsequence_v0(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="longest_common_subsequence_v0_match",
        idx_column2="longest_common_subsequence_v0_idx",
        function="ab_map_longest_common_subsequence_v0",
    )


cpdef d_fm_longest_common_substring_v0(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="longest_common_substring_v0_match",
        idx_column2="longest_common_substring_v0_idx",
        function="ab_map_longest_common_substring_v0",
    )


cpdef d_fm_longest_common_substring_v1(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="longest_common_substring_v1_match",
        idx_column2="longest_common_substring_v1_idx",
        function="ab_map_longest_common_substring_v1",
    )


cpdef d_fm_subsequence_v1(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="subsequence_v1_match",
        idx_column2="subsequence_v1_idx",
        function="ab_map_subsequence_v1",
    )


cpdef d_fm_subsequence_v2(
    self,
    df2,
    left_on,
    right_on,
):
    return fuzzmatch(
        df1=self,
        df2=df2,
        left_on=left_on,
        right_on=right_on,
        result_column="subsequence_v2_match",
        idx_column2="subsequence_v2_idx",
        function="ab_map_subsequence_v2",
    )


cpdef d_save_screenshots_as_png(
    self, str folder="/sdcard/screenshots_png", str screenshot_column="aa_screenshot"
):
    """
    Saves all screenshots in a given column as PNG files in the specified folder.
    For each unique set of coordinates, only one screenshot is saved, and the
    corresponding filenames are saved in a dictionary.

    Parameters
    ----------
    self : pandas.DataFrame
        The dataframe containing the screenshots
    folder : str, optional
        The folder where the screenshots will be saved, by default "/sdcard/screenshots_png"
    screenshot_column : str, optional
        The column containing the screenshots, by default "aa_screenshot"

    Returns
    -------
    list
        A list of the saved files
    """
    os.makedirs(folder, exist_ok=True)
    screenshotdict = {}
    screenshot_filenames = {}
    for key, item in self.iterrows():
        tuplekey = (item.aa_start_x, item.aa_start_y, item.aa_end_x, item.aa_end_y)
        if tuplekey not in screenshotdict:
            try:
                screenshotdict[tuplekey] = write_png(item[screenshot_column])
            except Exception:
                screenshotdict[tuplekey] = b""
            screenshot_filenames[tuplekey] = [os.path.join(folder, f"{key}.png")]
        else:
            screenshot_filenames[tuplekey].append(os.path.join(folder, f"{key}.png"))

    savedfiles = []
    for key, item in screenshot_filenames.items():
        for file in item:
            print(f"Writing {file}", end="\r")
            with open(file, mode="wb") as f:
                f.write(screenshotdict[key])
            savedfiles.append(file)
    return savedfiles


cpdef d_save_screenshots_as_ppm(
    self, str folder="/sdcard/screenshots_ppm", str screenshot_column="aa_screenshot"
):
    """
    Save screenshots from a DataFrame as PPM files.

    This function iterates through a DataFrame, extracts screenshots from a specified column,
    and saves them as PPM files in a specified folder. Each screenshot is indexed by its
    bounding box coordinates (start and end positions on x and y axes).

    Parameters
    ----------
    self : pandas.DataFrame
        The DataFrame containing the screenshots.
    folder : str, optional
        The folder where the screenshots will be saved, by default "/sdcard/screenshots_ppm".
    screenshot_column : str, optional
        The column containing the screenshots, by default "aa_screenshot".

    Returns
    -------
    list
        A list of the saved PPM file paths.
    """

    os.makedirs(folder, exist_ok=True)
    screenshotdict = {}
    screenshot_filenames = {}
    dummpynp = np.array([], dtype=np.uint8)
    for key, item in self.iterrows():
        tuplekey = (item.aa_start_x, item.aa_start_y, item.aa_end_x, item.aa_end_y)
        if tuplekey not in screenshotdict:
            try:
                screenshotdict[tuplekey] = [
                    item[screenshot_column].ravel(),
                    item[screenshot_column].shape[1],
                    item[screenshot_column].shape[0],
                ]
            except Exception:
                screenshotdict[tuplekey] = [dummpynp, 0, 0]
            screenshot_filenames[tuplekey] = [os.path.join(folder, f"{key}.ppm")]
        else:
            screenshot_filenames[tuplekey].append(os.path.join(folder, f"{key}.ppm"))

    savedfiles = []
    for key, item in screenshot_filenames.items():
        for file in item:
            print(f"Writing {file}", end="\r")
            write_numpy_array_to_ppm_pic(
                file,
                screenshotdict[key][0],
                screenshotdict[key][1],
                screenshotdict[key][2],
            )
            savedfiles.append(file)
    return savedfiles


cpdef d_color_search(self, colors, result_column, screenshot_column="aa_screenshot"):
    """
    Searches for the given colors in the given column of the dataframe,
    and appends the results to a new column in the dataframe.

    Parameters
    ----------
    self : pandas.DataFrame
        The dataframe containing the screenshots.
    colors : list of tuples or np.ndarray
        The colors to search for, given as RGB tuples.
    result_column : str, optional
        The column where the results will be stored, by default None.
    screenshot_column : str, optional
        The column containing the screenshots, by default "aa_screenshot".

    Returns
    -------
    None
    """
    if "aa_screenshot" not in self.columns:
        raise IndexError(f"{screenshot_column} column not found")
    if len(colors) == 0:
        return
    if isinstance(colors[0], int):
        colors = [colors]
    if not isinstance(colors, np.ndarray):
        colors = np.array(colors, dtype=np.uint8)
    if colors.dtype != np.uint8:
        colors = colors.astype(np.uint8)
    first_resultcolumn = f"{result_column}"
    try:
        search_for_colors_in_elements(
            df=self,
            colors=colors,
            result_column=first_resultcolumn,
            screenshot_column=screenshot_column,
            start_x="aa_start_x",
            start_y="aa_start_y",
            end_x="aa_end_x",
            end_y="aa_end_y",
        )
    except Exception:
        self.loc[:, result_column] = np.asarray(
            [[] for _ in range(len(self))], dtype="object"
        )


cdef extern from "nonblockingsubprocess.hpp" nogil :
    cdef cppclass ShellProcessManager:
        void ShellProcessManager(
            string shell_command,
            size_t buffer_size,
            size_t stdout_max_len,
            size_t stderr_max_len,
            string exit_command,
            int print_stdout,
            int print_stderr)
        bint start_shell(unsigned long creationFlag,
                        unsigned long creationFlags,
                        unsigned short wShowWindow,
                        char * lpReserved,
                        char * lpDesktop,
                        char * lpTitle,
                        unsigned long dwX,
                        unsigned long dwY,
                        unsigned long dwXSize,
                        unsigned long dwYSize,
                        unsigned long dwXCountChars,
                        unsigned long dwYCountChars,
                        unsigned long dwFillAttribute,
                        unsigned long dwFlags,
                        unsigned long cbReserved2,
                        unsigned char * lpReserved2,)
        bint stdin_write(string)
        string get_stdout()
        string get_stderr()
        void stop_shell()
        void clear_stdout()
        void clear_stderr()

@cython.final
cdef class CySubProc:
    """
    CySubProc is a Cython class that provides a Python interface to a C++ ShellProcessManager.
    It allows you to start a shell process, write commands to stdin, and read stdout/stderr output without deadlocking.
    The 2 two threads that read from stdout/stderr run in nogil mode
    """
    cdef ShellProcessManager*subproc

    def __init__(self,
                object shell_command,
                size_t buffer_size=4096,
                size_t stdout_max_len=4096,
                size_t stderr_max_len=4096,
                object exit_command=b"exit",
                bint print_stdout=False,
                bint print_stderr=False,
                ):
        r"""
        Initialize the CySubProc object.

        Parameters
        ----------
        shell_command : bytes or str
            The command used to start the shell or interpreter (e.g., b'/bin/bash' or "C:\\Windows\\System32\\cmd.exe").
        buffer_size : int, optional
            The size of the buffer used when reading output, by default 4096.
        stdout_max_len : int, optional
            The maximum length of stdout before truncation or buffering logic, by default 4096.
            It treats the C++ vector that stores the output data like collections.deque
        stderr_max_len : int, optional
            The maximum length of stderr before truncation or buffering logic, by default 4096.
            It treats the C++ vector that stores the output data like collections.deque
        exit_command : bytes or str, optional
            The command sent to gracefully exit the shell, by default b"exit".
        print_stdout : bool, optional
            Whether to print the shell's stdout directly, by default False.
            Stdout is saved nevertheless, it is not lost after printing!
        print_stderr : bool, optional
            Whether to print the shell's stderr directly, by default False.
            Stderr is saved nevertheless, it is not lost after printing!

        Returns
        -------
        None
        """
        cdef:
            string cpp_shell_command
            string cpp_exit_command
        if isinstance(shell_command,bytes):
            cpp_shell_command=<string>shell_command
        else:
            cpp_shell_command=<string>(str(shell_command).encode())
        if isinstance(exit_command,bytes):
            cpp_exit_command=<string>exit_command
        else:
            cpp_exit_command=<string>(str(exit_command).encode())

        self.subproc= new ShellProcessManager(
        shell_command=cpp_shell_command,
        buffer_size=buffer_size,
        stdout_max_len=stdout_max_len,
        stderr_max_len=stderr_max_len,
        exit_command=cpp_exit_command,
        print_stdout=print_stdout,
        print_stderr=print_stderr
    )
    cpdef start_shell(
        self,
        unsigned long  creationFlag=0,
        unsigned long  creationFlags=0x08000000,
        unsigned short  wShowWindow=1,
        object lpReserved=None,
        object lpDesktop=None,
        object lpTitle=None,
        unsigned long  dwX=0,
        unsigned long  dwY=0,
        unsigned long  dwXSize=0,
        unsigned long  dwYSize=0,
        unsigned long  dwXCountChars=0,
        unsigned long  dwYCountChars=0,
        unsigned long  dwFillAttribute=0,
        unsigned long  dwFlags=0,
        unsigned long  cbReserved2=0,
        object lpReserved2=None,
    ):
        r"""
        Start the shell process with specific creation flags and environment parameters.
        On Posix, all arguments are ignored!

        Detailed information can be found on Microsoft's website https://learn.microsoft.com/en-us/windows/win32/procthread/process-creation-flags

        Parameters
        ----------
        creationFlag : int, optional
            A custom flag for process creation, by default 0.
        creationFlags : int, optional
            Additional flags controlling process creation, by default 0x08000000.
        wShowWindow : int, optional
            Flags controlling how the window is shown (e.g., hidden, normal, minimized),
            by default 1 (SW_SHOWNORMAL).
        lpReserved : bytes or str, optional
            Reserved parameter for process creation, by default None.
        lpDesktop : bytes or str, optional
            The name of the desktop for the process, by default None.
        lpTitle : bytes or str, optional
            The title for the new console window, by default None.
        dwX : int, optional
            X-coordinate for the upper-left corner of the window, by default 0.
        dwY : int, optional
            Y-coordinate for the upper-left corner of the window, by default 0.
        dwXSize : int, optional
            Width of the window, by default 0.
        dwYSize : int, optional
            Height of the window, by default 0.
        dwXCountChars : int, optional
            Screen buffer width in character columns, by default 0.
        dwYCountChars : int, optional
            Screen buffer height in character rows, by default 0.
        dwFillAttribute : int, optional
            Initial text and background colors if used in a console, by default 0.
        dwFlags : int, optional
            Flags that control how the creationFlags are used, by default 0.
        cbReserved2 : int, optional
            Reserved for C runtime initialization, by default 0.
        lpReserved2 : bytes or str, optional
            Reserved for C runtime initialization, by default None.

        Returns
        -------
        None
        """
        cdef:
            string cpp_lpReserved, cpp_lpDesktop, cpp_lpTitle, cpp_lpReserved2
            unsigned char* ptr_lpReserved2
            char* ptr_lpReserved
            char* ptr_lpDesktop
            char* ptr_lpTitle
            size_t addr_cpp_lpReserved, addr_cpp_lpDesktop, addr_cpp_lpTitle, addr_cpp_lpReserved2

        if not lpReserved:
            lpReserved=b'\x00'
        if not lpDesktop:
            lpDesktop=b'\x00'
        if not lpTitle:
            lpTitle=b'\x00'
        if not lpReserved2:
            lpReserved2=b'\x00'
        if isinstance(lpReserved, bytes):
            cpp_lpReserved=<string>lpReserved
        else:
            cpp_lpReserved=<string>(str(lpReserved).encode())
        if isinstance(lpDesktop, bytes):
            cpp_lpDesktop=<string>lpDesktop
        else:
            cpp_lpDesktop=<string>(str(lpDesktop).encode())
        if isinstance(lpTitle, bytes):
            cpp_lpTitle=<string>lpTitle
        else:
            cpp_lpTitle=<string>(str(lpTitle).encode())
        if isinstance(lpReserved2, bytes):
            cpp_lpReserved2=<string>lpReserved2
        else:
            cpp_lpReserved2=<string>(str(lpReserved2).encode())

        # Obtain raw pointers to the underlying string data.
        # Cython is nagging when assigning or casting directly to char pointers of .data() (temporary object ... unsafe ... blah blah blah)
        # But the data pointer of the string doesn't not change as long as the size of the string doesn't change which is the case here.
        # It works perfectly on Windows, and on Linux, the pointers and all other arguments are ignored anyways, so they could even be dangling on Posix, it wouldn't matter at all.
        addr_cpp_lpReserved=<size_t>(&(cpp_lpReserved.data()[0]))
        addr_cpp_lpDesktop=<size_t>(&(cpp_lpDesktop.data()[0]))
        addr_cpp_lpTitle=<size_t>(&(cpp_lpTitle.data()[0]))
        addr_cpp_lpReserved2=<size_t>(&(cpp_lpReserved2.data()[0]))

        ptr_lpReserved=<char*>addr_cpp_lpReserved
        ptr_lpDesktop=<char*>addr_cpp_lpDesktop
        ptr_lpTitle=<char*>addr_cpp_lpTitle
        ptr_lpReserved2=<unsigned char*>(addr_cpp_lpReserved2)
        self.subproc.start_shell(
                    creationFlag=creationFlag,
                    creationFlags=creationFlags,
                    wShowWindow=wShowWindow,
                    lpReserved=ptr_lpReserved,
                    lpDesktop=ptr_lpDesktop,
                    lpTitle=ptr_lpTitle,
                    dwX=dwX,
                    dwY=dwY,
                    dwXSize=dwXSize,
                    dwYSize=dwYSize,
                    dwXCountChars=dwXCountChars,
                    dwYCountChars=dwYCountChars,
                    dwFillAttribute=dwFillAttribute,
                    dwFlags=dwFlags,
                    cbReserved2=cbReserved2,
                    lpReserved2=ptr_lpReserved2,
                    )
    cpdef stdin_write(self, object cmd):
        """
        Write a command or input data to the shell process's stdin.

        Parameters
        ----------
        cmd : bytes or str
            The command or data to send to the process via stdin.

        Returns
        -------
        None
        """
        cdef:
            string cpp_cmd
        if isinstance(cmd,bytes):
            cpp_cmd=<string>cmd
        elif isinstance(cmd,str):
            cpp_cmd=<string>(cmd.encode())
        else:
            cpp_cmd=<string>str(cmd).encode()
        self.subproc.stdin_write(cpp_cmd)

    cpdef bytes get_stdout(self):
        """
        Retrieve the current contents of the shell's standard output as bytes, and clears the C++ vector

        Returns
        -------
        bytes
            The raw bytes from the shell's stdout.
        """
        return self.subproc.get_stdout()

    cpdef bytes get_stderr(self):
        """
        Retrieve the current contents of the shell's standard error as bytes, and clears the C++ vector.

        Returns
        -------
        bytes
            The raw bytes from the shell's stderr.
        """
        return self.subproc.get_stderr()

    cpdef stop_shell(self):
        """
        Stop the running shell process gracefully (stops the 2 background threads and writes the exit command 5 times to the shell - in case there are subshells running).

        Returns
        -------
        None
        """
        self.subproc.stop_shell()

    cdef string read_stdout(self):
        """
        Read the current contents of the shell's standard output as a C++ string, and clears the C++ vector.
        This function is Cython only, and has the advantage that it does not convert the data to a Python object

        Returns
        -------
        string
            The raw C++ string from the shell's stdout.
        """
        return self.subproc.get_stdout()

    cdef string read_stderr(self):
        """
        Read the current contents of the shell's standard error as a C++ string, and clears the C++ vector.
        This function is Cython only, and has the advantage that it does not convert the data to a Python object

        Returns
        -------
        string
            The raw C++ string from the shell's stderr.
        """
        return self.subproc.get_stderr()

    def __dealloc__(self):
        """
        Calls the C++ destructor, which executes the C++ stop_shell function
        It deallocates the underlying ShellProcessManager pointer when this object is garbage collected.
        """
        del self.subproc


class Tuppsub(tuple):
    pass

#######################################################################################################################################
###################################################### Global vars ####################################################################
cdef:
    object regex_device_size_node_name = repy.compile(
    r"(?P<tmpindex>^[\d]+)\|(?P<aa_DEVICE>[\d,]+)\s+(?P<aa_SIZE>[\dt]+)\s+(?P<aa_NODE>\d+)\s+(?P<aa_NAME>.*$)",
    flags=re.I,
    )
    object regex_package_start = re.compile("^package:", flags=re.I).sub
    object regex_netstat = re.compile(rb"^\w+\s+\d+\s+\d+.*\s+\d+/.*$", flags=re.I).match
    object proc_match = re.compile(rb"^\s*\d+\s+\w+\s+.*$", flags=re.I).match
    list[str] columns_files = [
        "aa_PermissionsSymbolic",
        "aa_SELinuxContext",
        "aa_FileSize",
        "aa_OwnerUsername",
        "aa_GroupName",
        "aa_SymlinkTarget",
        "aa_ModificationTimestampEpoch",
        "aa_OwnerUID",
        "aa_GroupGID",
        "aa_PermissionsOctal",
        "aa_FullPath",
        "aa_FileName",
    ]
    dict[str,object] dtypes_files = {
        "aa_PermissionsSymbolic": np.dtype("object"),
        "aa_SELinuxContext": np.dtype("object"),
        "aa_FileSize": np.dtype("int64"),
        "aa_OwnerUsername": np.dtype("object"),
        "aa_GroupName": np.dtype("object"),
        "aa_SymlinkTarget": np.dtype("object"),
        "aa_ModificationTimestampEpoch": np.dtype("float64"),
        "aa_OwnerUID": np.dtype("int64"),
        "aa_GroupGID": np.dtype("int64"),
        "aa_PermissionsOctal": np.dtype("int64"),
        "aa_FullPath": np.dtype("object"),
        "aa_FileName": np.dtype("object"),
    }
    list[str] dict_variation=[
        "collections.defaultdict",
        "collections.UserDict",
        "collections.OrderedDict",
    ]
    object forbidden = (
        list,
        tuple,
        set,
        frozenset,
    )
    object allowed = (
        str,
        int,
        float,
        complex,
        bool,
        bytes,
        type(None),
        Tuppsub,
    )


#####################################################################################################################################
###################################################### C++ Stuff ####################################################################

cdef extern from "split_string.hpp" nogil :
    vector[string] split_string(string& input, string& delimiter)

cdef extern from "timeoutstuff.hpp" nogil :
    int64_t get_current_timestamp()


cdef extern from "cppsleep.hpp" nogil :
    void sleep_milliseconds(int milliseconds)

cdef extern from "stripstring.hpp" nogil :
    void strip_spaces_inplace(string& s)



cdef list convert_to_list(object folders):
    if not isinstance(folders, list):
        folders = [folders]
    return folders

cpdef calculate_chmod(object s):
    cdef:
        Py_ssize_t last_index = len(s) - 1
        Py_ssize_t final_result = 0
    if len(s) < 9:
        return -1
    if isinstance(s, str):
        if s[last_index] != "-":
            final_result += 1
        if s[last_index - 1] != "-":
            final_result += 2
        if s[last_index - 2] != "-":
            final_result += 4
        if s[last_index - 3] != "-":
            final_result += 10
        if s[last_index - 4] != "-":
            final_result += 20
        if s[last_index - 5] != "-":
            final_result += 40
        if s[last_index - 6] != "-":
            final_result += 100
        if s[last_index - 7] != "-":
            final_result += 200
        if s[last_index - 8] != "-":
            final_result += 400
        return final_result
    if s[last_index] != 45:
        final_result += 1
    if s[last_index - 1] != 45:
        final_result += 2
    if s[last_index - 2] != 45:
        final_result += 4
    if s[last_index - 3] != 45:
        final_result += 10
    if s[last_index - 4] != 45:
        final_result += 20
    if s[last_index - 5] != 45:
        final_result += 40
    if s[last_index - 6] != 45:
        final_result += 100
    if s[last_index - 7] != 45:
        final_result += 200
    if s[last_index - 8] != 45:
        final_result += 400
    return final_result


################################################# START Recursive Dictstuff ###############################################################
class subi(dict):
    def __missing__(self, k):
        self[k] = self.__class__()
        return self[k]

cdef list_split(l, indices_or_sections):
    Ntotal = len(l)
    try:
        Nsections = len(indices_or_sections) + 1
        div_points = [0] + list(indices_or_sections) + [Ntotal]
    except TypeError:
        Nsections = int(indices_or_sections)
        if Nsections <= 0:
            raise ValueError("number sections must be larger than 0.") from None
        Neach_section, extras = divmod(Ntotal, Nsections)
        section_sizes = (
            [0] + extras * [Neach_section + 1] + (Nsections - extras) * [Neach_section]
        )
        div_points = []
        new_sum = 0
        for i in section_sizes:
            new_sum += i
            div_points.append(new_sum)

    sub_arys = []
    lenar = len(l)
    for i in range(Nsections):
        st = div_points[i]
        end = div_points[i + 1]
        if st >= lenar:
            break
        sub_arys.append((l[st:end]))

    return sub_arys

@cython.boundscheck(True)
@cython.wraparound(True)
@cython.nonecheck(True)
cdef bint isiter(
    object x,
    object consider_iter = (),
    object consider_non_iter = (),
):
    if type(x) in consider_iter:
        return True
    if type(x) in consider_non_iter:
        return False
    if isinstance(x, (int, float, bool, complex, type(None))):
        return False
    if isinstance(x, (list, tuple, set, frozenset, dict)):
        return True
    if isinstance(x, (GeneratorType,Iterable,collections.abc.Iterable,collections.abc.Sequence,typing.Iterable,typing.Iterator)):
        return True
    try:
        iter(x)
        return True
    except Exception:
        pass
    if hasattr(x, "__contains__"):
        try:
            for _ in x:
                return True
        except Exception:
            pass
    if hasattr(x, "__len__"):
        try:
            for _ in x:
                return True
        except Exception:
            pass
    if hasattr(x, "__getitem__"):
        try:
            for _ in x:
                return True
        except Exception:
            pass
    if hasattr(x, "__iter__"):
        try:
            for _ in x:
                return True
        except Exception:
            pass
    if not hasattr(x, "__trunc__"):
        try:
            for _ in x:
                return True
        except Exception:
            pass
    try:
        for _ in x:
            return True
    except Exception:
        pass
    return False

cpdef convert_to_normal_dict(object di):
    if isinstance(di, defaultdict):
        di = {k: convert_to_normal_dict(v) for k, v in di.items()}
    return di

cpdef nested_dict():
    return defaultdict(nested_dict)

@cython.boundscheck(True)
@cython.wraparound(True)
@cython.nonecheck(True)
def dict_merger(*args):
    cdef:
        object newdict = nested_dict()
    for it in args:
        for p in fla_tu(it):
            tcr = type(reduce(operator_getitem, p[1][:-1], it))
            if tcr is tuple or tcr is set:
                tcr = list
            if tcr == list:
                try:
                    if not reduce(operator_getitem, p[1][:-2], newdict)[p[1][-2]]:
                        reduce(operator_getitem, p[1][:-2], newdict)[p[1][-2]] = tcr()
                    reduce(operator_getitem, p[1][:-2], newdict)[p[1][-2]].append(p[0])
                except Exception:
                    try:
                        reduce(operator_getitem, p[1][:-1], newdict)[p[1][-1]] = p[0]
                    except Exception:
                        reduce(operator_getitem, p[1][:-2], newdict)[p[1][-2]] = [
                            reduce(operator_getitem, p[1][:-1], newdict)[p[1][-1]],
                            p[0],
                        ]
            else:
                try:
                    if not reduce(operator_getitem, p[1][:-1], newdict)[p[1][-1]]:
                        reduce(operator_getitem, p[1][:-1], newdict)[p[1][-1]] = p[0]
                    else:
                        reduce(operator_getitem, p[1][:-1], newdict)[p[1][-1]] = [
                            reduce(operator_getitem, p[1][:-1], newdict)[p[1][-1]]
                        ]
                        reduce(operator_getitem, p[1][:-1], newdict)[p[1][-1]].append(
                            p[0]
                        )
                except Exception:
                    reduce(operator_getitem, p[1][:-2], newdict)[p[1][-2]] = [
                        reduce(operator_getitem, p[1][:-1], newdict)[p[1][-1]],
                        p[0],
                    ]
    return convert_to_normal_dict(newdict)



@cython.nonecheck(True)
def aa_flatten_dict_tu(
    object v,
    object listitem,
) :
    if (
        isinstance(v, dict)
        or (hasattr(v, "items") and hasattr(v, "keys"))
        and not isinstance(v, allowed)
    ):
        for k, v2 in v.items():
            newtu = listitem + (k,)
            if isinstance(v2, allowed):
                yield Tuppsub((v2, newtu))
            else:
                yield from aa_flatten_dict_tu(
                    v2, listitem=newtu
                )
    elif isinstance(v, forbidden) and not isinstance(v, allowed):
        for indi, v2 in enumerate(v):
            if isinstance(v2, allowed):
                yield Tuppsub((v2, (listitem + (indi,))))
            else:
                yield from aa_flatten_dict_tu(
                    v2,
                    listitem=(listitem + (indi,)),
                )
    elif isinstance(v, allowed):
        yield Tuppsub((v, listitem))
    else:
        try:
            for indi2, v2 in enumerate(v):
                try:
                    if isinstance(v2, allowed):
                        yield Tuppsub((v2, (listitem + (indi2,))))

                    else:
                        yield aa_flatten_dict_tu(
                            v2,
                            listitem=(listitem + (indi2,)),
                        )
                except Exception:
                    yield Tuppsub((v2, listitem))
        except Exception:
            yield Tuppsub((v, listitem))


def fla_tu(
    object item,
    object walkthrough,
):
    if isinstance(item, allowed):
        yield Tuppsub((item, (walkthrough,)))
    elif isinstance(item, forbidden) and not isinstance(item, allowed):
        for ini, xaa in enumerate(item):
            if not isinstance(xaa, allowed):
                try:
                    yield from fla_tu(
                        xaa,
                        walkthrough=(walkthrough + (ini,)),
                    )

                except Exception:
                    yield Tuppsub((xaa, (walkthrough + (ini,))))
            else:
                yield Tuppsub((xaa, (walkthrough + (ini,))))
    elif isinstance(item, dict):
        if not isinstance(item, allowed):
            yield from aa_flatten_dict_tu(
                item, listitem=walkthrough,
            )
        else:
            yield Tuppsub((item, (walkthrough,)))
    elif (
        hasattr(item, "items") and hasattr(item, "keys")
    ) or (str(type(item)) in dict_variation):
        if not isinstance(item, allowed):
            yield from aa_flatten_dict_tu(
                dict(item), listitem=walkthrough,
            )
        else:
            yield Tuppsub((item, (walkthrough,)))
    else:
        try:
            for ini2, xaa in enumerate(item):
                try:
                    if isinstance(xaa, allowed):
                        yield Tuppsub((xaa, (walkthrough + (ini2,))))
                    else:
                        yield from fla_tu(
                            xaa,
                            walkthrough=(walkthrough + (ini2,)),
                        )
                except Exception:
                    yield Tuppsub((xaa, (walkthrough + (ini2,))))
        except Exception:
            yield Tuppsub((item, (walkthrough,)))

cpdef convert_to_normal_dict_simple(object di):
    if isinstance(di, MultiKeyDict):
        di = {k: convert_to_normal_dict_simple(v) for k, v in di.items()}
    return di

class MultiKeyDict(dict):
    def __init__(self, seq=None, **kwargs):
        if seq:
            super().__init__(seq, **kwargs)

        def convert_dict(di):
            if (isinstance(di, dict) and not isinstance(di, self.__class__)) or (
                hasattr(di, "items") and hasattr(di, "keys") and hasattr(di, "keys")
            ):
                ndi = self.__class__(
                    {},
                )
                for k, v in di.items():
                    ndi[k] = convert_dict(v)
                return ndi
            return di

        for key in self:
            self[key] = convert_dict(self[key])

    def __str__(self):
        return str(self.to_dict())

    def __missing__(self, key):
        self[key] = self.__class__({})
        return self[key]

    def __repr__(self):
        return self.__str__()

    def __delitem__(self, i):
        if isinstance(i, list):
            if len(i) > 1:
                lastkey = i[len(i)-1]
                i = i[:len(i)-1]
                it = iter(i)
                firstkey = next(it)
                value = self[firstkey]
                for element in it:
                    value = operator_itemgetter(element)(value)
                del value[lastkey]
            else:
                super().__delitem__(i[0])
        else:
            super().__delitem__(i)

    def __getitem__(self, key, /):
        if isinstance(key, list):
            if len(key) > 1:
                it = iter(key)
                firstkey = next(it)
                value = self[firstkey]
                for element in it:
                    value = operator_itemgetter(element)(value)
                return value
            else:
                return super().__getitem__(key[0])
        else:
            return super().__getitem__(key)

    def __setitem__(self, i, item):
        if isinstance(i, list):
            if len(i) > 1:
                lastkey = i[len(i)-1]
                i = i[:len(i)-1]
                it = iter(i)
                firstkey = next(it)
                value = self[firstkey]
                for element in it:
                    value = operator_itemgetter(element)(value)
                value[lastkey] = item
            else:
                return super().__setitem__(i[0], item)
        else:
            return super().__setitem__(i, item)

    def to_dict(self):
        return convert_to_normal_dict_simple(self)

    def update(self, other, /, **kwds):
        other = self.__class__(other)
        super().update(other, **kwds)

    def get(self, key, default=None):
        v = default
        if not isinstance(key, list):
            return super().get(key, default)
        else:
            if len(key) > 1:
                it = iter(key)
                firstkey = next(it)
                value = self[firstkey]
                for element in it:
                    if element in value:
                        value = operator_itemgetter(element)(value)
                    else:
                        return default
            else:
                return super().get(key[0], default)
            return value

    def pop(self, key, default=None):
        if not isinstance(key, list):
            return super().pop(key, default)

        elif len(key) == 1:
            return super().pop(key[0], default)
        else:
            return self._del_and_return(key, default)

    def _del_and_return(self, key, default=None):
        newkey = key[:len(key)-1]
        delkey = key[len(key)-1]
        it = iter(newkey)
        firstkey = next(it)
        value = self[firstkey]
        for element in it:
            if element in value:
                value = operator_itemgetter(element)(value)
            else:
                return default

        value1 = value[delkey]
        del value[delkey]
        return value1

    def reversed(self):
        return reversed(list(iter(self.keys())))


class MultiKeyIterDict(MultiKeyDict):
    def __init__(self, /, initialdata=None, **kwargs):
        super().__init__(initialdata, **kwargs)

    def nested_items(self):
        for v, k in fla_tu(self.to_dict()):
            yield list(k), v

    def nested_values(self):
        for v, _ in fla_tu(self.to_dict()):
            yield v

    def nested_keys(self):
        for _, k in fla_tu(self.to_dict()):
            yield list(k)

    def _check_last_item(self):
        cdef:
            list alreadydone = []
            list results = []
        for v, k in fla_tu(self.to_dict()):
            if len(k) > 1 and k not in alreadydone:
                qr = list(k)
                qr=qr[:len(qr)-1]
                if isinstance(v2 := self[qr], (dict, defaultdict)):
                    results.append((list(k), v))
                elif isiter(v2):
                    alreadydone.append(qr)
                    results.append((qr, v2))
                else:
                    results.append((list(k), v))
            else:
                results.append((list(k), v))
        return results

    def nested_value_search(self, value):
        for k, v in self._check_last_item():
            if v == value:
                yield k

    def nested_key_search(self, key):
        return (
            (q := list(takewhile(lambda xx: xx != key, list(x))) + [key], self[q])
            for x in list(self.nested_keys())
            if key in x
        )

    def nested_update(self, *args):
        self.update(dict_merger(self.to_dict(), *args))

    def nested_merge(self, *args):
        return convert_to_normal_dict_simple(dict_merger(self.to_dict(), *args))


cpdef dict nested_list_to_nested_dict(l):
    cdef:
        object di = MultiKeyIterDict()
    for v, k in fla_tu(l):
        di[list(k)] = v
    return di.to_dict()

@cython.boundscheck(True)
@cython.wraparound(True)
@cython.nonecheck(True)
def indent2dict(data, removespaces):
    @lru_cache
    def strstrip(x):
        return x.strip()

    def convert_to_normal_dict_simple(di):
        globcounter = 0

        def _convert_to_normal_dict_simple(di):
            nonlocal globcounter
            globcounter = globcounter + 1
            if not di:
                return globcounter
            if isinstance(di, subi):
                di = {k: _convert_to_normal_dict_simple(v) for k, v in di.items()}
            return di

        return _convert_to_normal_dict_simple(di)

    def splitfunc(alli, dh):
        def splifu(lix, ind):
            try:
                firstsplit = [n for n, y in enumerate(lix) if y[0] == ind]
            except Exception:
                return lix
            result1 = list_split(l=lix, indices_or_sections=firstsplit)
            newi = ind + 1
            splitted = []
            for l in result1:
                if newi < (lendh):
                    if isinstance(l, list):
                        if l:
                            la = splifu(l, newi)
                            splitted.append(la)
                    else:
                        splitted.append(l)
                else:
                    splitted.append(l)
            return splitted

        lendh = len(dh.keys())
        alli2 = [alli[0]] + alli
        return splifu(alli2, ind=0)

    if isinstance(data, (str, bytes)):
        da2 = data.splitlines()
    else:
        da2 = list(data)

    d = defaultdict(list)
    dox = da2.copy()
    dox = [x for x in dox if x.strip()]
    for dx in dox:
        eg = len(dx) - len(dx.lstrip())
        d[eg].append(dx)

    dh = {k: v[1] for k, v in enumerate(sorted(d.items()))}

    alli = []
    for xas in dox:
        for kx, kv in dh.items():
            if xas in kv:
                alli.append([kx, xas])
                break

    iu = splitfunc(alli, dh)

    allra = []
    d = nested_list_to_nested_dict(l=iu)
    lookupdi = {}
    for iasd, ius in enumerate((q for q in fla_tu(d) if not isinstance(q[0], int))):
        if iasd == 0:
            continue
        it = list(takewhile(lambda o: o == 0, reversed(ius[1][:-2])))
        it = ius[1][: -2 - len(it)]
        allra.append([it, ius[0]])
        lookupdi[it] = ius[0]

    allmils = []
    for im, _ in allra:
        mili = []
        for x in reversed(range(1, len(im) + 1)):
            try:
                mili.append(lookupdi[im[:x]])
            except Exception:
                with contextlib_suppress(Exception):
                    mili.append(lookupdi[im[: x - 1]])
        mili = tuple(reversed(mili))
        allmils.append(mili)
    allmilssorted = sorted(allmils, key=len, reverse=True)
    countdict = defaultdict(int)
    difi = subi()
    allmilssorted = [
        tuple(map(strstrip, x) if removespaces else x) for x in allmilssorted
    ]
    for ixas in allmilssorted:
        for rad in range(len(ixas) + 1):
            countdict[ixas[:rad]] += 1
    for key, item in countdict.items():
        if not key:
            continue
        if item != 1:
            continue
        vaxu = difi[key[0]]
        for inxa, kax in enumerate(key):
            if inxa == 0:
                continue
            vaxu = vaxu[kax]

    return convert_to_normal_dict_simple(difi)

cpdef tointstr(v):
    return str(int(v))


cpdef _dumpsys_splitter_to_dict(so,convert_to_dict=True):
    cdef:
        object resultdict = MultiKeyIterDict({})
    for ita in re.split(
        r"\n(?=[^\s])",
        (
            b"".join([k for k in so if k.strip()])
            .decode("utf-8", "backslashreplace")
            .strip()
        ),
    ):
        with contextlib_suppress(Exception):
            result = indent2dict(ita, removespaces=True)
            resultdict.nested_update(result)
    if convert_to_dict:
        return resultdict.to_dict()
    return resultdict

@cython.final
cdef class CommandGetter:
    SH_FIND_FILES_WITH_CONTEXT = r'''{exe_path}find "{folder_path}" -maxdepth {max_depth} -printf "\"%M\",\"%Z\",\"%s\",\"%u\",\"%g\",\"%l\",\"%T@\",\"%U\",\"%G\",\"%m\",\"%p\",\"%f\"\n";find "{folder_path}" -maxdepth {max_depth} -iname ".*" -printf "\"%M\",\"%Z\",\"%s\",\"%u\",\"%g\",\"%l\",\"%T@\",\"%U\",\"%G\",\"%m\",\"%p\",\"%f\"\n"'''
    SH_FIND_PROP_FILES = '{exe_path}find / -type f -name "*.prop" 2>/dev/null'
    SH_FIND_FILES_WITH_ENDING = '{exe_path}find "{folder_path}" -type f -maxdepth {max_depth} -iname "*.{ending}" 2>/dev/null'
    SH_SAVE_SED_REPLACE = r"""
subssed() {{
    {exe_path}sed -i "s/$({exe_path}printf "%s" "$1" | {exe_path}sed -e 's/\([[\/.*]\|\]\)/\\&/g')/$({exe_path}printf "%s" "$2" | {exe_path}sed -e 's/[\/&]/\\&/g')/g" "$3"
}}

sourcef='{file_path}'
str1='{string2replace}'
str2='{replacement}'
perm=$({exe_path}stat -c '%a' "$sourcef")
owner=$({exe_path}stat -c '%U' "$sourcef")
group=$({exe_path}stat -c '%G' "$sourcef")
atime=$({exe_path}stat -c '%X' "$sourcef")
mtime=$({exe_path}stat -c '%Y' "$sourcef")
selinux_context="$({exe_path}ls -Z "$sourcef" | {exe_path}awk '{{print $1}}')"
subssed "$sourcef" "$str1" "$str2"
{exe_path}chown "$owner" "$sourcef"
{exe_path}chgrp "$group" "$sourcef"
{exe_path}chmod "$perm" "$sourcef"
{exe_path}touch -m -d "@$mtime" "$sourcef"
{exe_path}touch -a -d "@$atime" "$sourcef"
{exe_path}chcon "$selinux_context" "$sourcef"
"""
    SH_SVC_ENABLE_WIFI = "{exe_path}svc wifi enable"
    SH_SVC_DISABLE_WIFI = "{exe_path}svc wifi disable"
    SH_TRIM_CACHES = "{exe_path}pm trim-caches 99999G"
    SH_FORCE_OPEN_APP = r"""
while true; do
  capture="$({exe_path}dumpsys window | {exe_path}grep -E 'mCurrentFocus|mFocusedApp' | {exe_path}grep -c "{package_name}")"
  if {exe_path}[ $capture -eq 0 ]; then
    {exe_path}am start "$({exe_path}cmd package resolve-activity --brief {package_name} | {exe_path}tail -n 1)"
  else
    break
  fi
  {exe_path}sleep {sleep_time}
  capture="$({exe_path}dumpsys window | {exe_path}grep -E 'mCurrentFocus|mFocusedApp' | {exe_path}grep -c "{package_name}")"
  if {exe_path}[ $capture -eq 0 ]; then
    {exe_path}monkey -p {package_name} 1 >/dev/null
  else
    break
  fi
  {exe_path}sleep {sleep_time}
done
"""
    SH_GET_MAIN_ACTIVITY = (
        r"""{exe_path}cmd package resolve-activity --brief {package_name}"""
    )
    SH_SVC_POWER_SHUT_DOWN = "{exe_path}svc power shutdown"
    SH_SVC_POWER_REBOOT = "{exe_path}svc power reboot"
    SH_DUMPSYS_DROPBOX = "{exe_path}dumpsys dropbox --print"
    SH_SET_NEW_LAUNCHER = """{exe_path}pm set-home-activity {package_name}"""
    SH_GET_PID_OF_SHELL = "echo $$"
    SH_TAR_FOLDER = "{exe_path}tar czf '{dst}' '{src}'"
    SH_EXTRACT_FILES = r"""UZ() {
  f_name="$(basename "$1" | awk -F. 'BEGIN{OFS="_"} {if ($(NF-1) == "tar") {ext = $(NF-1) "." $NF; NF-=2} else {ext = $NF; NF--}; print $0}')"
  f_ext="$(echo "$1" | awk -F. '{if ($(NF-1) == "tar") {print $(NF-1) "." $NF} else {print $NF}}')"
  case "$f_ext" in
    "zip")
      echo "unzipping zip to $f_name"
      mkdir "$f_name"
      unzip "$1" -d "$f_name"
      ;;
    "tar.gz" | "tgz")
      echo "unzipping tar.gz to $f_name"
      mkdir "$f_name"
      tar -zxvf "$1" -C "$f_name"
      ;;
    "tar")
      echo "unzipping tar to $f_name"
      mkdir "$f_name"
      tar -xvf "$1" -C "$f_name"
      ;;
    "gz")
      echo "unzipping gz to $f_name"
      mkdir "$f_name"
      gunzip -c "$1" > "$f_name"
      ;;
    "7z")
      echo "unzipping 7z to $f_name"
      mkdir "$f_name"
      7z x "$1" -o"$f_name"
      ;;
    *)
      echo "unknown file type: $f_ext"
      ;;
  esac
}

UZ COMPRESSED_ARCHIVE FOLDER_TO_EXTRACT
"""
    SH_GET_USER_ROTATION = "{exe_path}settings get system user_rotation"
    SH_COPY_DIR_RECURSIVE = "{exe_path}cp -R {src} {dst}"
    SH_BACKUP_FILE = "{exe_path}cp -R {src} {src}.bak"
    SH_REMOVE_FOLDER = "{exe_path}rm -r -f {folder}"
    SH_WHOAMI = "{exe_path}whoami"
    SH_DUMPSYS_PACKAGE = "{exe_path}dumpsys package {package}"
    SH_GRANT_PERMISSION = "{exe_path}pm grant {package} {permission}"
    SH_REVOKE_PERMISSION = "{exe_path}pm revoke {package} {permission}"
    SH_GET_AVAIABLE_KEYBOARDS = "{exe_path}ime list -s -a"
    SH_GET_ACTIVE_KEYBOARD = "{exe_path}settings get secure default_input_method"
    SH_GET_ALL_KEYBOARDS_INFORMATION = "{exe_path}ime list -a"
    SH_ENABLE_KEYBOARD = "{exe_path}ime enable {keyboard}"
    SH_DISABLE_KEYBOARD = "{exe_path}ime disable {keyboard}"
    SH_SET_KEYBOARD = "{exe_path}ime set {keyboard}"
    SH_IS_KEYBOARD_SHOWN = (
        '{exe_path}dumpsys input_method | {exe_path}grep -E "mInputShown|mVisibleBound"'
    )
    SH_SHOW_TOUCHES = "{exe_path}settings put system show_touches 1"
    SH_SHOW_TOUCHES_NOT = "{exe_path}settings put system show_touches 0"
    SH_SHOW_POINTER_LOCATION = "{exe_path}settings put system pointer_location 1"
    SH_SHOW_POINTER_LOCATION_NOT = "{exe_path}settings put system pointer_location 0"
    SH_INPUT_SWIPE = "{exe_path}input swipe {x1} {y1} {x2} {y2} {duration}"
    SH_INPUT_TAP = "{exe_path}input tap {x} {y}"
    SH_CLEAR_FILE_CONTENT = """{exe_path}printf "%s" '' > {file_path}"""
    SH_MAKEDIRS = "{exe_path}mkdir -p {folder}"
    SH_TOUCH = "{exe_path}touch {file_path}"
    SH_MV = "{exe_path}mv {src} {dst}"
    SH_OPEN_ACCESSIBILITY_SETTINGS = (
        "{exe_path}am start -a android.settings.ACCESSIBILITY_SETTINGS"
    )
    SH_OPEN_ADVANCED_MEMORY_PROTECTION_SETTINGS = (
        "{exe_path}am start -a android.settings.ADVANCED_MEMORY_PROTECTION_SETTINGS"
    )
    SH_OPEN_AIRPLANE_MODE_SETTINGS = (
        "{exe_path}am start -a android.settings.AIRPLANE_MODE_SETTINGS"
    )
    SH_OPEN_ALL_APPS_NOTIFICATION_SETTINGS = (
        "{exe_path}am start -a android.settings.ALL_APPS_NOTIFICATION_SETTINGS"
    )
    SH_OPEN_APN_SETTINGS = "{exe_path}am start -a android.settings.APN_SETTINGS"
    SH_OPEN_APPLICATION_DETAILS_SETTINGS = (
        "{exe_path}am start -a android.settings.APPLICATION_DETAILS_SETTINGS"
    )
    SH_OPEN_APPLICATION_DEVELOPMENT_SETTINGS = (
        "{exe_path}am start -a android.settings.APPLICATION_DEVELOPMENT_SETTINGS"
    )
    SH_OPEN_APPLICATION_SETTINGS = (
        "{exe_path}am start -a android.settings.APPLICATION_SETTINGS"
    )
    SH_OPEN_APP_LOCALE_SETTINGS = (
        "{exe_path}am start -a android.settings.APP_LOCALE_SETTINGS"
    )
    SH_OPEN_APP_NOTIFICATION_BUBBLE_SETTINGS = (
        "{exe_path}am start -a android.settings.APP_NOTIFICATION_BUBBLE_SETTINGS"
    )
    SH_OPEN_APP_NOTIFICATION_SETTINGS = (
        "{exe_path}am start -a android.settings.APP_NOTIFICATION_SETTINGS"
    )
    SH_OPEN_APP_OPEN_BY_DEFAULT_SETTINGS = (
        "{exe_path}am start -a android.settings.APP_OPEN_BY_DEFAULT_SETTINGS"
    )
    SH_OPEN_APP_SEARCH_SETTINGS = (
        "{exe_path}am start -a android.settings.APP_SEARCH_SETTINGS"
    )
    SH_OPEN_APP_USAGE_SETTINGS = (
        "{exe_path}am start -a android.settings.APP_USAGE_SETTINGS"
    )
    SH_OPEN_AUTOMATIC_ZEN_RULE_SETTINGS = (
        "{exe_path}am start -a android.settings.AUTOMATIC_ZEN_RULE_SETTINGS"
    )
    SH_OPEN_AUTO_ROTATE_SETTINGS = (
        "{exe_path}am start -a android.settings.AUTO_ROTATE_SETTINGS"
    )
    SH_OPEN_BATTERY_SAVER_SETTINGS = (
        "{exe_path}am start -a android.settings.BATTERY_SAVER_SETTINGS"
    )
    SH_OPEN_BLUETOOTH_SETTINGS = (
        "{exe_path}am start -a android.settings.BLUETOOTH_SETTINGS"
    )
    SH_OPEN_CAPTIONING_SETTINGS = (
        "{exe_path}am start -a android.settings.CAPTIONING_SETTINGS"
    )
    SH_OPEN_CAST_SETTINGS = "{exe_path}am start -a android.settings.CAST_SETTINGS"
    SH_OPEN_CHANNEL_NOTIFICATION_SETTINGS = (
        "{exe_path}am start -a android.settings.CHANNEL_NOTIFICATION_SETTINGS"
    )
    SH_OPEN_CONDITION_PROVIDER_SETTINGS = (
        "{exe_path}am start -a android.settings.CONDITION_PROVIDER_SETTINGS"
    )
    SH_OPEN_DATA_ROAMING_SETTINGS = (
        "{exe_path}am start -a android.settings.DATA_ROAMING_SETTINGS"
    )
    SH_OPEN_DATA_USAGE_SETTINGS = (
        "{exe_path}am start -a android.settings.DATA_USAGE_SETTINGS"
    )
    SH_OPEN_DATE_SETTINGS = "{exe_path}am start -a android.settings.DATE_SETTINGS"
    SH_OPEN_DEVICE_INFO_SETTINGS = (
        "{exe_path}am start -a android.settings.DEVICE_INFO_SETTINGS"
    )
    SH_OPEN_DISPLAY_SETTINGS = "{exe_path}am start -a android.settings.DISPLAY_SETTINGS"
    SH_OPEN_DREAM_SETTINGS = "{exe_path}am start -a android.settings.DREAM_SETTINGS"
    SH_OPEN_HARD_KEYBOARD_SETTINGS = (
        "{exe_path}am start -a android.settings.HARD_KEYBOARD_SETTINGS"
    )
    SH_OPEN_HOME_SETTINGS = "{exe_path}am start -a android.settings.HOME_SETTINGS"
    SH_OPEN_IGNORE_BACKGROUND_DATA_RESTRICTIONS_SETTINGS = "{exe_path}am start -a android.settings.IGNORE_BACKGROUND_DATA_RESTRICTIONS_SETTINGS"
    SH_OPEN_IGNORE_BATTERY_OPTIMIZATION_SETTINGS = (
        "{exe_path}am start -a android.settings.IGNORE_BATTERY_OPTIMIZATION_SETTINGS"
    )
    SH_OPEN_INPUT_METHOD_SETTINGS = (
        "{exe_path}am start -a android.settings.INPUT_METHOD_SETTINGS"
    )
    SH_OPEN_INPUT_METHOD_SUBTYPE_SETTINGS = (
        "{exe_path}am start -a android.settings.INPUT_METHOD_SUBTYPE_SETTINGS"
    )
    SH_OPEN_INTERNAL_STORAGE_SETTINGS = (
        "{exe_path}am start -a android.settings.INTERNAL_STORAGE_SETTINGS"
    )
    SH_OPEN_LOCALE_SETTINGS = "{exe_path}am start -a android.settings.LOCALE_SETTINGS"
    SH_OPEN_LOCATION_SOURCE_SETTINGS = (
        "{exe_path}am start -a android.settings.LOCATION_SOURCE_SETTINGS"
    )
    SH_OPEN_MANAGE_ALL_APPLICATIONS_SETTINGS = (
        "{exe_path}am start -a android.settings.MANAGE_ALL_APPLICATIONS_SETTINGS"
    )
    SH_OPEN_MANAGE_ALL_SIM_PROFILES_SETTINGS = (
        "{exe_path}am start -a android.settings.MANAGE_ALL_SIM_PROFILES_SETTINGS"
    )
    SH_OPEN_MANAGE_APPLICATIONS_SETTINGS = (
        "{exe_path}am start -a android.settings.MANAGE_APPLICATIONS_SETTINGS"
    )
    SH_OPEN_MANAGE_DEFAULT_APPS_SETTINGS = (
        "{exe_path}am start -a android.settings.MANAGE_DEFAULT_APPS_SETTINGS"
    )
    SH_OPEN_MANAGE_SUPERVISOR_RESTRICTED_SETTING = (
        "{exe_path}am start -a android.settings.MANAGE_SUPERVISOR_RESTRICTED_SETTING"
    )
    SH_OPEN_MANAGE_WRITE_SETTINGS = (
        "{exe_path}am start -a android.settings.MANAGE_WRITE_SETTINGS"
    )
    SH_OPEN_MEMORY_CARD_SETTINGS = (
        "{exe_path}am start -a android.settings.MEMORY_CARD_SETTINGS"
    )
    SH_OPEN_NETWORK_OPERATOR_SETTINGS = (
        "{exe_path}am start -a android.settings.NETWORK_OPERATOR_SETTINGS"
    )
    SH_OPEN_NFCSHARING_SETTINGS = (
        "{exe_path}am start -a android.settings.NFCSHARING_SETTINGS"
    )
    SH_OPEN_NFC_PAYMENT_SETTINGS = (
        "{exe_path}am start -a android.settings.NFC_PAYMENT_SETTINGS"
    )
    SH_OPEN_NFC_SETTINGS = "{exe_path}am start -a android.settings.NFC_SETTINGS"
    SH_OPEN_NIGHT_DISPLAY_SETTINGS = (
        "{exe_path}am start -a android.settings.NIGHT_DISPLAY_SETTINGS"
    )
    SH_OPEN_NOTIFICATION_ASSISTANT_SETTINGS = (
        "{exe_path}am start -a android.settings.NOTIFICATION_ASSISTANT_SETTINGS"
    )
    SH_OPEN_NOTIFICATION_LISTENER_DETAIL_SETTINGS = (
        "{exe_path}am start -a android.settings.NOTIFICATION_LISTENER_DETAIL_SETTINGS"
    )
    SH_OPEN_NOTIFICATION_LISTENER_SETTINGS = (
        "{exe_path}am start -a android.settings.NOTIFICATION_LISTENER_SETTINGS"
    )
    SH_OPEN_NOTIFICATION_POLICY_ACCESS_SETTINGS = (
        "{exe_path}am start -a android.settings.NOTIFICATION_POLICY_ACCESS_SETTINGS"
    )
    SH_OPEN_PRINT_SETTINGS = "{exe_path}am start -a android.settings.PRINT_SETTINGS"
    SH_OPEN_PRIVACY_SETTINGS = "{exe_path}am start -a android.settings.PRIVACY_SETTINGS"
    SH_OPEN_QUICK_ACCESS_WALLET_SETTINGS = (
        "{exe_path}am start -a android.settings.QUICK_ACCESS_WALLET_SETTINGS"
    )
    SH_OPEN_QUICK_LAUNCH_SETTINGS = (
        "{exe_path}am start -a android.settings.QUICK_LAUNCH_SETTINGS"
    )
    SH_OPEN_REGIONAL_PREFERENCES_SETTINGS = (
        "{exe_path}am start -a android.settings.REGIONAL_PREFERENCES_SETTINGS"
    )
    SH_OPEN_SATELLITE_SETTING = (
        "{exe_path}am start -a android.settings.SATELLITE_SETTING"
    )
    SH_OPEN_SEARCH_SETTINGS = "{exe_path}am start -a android.settings.SEARCH_SETTINGS"
    SH_OPEN_SECURITY_SETTINGS = (
        "{exe_path}am start -a android.settings.SECURITY_SETTINGS"
    )
    SH_OPEN_SETTINGS = "{exe_path}am start -a android.settings.SETTINGS"
    SH_OPEN_SETTINGS = "{exe_path}am start -a android.settings.SETTINGS"
    SH_OPEN_SOUND_SETTINGS = "{exe_path}am start -a android.settings.SOUND_SETTINGS"
    SH_OPEN_STORAGE_VOLUME_ACCESS_SETTINGS = (
        "{exe_path}am start -a android.settings.STORAGE_VOLUME_ACCESS_SETTINGS"
    )
    SH_OPEN_SYNC_SETTINGS = "{exe_path}am start -a android.settings.SYNC_SETTINGS"
    SH_OPEN_USAGE_ACCESS_SETTINGS = (
        "{exe_path}am start -a android.settings.USAGE_ACCESS_SETTINGS"
    )
    SH_OPEN_USER_DICTIONARY_SETTINGS = (
        "{exe_path}am start -a android.settings.USER_DICTIONARY_SETTINGS"
    )
    SH_OPEN_VOICE_INPUT_SETTINGS = (
        "{exe_path}am start -a android.settings.VOICE_INPUT_SETTINGS"
    )
    SH_OPEN_VPN_SETTINGS = "{exe_path}am start -a android.settings.VPN_SETTINGS"
    SH_OPEN_VR_LISTENER_SETTINGS = (
        "{exe_path}am start -a android.settings.VR_LISTENER_SETTINGS"
    )
    SH_OPEN_WEBVIEW_SETTINGS = "{exe_path}am start -a android.settings.WEBVIEW_SETTINGS"
    SH_OPEN_WIFI_IP_SETTINGS = "{exe_path}am start -a android.settings.WIFI_IP_SETTINGS"
    SH_OPEN_WIFI_SETTINGS = "{exe_path}am start -a android.settings.WIFI_SETTINGS"
    SH_OPEN_WIRELESS_SETTINGS = (
        "{exe_path}am start -a android.settings.WIRELESS_SETTINGS"
    )
    SH_OPEN_ZEN_MODE_PRIORITY_SETTINGS = (
        "{exe_path}am start -a android.settings.ZEN_MODE_PRIORITY_SETTINGS"
    )
    SH_OPEN_DEVELOPER_SETTINGS = (
        "{exe_path}am start -a android.settings.DEVELOPER_SETTINGS"
    )
    SH_RESCAN_MEDIA_FOLDER = """folder='{folder}'
string="$({exe_path}find "$folder" -type f 2> /dev/null)"
stringlines="$({exe_path}printf "%s\n" "$string" | {exe_path}wc -l)"
for i in $({exe_path}seq 1 $stringlines); do
  line="$({exe_path}printf "%s\n" "$string" | {exe_path}sed -n "$i"p)"
  {exe_path}am broadcast -a android.intent.action.MEDIA_SCANNER_SCAN_FILE -d "file://${{line}}"
done"""
    SH_RESCAN_MEDIA_FILE = '{exe_path}am broadcast -a android.intent.action.MEDIA_SCANNER_SCAN_FILE -d "file://{file_path}"'
    SH_SCREENCAP_PNG = "{exe_path}screencap -p {file_path}"
    SH_DUMP_PROCESS_MEMORY_TO_SDCARD = R"""getmemdump() {
	mkdir -p /sdcard/$1
    cat /proc/$1/maps | grep -v -E "rw-p.*deleted\)" | grep -E "rw-p.*" | awk '{print $1}' | (
        IFS="-"
        while read a b; do
            adec=$(printf "%d\n" 0x"$a")
            bdec=$(printf "%d\n" 0x"$b")
            si=$((bdec - adec))
            fina="/sdcard/$1/mem_$a.bin"
            echo "$fina $adec $bdec $si"
            dd if=/proc/$1/mem ibs=1 obs="$si" skip="$adec" count="$si" of="$fina"
        done
    )
}
oldIFS=$IFS
getmemdump PID2OBSERVE
IFS=$oldIFS"""
    SH_PM_CLEAR = "{exe_path}pm clear {package}"
    SH_CHANGE_WM_SIZE = "{exe_path}wm size {width}x{height}"
    SH_WM_RESET_SIZE = "{exe_path}wm size reset"
    SH_GET_WM_DENSITY = "{exe_path}wm density"
    SH_CHANGE_WM_DENSITY = "{exe_path}wm density {density}"
    SH_WM_RESET_DENSITY = "{exe_path}wm density reset"
    SH_AM_SCREEN_COMPAT_ON = "{exe_path}am screen-compat on {package}"
    SH_AM_SCREEN_COMPAT_OFF = "{exe_path}am screen-compat off {package}"
    SH_ENABLE_NOTIFICATIONS = (
        "{exe_path}settings put global heads_up_notifications_enabled 1"
    )
    SH_DISABLE_NOTIFICATIONS = (
        "{exe_path}settings put global heads_up_notifications_enabled 0"
    )
    SH_STILL_IMAGE_CAMERA = (
        "{exe_path}am start -a android.media.action.STILL_IMAGE_CAMERA"
    )
    SH_DISABLE_NETWORK_INTERFACE = "{exe_path}ifconfig {nic} down &"
    SH_ENABLE_NETWORK_INTERFACE = "{exe_path}ifconfig {nic} up &"
    SH_GET_LINUX_VERSION = "{exe_path}uname -a"
    SH_START_PACKAGE_WITH_MONKEY = "{exe_path}monkey -p {package} 1"
    SH_EXPAND_NOTIFICATIONS = "%scmd statusbar expand-notifications"
    SH_EXPAND_SETTINGS = "%scmd statusbar expand-settings"
    SH_LIST_PERMISSION_GROUPS = "%spm list permission-groups"
    SH_INPUT_DPAD_TAP = "%sinput dpad tap %s %s"
    SH_INPUT_KEYBOARD_TAP = "%sinput keyboard tap %s %s"
    SH_INPUT_MOUSE_TAP = "%sinput mouse tap %s %s"
    SH_INPUT_TOUCHPAD_TAP = "%sinput touchpad tap %s %s"
    SH_INPUT_GAMEPAD_TAP = "%sinput gamepad tap %s %s"
    SH_INPUT_TOUCHNAVIGATION_TAP = "%sinput touchnavigation tap %s %s"
    SH_INPUT_JOYSTICK_TAP = "%sinput joystick tap %s %s"
    SH_INPUT_TOUCHSCREEN_TAP = "%sinput touchscreen tap %s %s"
    SH_INPUT_STYLUS_TAP = "%sinput stylus tap %s %s"
    SH_INPUT_TRACKBALL_TAP = "%sinput trackball tap %s %s"
    SH_INPUT_DPAD_SWIPE = "%sinput dpad swipe %s %s %s %s %s"
    SH_INPUT_DPAD_DRAGANDDROP = "%sinput dpad draganddrop %s %s %s %s %s"
    SH_INPUT_DPAD_ROLL = "%sinput dpad roll %s %s"
    SH_INPUT_KEYBOARD_SWIPE = "%sinput keyboard swipe %s %s %s %s %s"
    SH_INPUT_KEYBOARD_DRAGANDDROP = "%sinput keyboard draganddrop %s %s %s %s %s"
    SH_INPUT_KEYBOARD_ROLL = "%sinput keyboard roll %s %s"
    SH_INPUT_MOUSE_SWIPE = "%sinput mouse swipe %s %s %s %s %s"
    SH_INPUT_MOUSE_DRAGANDDROP = "%sinput mouse draganddrop %s %s %s %s %s"
    SH_INPUT_MOUSE_ROLL = "%sinput mouse roll %s %s"
    SH_INPUT_TOUCHPAD_SWIPE = "%sinput touchpad swipe %s %s %s %s %s"
    SH_INPUT_TOUCHPAD_DRAGANDDROP = "%sinput touchpad draganddrop %s %s %s %s %s"
    SH_INPUT_TOUCHPAD_ROLL = "%sinput touchpad roll %s %s"
    SH_INPUT_GAMEPAD_SWIPE = "%sinput gamepad swipe %s %s %s %s %s"
    SH_INPUT_GAMEPAD_DRAGANDDROP = "%sinput gamepad draganddrop %s %s %s %s %s"
    SH_INPUT_GAMEPAD_ROLL = "%sinput gamepad roll %s %s"
    SH_INPUT_TOUCHNAVIGATION_SWIPE = "%sinput touchnavigation swipe %s %s %s %s %s"
    SH_INPUT_TOUCHNAVIGATION_DRAGANDDROP = (
        "%sinput touchnavigation draganddrop %s %s %s %s %s"
    )
    SH_INPUT_TOUCHNAVIGATION_ROLL = "%sinput touchnavigation roll %s %s"
    SH_INPUT_JOYSTICK_SWIPE = "%sinput joystick swipe %s %s %s %s %s"
    SH_INPUT_JOYSTICK_DRAGANDDROP = "%sinput joystick draganddrop %s %s %s %s %s"
    SH_INPUT_JOYSTICK_ROLL = "%sinput joystick roll %s %s"
    SH_INPUT_TOUCHSCREEN_SWIPE = "%sinput touchscreen swipe %s %s %s %s %s"
    SH_INPUT_TOUCHSCREEN_DRAGANDDROP = "%sinput touchscreen draganddrop %s %s %s %s %s"
    SH_INPUT_TOUCHSCREEN_ROLL = "%sinput touchscreen roll %s %s"
    SH_INPUT_STYLUS_SWIPE = "%sinput stylus swipe %s %s %s %s %s"
    SH_INPUT_STYLUS_DRAGANDDROP = "%sinput stylus draganddrop %s %s %s %s %s"
    SH_INPUT_STYLUS_ROLL = "%sinput stylus roll %s %s"
    SH_INPUT_TRACKBALL_SWIPE = "%sinput trackball swipe %s %s %s %s %s"
    SH_INPUT_TRACKBALL_DRAGANDDROP = "%sinput trackball draganddrop %s %s %s %s %s"
    SH_INPUT_TRACKBALL_ROLL = "%sinput trackball roll %s %s"
    SH_OPEN_URL = "{exe_path}am start -a android.intent.action.VIEW -d {url}"

    SH_READ_WRITE_REMOUNT_V01 = """busybox mount -o remount,rw /"""
    SH_READ_WRITE_REMOUNT_V02 = """busybox mount --all -o remount,rw -t vfat1"""
    SH_READ_WRITE_REMOUNT_V03 = """busybox mount --all -o remount,rw -t ext4"""
    SH_READ_WRITE_REMOUNT_V04 = """busybox mount -o remount,rw"""
    SH_READ_WRITE_REMOUNT_V05 = """busybox mount -o remount,rw /;"""
    SH_READ_WRITE_REMOUNT_V06 = """busybox mount -o rw&&remount /"""
    SH_READ_WRITE_REMOUNT_V07 = """busybox mount -o rw;remount /"""
    SH_READ_WRITE_REMOUNT_V08 = """busybox mount --all -o remount,rw -t vfat"""
    SH_READ_WRITE_REMOUNT_V09 = """busybox mount --all -o remount,rw -t ext4"""
    SH_READ_WRITE_REMOUNT_V10 = """busybox mount --all -o remount,rw -t vfat1"""
    SH_READ_WRITE_REMOUNT_V11 = """mount -o remount,rw /"""
    SH_READ_WRITE_REMOUNT_V12 = """mount --all -o remount,rw -t vfat1"""
    SH_READ_WRITE_REMOUNT_V13 = """mount --all -o remount,rw -t ext4"""
    SH_READ_WRITE_REMOUNT_V14 = """mount -o remount,rw"""
    SH_READ_WRITE_REMOUNT_V15 = """mount -o remount,rw /;"""
    SH_READ_WRITE_REMOUNT_V16 = """mount -o rw&&remount /"""
    SH_READ_WRITE_REMOUNT_V17 = """mount -o rw;remount /"""
    SH_READ_WRITE_REMOUNT_V18 = """mount --all -o remount,rw -t vfat"""
    SH_READ_WRITE_REMOUNT_V19 = """mount --all -o remount,rw -t ext4"""
    SH_READ_WRITE_REMOUNT_V20 = """mount --all -o remount,rw -t vfat1"""
    SH_READ_WRITE_REMOUNT_V21 = """getprop --help >/dev/null;mount -o remount,rw /;"""
    SH_READ_WRITE_REMOUNT_V22 = r"""mount -v | grep "^/" | grep -v '\\(rw,' | grep '\\(ro' | awk '{print "mount -o rw,remount " $1 " " $3}' | tr '\n' '\0' | xargs -0 -n1 su -c"""
    SH_READ_WRITE_REMOUNT_V23 = r"""mount -v | grep "^/" | grep -v '\\(rw,' | grep '\\(ro' | awk '{print "mount -o rw,remount " $1 " " $3}' | su -c sh"""
    SH_READ_WRITE_REMOUNT_V24 = r"""mount -v | grep "^/" | grep -v '\\(rw,' | grep '\\(ro' | awk '{system("mount -o rw,remount " $1 " " $3)}' """
    SH_READ_WRITE_REMOUNT_V25 = r"""su -c 'mount -v | grep -E "^/" | awk '\''{print "mount -o rw,remount " $1 " " $3}'\''' | tr '\n' '\0' | xargs -0 -n1 su -c"""
    SH_READ_WRITE_REMOUNT_V26 = r"""mount -Ev | grep -Ev 'nodev' | grep -Ev '/proc' | grep -v '\\(rw,' | awk 'BEGIN{FS="([[:space:]]+(on|type)[[:space:]]+)|([[:space:]]+\\()"}{print "mount -o rw,remount " $1 " " $2}' | xargs -n5 | su -c"""
    SH_READ_WRITE_REMOUNT_V27 = r"""su -c 'mount -v | grep -E "^/" | awk '\''{print "mount -o rw,remount " $1 " " $3}'\''' | sh su -c"""
    SH_READ_WRITE_REMOUNT_V28 = r"""getprop --help >/dev/null;su -c 'mount -v | grep -E "^/" | awk '\''{print "mount -o rw,remount " $1 " " $3}'\''' | tr '\n' '\0' | xargs -0 -n1 | su -c sh"""
    SH_GET_BIOS_INFO = R"""{exe_path}dd if=/dev/mem bs=1k skip=768 count=256 2>/dev/null | {exe_path}strings -n 8"""
    SH_PRINTENV = "{exe_path}printenv"
    SH_FREEZE_PROC = "{exe_path}kill -19 {pid}"
    SH_UNFREEZE_PROC = "{exe_path}kill -18 {pid}"
    SH_SHOW_FRAGMENTS_ON_SCREEN_ENABLE = """{exe_path}setprop debug.layout true
    {exe_path}service call activity 1599295570"""
    SH_SHOW_FRAGMENTS_SCREEN_DISABLE = """{exe_path}setprop debug.layout false"""

@cython.final
cdef class Shelly:
    cdef:
        string* finish_cmd_to_write
        string* finish_cmd_to_write_stderr
        string* bin_finish_cmd
        string* su_exe
        string* cpp_new_line
        string* cpp_empty_string
        CySubProc p
        CommandGetter _c
        str system_bin
        bytes system_bin_as_binary

    def __dealloc__(self):
        del self.finish_cmd_to_write
        del self.finish_cmd_to_write_stderr
        del self.su_exe
        del self.bin_finish_cmd
        del self.cpp_new_line
        del self.cpp_empty_string

    def __init__(self,
                object shell_command,
                size_t buffer_size=40960,
                size_t stdout_max_len=40960,
                size_t stderr_max_len=40960,
                object exit_command=b"exit",
                bint print_stdout=False,
                bint print_stderr=False,
                str su_exe="su",
                str finish_cmd="HERE_IS_FINISH",
                str system_bin="",
                ):
        cdef:
                bytes self_su_exe = su_exe.encode("utf-8")
                bytes self_finish_cmd_to_write = f"""printf "\n%s\n" '{finish_cmd}'""".encode()
                bytes self_finish_cmd_to_write_stderr = (
            f"""printf "\n%s\n" '{finish_cmd}' >&2""".encode()
        )
        self.finish_cmd_to_write=new string(<string>self_finish_cmd_to_write)
        self.finish_cmd_to_write_stderr=new string(<string>self_finish_cmd_to_write_stderr)
        self.su_exe=new string(<string>self_su_exe)
        self.bin_finish_cmd=new string(convert_python_object_to_cpp_string(finish_cmd))
        self.cpp_new_line= new string(b"\n")
        self.cpp_empty_string= new string(b"")
        self.system_bin=system_bin
        self.system_bin_as_binary = system_bin.encode("utf-8")
        self.p = CySubProc(
                shell_command=shell_command,
                buffer_size=buffer_size,
                stdout_max_len=stdout_max_len,
                stderr_max_len=stderr_max_len,
                exit_command=exit_command,
                print_stdout=print_stdout,
                print_stderr=print_stderr,
                )
        self._c = CommandGetter()
        self.p.start_shell()
        self.p.stdin_write("echo STARTED")
        self.p.stdin_write("echo STARTED >&2")
        sleep_milliseconds(100)

    cpdef pair[string,string] write_and_wait(self, object line, int64_t timeout=10, bint strip_results=True):
        cdef:
            string formatted_line = convert_python_object_to_cpp_string(line)
            pair[string,string] result =self._write_and_wait(formatted_line=formatted_line, timeout=timeout, strip_results=strip_results)

        return result

    cpdef pair[vector[string],vector[string]] write_and_wait_list(self, object line, int64_t timeout=10, bint strip_results=True):
        cdef:
            string formatted_line = convert_python_object_to_cpp_string(line)
            pair[string,string] result =self._write_and_wait(formatted_line=formatted_line, timeout=timeout, strip_results=strip_results)
            pair[vector[string],vector[string]] resultpair=pair[vector[string],vector[string]]([],[])
        if not result.first.empty():
            resultpair.first=split_string(result.first,self.cpp_new_line[0])
        if not result.second.empty():
            resultpair.second=split_string(result.second,self.cpp_new_line[0])
        return resultpair


    cdef pair[string,string] _write_and_wait(self, string formatted_line, int64_t timeout=10, bint strip_results=True) nogil:
        cdef:
            string outstring_stdout
            string outstring_stderr
            size_t string_search_position=npos
            string tmpstring
            int64_t start_time
            int64_t end_time
            pair[string,string] resultpair = pair[string,string](self.cpp_empty_string[0],self.cpp_empty_string[0])
        outstring_stderr.reserve(256)
        outstring_stdout.reserve(8192)
        self.p.subproc.clear_stdout()
        self.p.subproc.clear_stderr()
        formatted_line.append(self.cpp_new_line[0])
        formatted_line.append(self.finish_cmd_to_write[0])
        formatted_line.append(self.cpp_new_line[0])
        formatted_line.append(self.finish_cmd_to_write_stderr[0])
        formatted_line.append(self.cpp_new_line[0])
        self.p.subproc.stdin_write(formatted_line)
        sleep_milliseconds(3)
        start_time = get_current_timestamp()
        end_time = start_time + timeout
        while npos==string_search_position and get_current_timestamp() < end_time:
            tmpstring=self.p.subproc.get_stderr()
            if tmpstring.empty():
                sleep_milliseconds(1)
                continue
            outstring_stderr.append(tmpstring)
            string_search_position=outstring_stderr.find(self.bin_finish_cmd[0])
        start_time = get_current_timestamp()
        end_time = start_time + timeout
        if (npos!=string_search_position):
            outstring_stderr.erase(outstring_stderr.begin()+string_search_position,outstring_stderr.end())
        string_search_position=npos
        while npos==string_search_position and get_current_timestamp() < end_time:
            tmpstring=self.p.subproc.get_stdout()
            if tmpstring.empty():
                sleep_milliseconds(1)
                continue
            outstring_stdout.append(tmpstring)

            string_search_position=outstring_stdout.find(self.bin_finish_cmd[0])
        if (npos!=string_search_position):
            outstring_stdout.erase(outstring_stdout.begin()+string_search_position,outstring_stdout.end())
        resultpair.first=outstring_stdout
        resultpair.second=outstring_stderr
        if strip_results:
            if not resultpair.first.empty():
                strip_spaces_inplace(resultpair.first)
            if not resultpair.second.empty():
                strip_spaces_inplace(resultpair.second)
        return resultpair

    def get_df_files_with_context_printf(self, object folders, int64_t max_depth=1, int64_t timeout=10):
        cdef:
            list ac=[]
            str str_result
        folders=convert_to_list(folders)
        for folder in folders:
            ac.append(
                self._c.SH_FIND_FILES_WITH_CONTEXT.format(
                    exe_path=self.system_bin, folder_path=folder, max_depth=max_depth
                )
            )
        str_result=(self.write_and_wait("\n".join(ac), timeout=timeout).first).decode("utf-8", "backslashreplace").strip()
        print(str_result)
        return pd.read_csv(
            StringIO(
                str_result
            ),
            encoding="utf-8",
            sep=",",
            index_col=False,
            encoding_errors="backslashreplace",
            on_bad_lines="warn",
            engine="python",
            na_filter=False,
            quoting=1,
            names=columns_files,
            dtype=dtypes_files,
        )
    def get_df_files_with_context_ls(
        self, object folders, int64_t max_depth=1, bint with_dates=True, int64_t timeout=10
    ):
        cdef:
            list ac=[]
            pair[vector[string],vector[string]] so_se_pair,so_se_pair2
            list[bytes] complete_command_list = []
            list[bytes] goodfiles = []
            bytes complete_command_list_bytes
            Py_ssize_t index,file_index
        folders=convert_to_list(folders)
        for folder in folders:
            ac.append(
                f'find {folder} -maxdepth {max_depth} -type f\nfind {folder} -maxdepth {max_depth} -type f -iname ".*"'
            )
        so_se_pair = self.write_and_wait_list("\n".join(ac).encode("utf-8"), timeout=timeout)
        for file_index in range(so_se_pair.first.size()):
            complete_command_list.append(
                self.system_bin_as_binary + b"ls -lZ " + bytes(so_se_pair.first[file_index]).rstrip()
            )
        complete_command_list_bytes = b"\n".join(complete_command_list)
        so_se_pair2 = self.write_and_wait_list(complete_command_list_bytes, timeout=timeout)

        for index in range((so_se_pair2.first.size())):
            linetmp = bytes(so_se_pair2.first[index]).strip().split(maxsplit=8)
            if len(linetmp) != 9:
                continue
            linetmp[6] = linetmp[6] + b" " + linetmp[7]
            del linetmp[7]
            goodfiles.append(b'"' + b'","'.join(linetmp) + b'"')

        df = pd.read_csv(
            StringIO(b"\n".join(goodfiles).decode("utf-8", "backslashreplace")),
            encoding="utf-8",
            sep=",",
            index_col=False,
            encoding_errors="backslashreplace",
            on_bad_lines="warn",
            engine="python",
            na_filter=False,
            quoting=1,
            names=[
                "aa_Permissions",
                "aa_Links",
                "aa_Owner",
                "aa_Group",
                "aa_SELinux",
                "aa_Size",
                "aa_Date",
                "aa_Path",
            ],
        )
        if with_dates:
            df.loc[:, "aa_date_time"] = pd.to_datetime(df.aa_Date, errors="coerce")
            print(df)
            df.loc[:, "aa_tstamp"] = df["aa_date_time"].apply(
                lambda x: x.value if not pd.isna(x) else pd.NA
            )
        df.loc[:, "aa_Permissions_as_int"] = df.aa_Permissions.apply(
            calculate_chmod
        )
        return df
    def get_df_build_props(self, int64_t timeout=10):
        cdef:
            pair[vector[string],vector[string]] so_se_pair,so_se_pair2
            list complete_command_list = []
            Py_ssize_t li,file_index
            str file_stripped

        so_se_pair = self.write_and_wait_list(
            self._c.SH_FIND_PROP_FILES.format(exe_path=self.system_bin),
            timeout=timeout
        )
        for file_index in range(so_se_pair.first.size()):
            file_stripped = bytes(so_se_pair.first[file_index]).strip().decode("utf-8", "backslashreplace")
            so_se_pair2 = self.write_and_wait_list(f"{self.system_bin}cat " + file_stripped,timeout=timeout)
            for li in range(so_se_pair2.first.size()):
                complete_command_list.append((file_stripped, li, bytes(so_se_pair2.first[li])))
        return pd_DataFrame(
            complete_command_list, columns=["aa_file", "aa_line", "aa_line_content"]
        )

    def get_df_files_with_ending(self, object folders, object endings, int64_t max_depth=10000, int64_t timeout=10):
        cdef:
            list ac = []
            str wholecmd
            pair[vector[string],vector[string]] so_se_pair
        folders=convert_to_list(folders)
        endings=convert_to_list(endings)
        for folder in folders:
            for ending in endings:
                ac.append(
                    self._c.SH_FIND_FILES_WITH_ENDING.format(
                        exe_path=self.system_bin,
                        folder_path=folder,
                        max_depth=max_depth,
                        ending=ending,
                    )
                )
        wholecmd = "\n".join(ac)
        so_se_pair = self.write_and_wait_list(wholecmd.encode("utf-8"), timeout=timeout)
        return pd_DataFrame(
            (q.decode("utf-8", "backslashreplace").strip() for q in list(so_se_pair.first)),
            columns=["aa_file"],
        )

    def get_df_top_procs(self, timeout=1000):
        return pd.read_csv(
            StringIO(
                (
                    b"\n".join(
                        b'"' + b'","'.join(q) + b'"'
                        for x in list(
                            self.write_and_wait_list(
                                f"{self.system_bin}top -b -n1", timeout=timeout
                            ).first
                        )
                        if proc_match(x)
                        and len(q := x.strip().split(maxsplit=11)) == 12
                    )
                ).decode("utf-8", "backslashreplace")
            ),
            encoding="utf-8",
            sep=",",
            index_col=False,
            encoding_errors="backslashreplace",
            on_bad_lines="warn",
            engine="python",
            na_filter=False,
            quoting=1,
            names=[
                "aa_PID",
                "aa_USER",
                "aa_PR",
                "aa_NI",
                "aa_VIRT",
                "aa_RES",
                "aa_SHR",
                "aa_CPU",
                "aa_MEM",
                "aa_TIME",
                "aa_ARGS",
            ],
        )
    def get_df_users(self, start=0, end=2000, timeout=10000):
        cdef:
            pair[vector[string],vector[string]] so_se_pair
            list[list] usergroup = []
            list ss
            Py_ssize_t s_index
        so_se_pair = self.write_and_wait_list(
            f'for q in $({self.system_bin}seq {start} {end}); do {self.system_bin}id "$q";done'
        )
        for s_index in range(so_se_pair.first.size()):
            ss = bytes(so_se_pair.first[s_index]).decode("utf-8", "backslashreplace").split()
            if len(ss) >= 2:
                usergroup.append([])
            else:
                continue
            for sss in ss:
                item = sss.split("=")
                if len(item) == 2:
                    usergroup[len(usergroup)-1].append(tuple(item))
            usergroup[len(usergroup)-1] = dict(usergroup[len(usergroup)-1])
        return pd_DataFrame(usergroup)

    def get_df_groups_of_user(self, start=0, end=2000, timeout=10000):
        cdef:
            pair[vector[string],vector[string]] so_se_pair
            list ss
            Py_ssize_t s_index
            dict usergroupdict = {}
        so_se_pair = self.write_and_wait_list(
            f'for q in $({self.system_bin}seq {start} {end}); do u="$({self.system_bin}groups "$q")" && echo "$u||||$q" ;done'
        )

        for s_index in range(so_se_pair.first.size()):
            ss = (bytes(so_se_pair.first[s_index]).decode("utf-8", "backslashreplace")).split("||||")
            if len(ss) != 2:
                continue
            usergroupdict[int(ss[1])] = ss[0]
        return (
            pd.Series(usergroupdict)
            .to_frame()
            .reset_index()
            .rename(columns={"index": "aa_id", 0: "aa_groups"})
        )
    def get_df_netstat_tlnp(self, timeout=100):
        return pd.read_csv(
            StringIO(
                "\n".join(
                    (
                        '"' + '","'.join(h) + '"'
                        for h in (
                            z[:6] + z[6].split("/", maxsplit=1)
                            for z in (
                                y.decode("utf-8", "backslashreplace")
                                .split(maxsplit=6)
                                for y in self.write_and_wait_list(
                                    f"{self.system_bin}netstat -tlnp", timeout=timeout
                                ).first
                                if regex_netstat(y)
                            )
                            if len(z) == 7
                        )
                        if len(h) == 8
                    )
                )
            ),
            encoding="utf-8",
            sep=",",
            index_col=False,
            encoding_errors="backslashreplace",
            on_bad_lines="warn",
            engine="python",
            na_filter=False,
            quoting=1,
            names=[
                "aa_Proto",
                "aa_RecvQ",
                "aa_SendQ",
                "aa_LocalAddress",
                "aa_ForeignAddress",
                "aa_State",
                "aa_PID",
                "aa_ProgramName",
            ],
        )

    cpdef sh_save_sed_replace(self, file_path, string2replace, replacement, timeout=1000):
        return self._write_and_wait(
            self._c.SH_SAVE_SED_REPLACE.format(
                exe_path=self.system_bin,
                file_path=file_path,
                string2replace=string2replace,
                replacement=replacement,
            ),
            timeout=timeout,
        )

    cpdef sh_svc_enable_wifi(self, timeout=10):
        return self._write_and_wait(
            self._c.SH_SVC_ENABLE_WIFI.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_svc_disable_wifi(self, timeout=10):
        return self._write_and_wait(
            self._c.SH_SVC_DISABLE_WIFI.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )
    cpdef sh_trim_cache(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_TRIM_CACHES.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_force_open_app(self, package_name, sleep_time, timeout=3):
        return self.write_and_wait(
            self._c.SH_FORCE_OPEN_APP.format(
                exe_path=self.system_bin,
                package_name=package_name,
                sleep_time=sleep_time,
            ),
            timeout=timeout,
        )
    cpdef sh_get_main_activity(self, package_name, timeout=3):
        return self.write_and_wait(
            self._c.SH_GET_MAIN_ACTIVITY.format(
                exe_path=self.system_bin,
                package_name=package_name,
            ),
            timeout=timeout,
        )

    cpdef sh_svc_power_shutdown(self, timeout=3):
        return self.write_and_wait(
            self._c.SH_SVC_POWER_SHUT_DOWN.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_svc_power_reboot(self, timeout=3):
        return self.write_and_wait(
            self._c.SH_SVC_POWER_REBOOT.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )
    cpdef sh_dumpsys_dropbox(self, timeout=3):
        return self.write_and_wait(
            self._c.SH_DUMPSYS_DROPBOX.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_set_new_launcher(self, package_name, timeout=3):
        return self.write_and_wait(
            self._c.SH_SET_NEW_LAUNCHER.format(
                exe_path=self.system_bin,
                package_name=package_name,
            ),
            timeout=timeout,
        )
    cpdef sh_tar_folder(self, src, dst, timeout=1000000):
        return self.write_and_wait(
            self._c.SH_TAR_FOLDER.format(
                exe_path=self.system_bin,
                dst=dst,
                src=src,
            ),
            timeout=timeout,
        )

    cpdef sh_extract_tar_zip(self, src_file, dst_folder, timeout=1000000):
        return self.write_and_wait(
            self._c.SH_EXTRACT_FILES.replace("COMPRESSED_ARCHIVE", src_file).replace(
                "FOLDER_TO_EXTRACT", dst_folder
            ),
            timeout=timeout,
        )
    cpdef sh_get_user_rotation(self, timeout=10):
        return int(
            bytes(
                self.write_and_wait(
                    self._c.SH_GET_USER_ROTATION.format(
                        exe_path=self.system_bin,
                    ),
                    timeout=timeout,
                ).first
            ).strip()
        )


    cpdef sh_copy_dir_recursive(self, src, dst, timeout=1000):
        return self.write_and_wait(
            self._c.SH_COPY_DIR_RECURSIVE.format(
                exe_path=self.system_bin,
                src=src,
                dst=dst,
            ),
            timeout=timeout,
        )

    cpdef sh_backup_file(self, src, timeout=1000):
        return self.write_and_wait(
            self._c.SH_BACKUP_FILE.format(
                exe_path=self.system_bin,
                src=src,
            ),
            timeout=timeout,
        )

    cpdef sh_remove_folder(self, folder, timeout=1000):
        return self.write_and_wait(
            self._c.SH_REMOVE_FOLDER.format(
                exe_path=self.system_bin,
                folder=folder,
            ),
            timeout=timeout,
        )
    cpdef sh_get_pid_of_shell(self, int64_t timeout=3):
        return int(
            self.write_and_wait(
                self._c.SH_GET_PID_OF_SHELL,
                timeout=timeout,
            ).first
        )
    cpdef sh_whoami(self, int64_t timeout=10):
        return self.write_and_wait(
            self._c.SH_WHOAMI.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        ).first

    cpdef su(self):
        self.p.subproc.stdin_write(self.su_exe[0])

    cpdef sh_dumpsys_package(self, package, timeout=1000, bint convert_to_dict=True):
        cdef:
            bytes so
            list[bytes] byteslist
        so = self.write_and_wait(
            self._c.SH_DUMPSYS_PACKAGE.format(
                exe_path=self.system_bin,
                package=package,
            ),
            timeout=timeout,
        ).first
        byteslist=so.splitlines(keepends=True)
        return _dumpsys_splitter_to_dict(byteslist,convert_to_dict=convert_to_dict)

    cpdef sh_get_all_wanted_permissions_from_package(self, package, timeout=1000):
        cdef:
            set all_permissions
        dd1 = self.sh_dumpsys_package(package,timeout=timeout,convert_to_dict=False)
        declared_permissions = list(dd1.nested_key_search("declared permissions:"))
        requested_permissions = list(dd1.nested_key_search("requested permissions:"))
        install_permissions = list(dd1.nested_key_search("install permissions:"))
        all_permissions = set()
        for permissions in [
            declared_permissions,
            requested_permissions,
            install_permissions,
        ]:
            for install_permission in permissions:
                for ipi in install_permission[len(install_permission)-1]:
                    all_permissions.add(ipi.split(":")[0].strip())
        return sorted(all_permissions)

    cpdef sh_grant_permission(self, package, permission, timeout=10):
        return self.write_and_wait(
            self._c.SH_GRANT_PERMISSION.format(
                exe_path=self.system_bin,
                package=package,
                permission=permission,
            ),
            timeout=timeout,
        )

    cpdef sh_grant_all_wanted_permissions(self, package, timeout=1000):
        cdef:
            list allcmds = []
        permissions = self.sh_get_all_wanted_permissions_from_package(package, timeout=timeout)
        for permission in permissions:
            allcmds.append(
                self._c.SH_GRANT_PERMISSION.format(
                    exe_path=self.system_bin,
                    package=package,
                    permission=permission,
                )
            )
        return self.write_and_wait("\n".join(allcmds), timeout=timeout)

    cpdef sh_revoke_all_wanted_permissions(self, package, timeout=1000):
        cdef:
            list allcmds = []
        permissions = self.sh_get_all_wanted_permissions_from_package(package, timeout=timeout)
        for permission in permissions:
            allcmds.append(
                self._c.SH_REVOKE_PERMISSION.format(
                    exe_path=self.system_bin,
                    package=package,
                    permission=permission,
                )
            )
        return self.write_and_wait("\n".join(allcmds), timeout=timeout)

    cpdef sh_parse_whole_dumpsys_to_dict(self, timeout=100,convert_to_dict=False):
        cdef:
            bytes so3
            dict wholedict = {}
            list[bytes] so
            list[str] so2
        so = self.write_and_wait_list(f"{self.system_bin}dumpsys -l", timeout=timeout).first
        so2 = [
            f"{self.system_bin}dumpsys " + x.decode("utf-8").strip()
            for x in so
            if len(x) > 1 and x[0] == 32
        ]
        for cmd in so2:
            so3 = self.write_and_wait(cmd, timeout=timeout).first
            wholedict[cmd.split()[1]] = _dumpsys_splitter_to_dict(so3.splitlines(keepends=True),convert_to_dict=convert_to_dict)
        return wholedict

    cpdef sh_parse_dumpsys_to_dict(self, subcmd, timeout=100,convert_to_dict=False):
        cdef:
            bytes so3
        so3=self.write_and_wait(f"{self.system_bin}dumpsys {subcmd}", timeout=timeout).first
        return _dumpsys_splitter_to_dict(so3.splitlines(keepends=True),convert_to_dict=convert_to_dict)


    cpdef sh_get_available_keyboards(self, timeout=10):
        return [
            x.decode("utf-8", "backslashreplace").strip()
            for x in self.write_and_wait_list(
                self._c.SH_GET_AVAIABLE_KEYBOARDS.format(
                    exe_path=self.system_bin,
                ),
                timeout=timeout,
            ).first
        ]

    @cython.boundscheck
    cpdef sh_get_active_keyboard(self, timeout=10):
        return [
            x.decode("utf-8", "backslashreplace").strip()
            for x in self.write_and_wait_list(
                self._c.SH_GET_ACTIVE_KEYBOARD.format(
                    exe_path=self.system_bin,
                ),
                timeout=timeout,
            ).first
        ][0]

    cpdef sh_get_all_information_about_all_keyboards(self, timeout=10,convert_to_dict=False):
        return _dumpsys_splitter_to_dict(
            bytes(self.write_and_wait(
                self._c.SH_GET_ALL_KEYBOARDS_INFORMATION.format(
                    exe_path=self.system_bin,
                ),
                timeout=timeout,
            ).first).splitlines(keepends=True), convert_to_dict=convert_to_dict
        )

    cpdef sh_enable_keyboard(self, keyboard, timeout=10):
        return self.write_and_wait(
            self._c.SH_ENABLE_KEYBOARD.format(
                exe_path=self.system_bin,
                keyboard=keyboard,
            ),
            timeout=timeout,
        )

    cpdef sh_disable_keyboard(self, keyboard, timeout=10):
        return self.write_and_wait(
            self._c.SH_DISABLE_KEYBOARD.format(
                exe_path=self.system_bin,
                keyboard=keyboard,
            ),
            timeout=timeout,
        )

    cpdef sh_is_keyboard_shown(self, timeout=10):
        cdef:
            bytes stdout
        stdout = (
            self.write_and_wait(
                self._c.SH_IS_KEYBOARD_SHOWN.format(
                    exe_path=self.system_bin,
                ),
                timeout=timeout,
            ).first
        )
        return b"mInputShown=true" in stdout

    cpdef sh_set_keyboard(self, keyboard, timeout=10):
        return self.write_and_wait(
            self._c.SH_SET_KEYBOARD.format(
                exe_path=self.system_bin,
                keyboard=keyboard,
            ),
            timeout=timeout,
        )

    cpdef sh_show_touches(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_SHOW_TOUCHES.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_dont_show_touches(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_SHOW_TOUCHES_NOT.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_show_pointer_location(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_SHOW_POINTER_LOCATION.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_dont_show_pointer_location(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_SHOW_POINTER_LOCATION_NOT.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_input_swipe(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_SWIPE.format(
                exe_path=self.system_bin,
                x1=int(x1),
                y1=int(y1),
                x2=int(x2),
                y2=int(y2),
                duration=int(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_tap(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TAP.format(
                exe_path=self.system_bin,
                x=int(x),
                y=int(y),
            ),
            timeout=timeout,
        )

    cpdef df_apply_md5_code_of_files(self, df, column_name, timeout=1000000):
        df.loc[:, str(column_name) + "_md5"] = (
            self.system_bin + "md5sum -b '" + df[column_name].str.replace("'", "'\\''",regex=False) + "'"
        )
        df.loc[:, str(column_name) + "_md5"] = [
            x.decode("utf-8", "backslashreplace").strip()
            for x in self.write_and_wait_list(
                "\n".join(df.loc[:, str(column_name) + "_md5"].to_list()),
                timeout=timeout,
            ).first
        ][: len(df)]

    cpdef sh_clear_file_content(self, file_path, timeout=10):
        return self.write_and_wait(
            self._c.SH_CLEAR_FILE_CONTENT.format(
                exe_path=self.system_bin,
                file_path=file_path,
            ),
            timeout=timeout,
        )

    cpdef sh_makedirs(self, folder, timeout=10):
        return self.write_and_wait(
            self._c.SH_MAKEDIRS.format(
                exe_path=self.system_bin,
                folder=folder,
            ),
            timeout=timeout,
        )

    cpdef sh_touch(self, file_path, timeout=10):
        return self.write_and_wait(
            self._c.SH_TOUCH.format(
                exe_path=self.system_bin,
                file_path=file_path,
            ),
            timeout=timeout,
        )

    cpdef sh_mv(self, src, dst, timeout=10):
        return self.write_and_wait(
            self._c.SH_MV.format(
                exe_path=self.system_bin,
                src=src,
                dst=dst,
            ),
            timeout=timeout,
        )

    def get_df_mounts(self, timeout=100):
        return pd_DataFrame(
            [
                h
                for h in [
                    z[:2] + z[2].split(maxsplit=1)
                    for z in [
                        y
                        for y in [
                            re.split(
                                r"\s+\b(?:on|type)\b\s+",
                                x.strip().decode("utf-8", "backslashreplace"),
                            )
                            for x in self.write_and_wait_list(f"{self.system_bin}mount -v",timeout=timeout).first
                        ]
                        if len(y) == 3
                    ]
                ]
                if len(h) == 4
            ],
            columns=["aa_identifier", "aa_mountpoint", "aa_type", "aa_options"],
        )
    cpdef sh_open_accessibility_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_ACCESSIBILITY_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_advanced_memory_protection_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_ADVANCED_MEMORY_PROTECTION_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_airplane_mode_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_AIRPLANE_MODE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_all_apps_notification_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_ALL_APPS_NOTIFICATION_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_apn_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_APN_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_application_details_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_APPLICATION_DETAILS_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_application_development_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_APPLICATION_DEVELOPMENT_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_application_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_APPLICATION_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_app_locale_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_APP_LOCALE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_app_notification_bubble_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_APP_NOTIFICATION_BUBBLE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_app_notification_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_APP_NOTIFICATION_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_app_open_by_default_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_APP_OPEN_BY_DEFAULT_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_app_search_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_APP_SEARCH_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_app_usage_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_APP_USAGE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_automatic_zen_rule_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_AUTOMATIC_ZEN_RULE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_auto_rotate_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_AUTO_ROTATE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_battery_saver_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_BATTERY_SAVER_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_bluetooth_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_BLUETOOTH_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_captioning_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_CAPTIONING_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_cast_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_CAST_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_channel_notification_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_CHANNEL_NOTIFICATION_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_condition_provider_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_CONDITION_PROVIDER_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_data_roaming_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_DATA_ROAMING_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_data_usage_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_DATA_USAGE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_date_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_DATE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_device_info_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_DEVICE_INFO_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_display_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_DISPLAY_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_dream_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_DREAM_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_hard_keyboard_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_HARD_KEYBOARD_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_home_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_HOME_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_ignore_background_data_restrictions_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_IGNORE_BACKGROUND_DATA_RESTRICTIONS_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_ignore_battery_optimization_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_IGNORE_BATTERY_OPTIMIZATION_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_input_method_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_INPUT_METHOD_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_input_method_subtype_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_INPUT_METHOD_SUBTYPE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_internal_storage_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_INTERNAL_STORAGE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_locale_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_LOCALE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_location_source_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_LOCATION_SOURCE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_manage_all_applications_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_MANAGE_ALL_APPLICATIONS_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_manage_all_sim_profiles_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_MANAGE_ALL_SIM_PROFILES_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_manage_applications_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_MANAGE_APPLICATIONS_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_manage_default_apps_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_MANAGE_DEFAULT_APPS_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_manage_supervisor_restricted_setting(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_MANAGE_SUPERVISOR_RESTRICTED_SETTING.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_manage_write_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_MANAGE_WRITE_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_memory_card_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_MEMORY_CARD_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_network_operator_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_NETWORK_OPERATOR_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_nfcsharing_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_NFCSHARING_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_nfc_payment_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_NFC_PAYMENT_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_nfc_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_NFC_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_night_display_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_NIGHT_DISPLAY_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_notification_assistant_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_NOTIFICATION_ASSISTANT_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_notification_listener_detail_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_NOTIFICATION_LISTENER_DETAIL_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_notification_listener_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_NOTIFICATION_LISTENER_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_notification_policy_access_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_NOTIFICATION_POLICY_ACCESS_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_print_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_PRINT_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_privacy_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_PRIVACY_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_quick_access_wallet_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_QUICK_ACCESS_WALLET_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_quick_launch_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_QUICK_LAUNCH_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_regional_preferences_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_REGIONAL_PREFERENCES_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_satellite_setting(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_SATELLITE_SETTING.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_search_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_SEARCH_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_security_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_SECURITY_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_sound_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_SOUND_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_storage_volume_access_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_STORAGE_VOLUME_ACCESS_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_sync_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_SYNC_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_usage_access_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_USAGE_ACCESS_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_user_dictionary_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_USER_DICTIONARY_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_voice_input_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_VOICE_INPUT_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_vpn_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_VPN_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_vr_listener_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_VR_LISTENER_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_webview_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_WEBVIEW_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_wifi_ip_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_WIFI_IP_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_wifi_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_WIFI_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_wireless_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_WIRELESS_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_zen_mode_priority_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_ZEN_MODE_PRIORITY_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_open_developer_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_DEVELOPER_SETTINGS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_rescan_media_folder(self, folder, timeout=10):
        return self.write_and_wait(
            self._c.SH_RESCAN_MEDIA_FOLDER.format(
                exe_path=self.system_bin,
                folder=folder,
            ),
            timeout=timeout,
        )

    cpdef sh_rescan_media_file(self, file_path, timeout=10):
        return self.write_and_wait(
            self._c.SH_RESCAN_MEDIA_FILE.format(
                exe_path=self.system_bin,
                file_path=file_path,
            ),
            timeout=timeout,
        )
    cpdef sh_dump_process_memory_to_sdcard(self, pid, timeout=100000):
        return self.write_and_wait(
            self._c.SH_DUMP_PROCESS_MEMORY_TO_SDCARD.replace("PID2OBSERVE", str(pid)),
            timeout=timeout,
        )

    cpdef sh_pm_clear(self, package, timeout=10):
        return self.write_and_wait(
            self._c.SH_PM_CLEAR.format(
                exe_path=self.system_bin,
                package=package,
            ),
            timeout=timeout,
        )
    def get_df_ps_el(self, timeout=1000):
        df = pd.read_csv(
            StringIO(
                (
                    b"\n".join(
                        (
                            b'"' + b'","'.join(y) + b'"'
                            for y in (
                                x.strip().split(maxsplit=13)
                                for x in self.write_and_wait_list(
                                    f"""{self.system_bin}ps -el""",timeout=timeout
                                ).first
                            )
                            if len(y) == 14
                        )
                    )
                ).decode("utf-8", "backslashreplace")
            ),
            encoding="utf-8",
            sep=",",
            index_col=False,
            encoding_errors="backslashreplace",
            on_bad_lines="warn",
            engine="python",
            na_filter=False,
            quoting=1,
        )
        df.columns = ["aa_" + x for x in df.columns]
        return df
    cpdef sh_wm_change_size(self, width, height, timeout=10):
        return self.write_and_wait(
            self._c.SH_CHANGE_WM_SIZE.format(
                exe_path=self.system_bin,
                width=width,
                height=height,
            ),
            timeout=timeout,
        )

    cpdef sh_wm_reset_size(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_WM_RESET_SIZE.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_wm_get_density(self, timeout=10):
        cdef:
            bytes resu
        resu = (
            self.write_and_wait(
                self._c.SH_GET_WM_DENSITY.format(
                    exe_path=self.system_bin,
                ),
                timeout=timeout,
            ).first
        )
        resu2 = resu.strip().split()
        return int(resu2[len(resu2) - 1])

    cpdef sh_wm_change_density(self, density, timeout=10):
        return self.write_and_wait(
            self._c.SH_CHANGE_WM_DENSITY.format(
                exe_path=self.system_bin,
                density=density,
            ),
            timeout=timeout,
        )

    cpdef sh_wm_reset_density(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_WM_RESET_DENSITY.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_am_screen_compat_on(self, package, timeout=10):
        return self.write_and_wait(
            self._c.SH_AM_SCREEN_COMPAT_ON.format(
                exe_path=self.system_bin,
                package=package,
            ),
            timeout=timeout,
        )

    cpdef sh_am_screen_compat_off(self, package, timeout=10):
        return self.write_and_wait(
            self._c.SH_AM_SCREEN_COMPAT_OFF.format(
                exe_path=self.system_bin,
                package=package,
            ),
            timeout=timeout,
        )

    cpdef sh_enable_notifications(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_ENABLE_NOTIFICATIONS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_disable_notifications(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_DISABLE_NOTIFICATIONS.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )

    cpdef sh_still_image_camera(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_STILL_IMAGE_CAMERA.format(
                exe_path=self.system_bin,
            ),
            timeout=timeout,
        )
    cpdef sh_disable_network_interface(self, nic, timeout=10):
        return self.write_and_wait(
            self._c.SH_DISABLE_NETWORK_INTERFACE.format(
                exe_path=self.system_bin,
                nic=nic,
            ),
            timeout=timeout,
        )

    cpdef sh_enable_network_interface(self, nic, timeout=10):
        return self.write_and_wait(
            self._c.SH_ENABLE_NETWORK_INTERFACE.format(
                exe_path=self.system_bin,
                nic=nic,
            ),
            timeout=timeout,
        )

    cpdef sh_get_linux_version(self, timeout=10):
        return (
            (
                self.write_and_wait(
                    self._c.SH_GET_LINUX_VERSION.format(
                        exe_path=self.system_bin,
                    ),
                    timeout=timeout,
                ).first
            )
            .decode("utf-8", "backslashreplace")
            .strip()
        )

    def get_df_packages(self, timeout=10):
        df2 = pd_DataFrame(
            (
                h
                for h in (
                    regex_package_start("", y[0]).rsplit("=", maxsplit=1) + y[1:]
                    for y in (
                        x.strip().decode().rsplit(maxsplit=2)
                        for x in self.write_and_wait_list(
                            f"""{self.system_bin}pm list packages -f -i -U -s""",
                            timeout=timeout,
                        ).first
                    )
                    if len(y) == 3
                )
                if len(h) == 4
            ),
            columns=["aa_apk", "aa_package", "aa_installer", "aa_uid"],
        ).assign(
            aa_3rd_party=False,
        )
        try:
            df1 = pd_DataFrame(
                (
                    h
                    for h in (
                        regex_package_start("", y[0]).rsplit("=", maxsplit=1)
                        + y[1:]
                        for y in (
                            x.strip().decode().rsplit(maxsplit=2)
                            for x in self.write_and_wait_list(
                                f"""{self.system_bin}pm list packages -f -i -U -3""",
                                timeout=timeout,
                            ).first
                        )
                        if len(y) == 3
                    )
                    if len(h) == 4
                ),
                columns=["aa_apk", "aa_package", "aa_installer", "aa_uid"],
            ).assign(
                aa_3rd_party=True,
            )
            return pd.concat([df2, df1], ignore_index=True)
        except Exception:
            return df2

    def get_df_netstat_connections_of_apps(self, resolve_names=True, timeout=10):
        cdef:
            list[bytes] so
        if resolve_names:
            so = self.write_and_wait_list(
                f"""{self.system_bin}netstat -W -p -u -t -l -e""",
                timeout=timeout,
            ).first
        else:
            so = self.write_and_wait_list(
                f"""{self.system_bin}netstat -n -W -p -u -t -l -e""",
                timeout=timeout,
            ).first
        return pd.read_csv(
            StringIO(
                (
                    b"\n".join(
                        (
                            b'"' + b'","'.join(z) + b'"'
                            for z in (
                                y[:8] + y[8].split(b"/", maxsplit=1)
                                for y in (x.strip().split(maxsplit=8) for x in so)
                                if len(y) == 9 and y[1].isdigit() and y[2].isdigit()
                            )
                        )
                    )
                ).decode("utf-8", "backslashreplace")
            ),
            encoding="utf-8",
            sep=",",
            index_col=False,
            encoding_errors="backslashreplace",
            on_bad_lines="warn",
            engine="python",
            na_filter=False,
            quoting=1,
            names=[
                "aa_proto",
                "aa_recv_q",
                "aa_send_q",
                "aa_local_addr",
                "aa_foreign_addr",
                "aa_state",
                "aa_user",
                "aa_inode",
                "aa_pid",
                "aa_program",
            ],
        )
    cpdef sh_expand_notifications(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_EXPAND_NOTIFICATIONS % (self.system_bin,),
            timeout=timeout,
        )

    cpdef sh_expand_settings(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_EXPAND_SETTINGS % (self.system_bin,),
            timeout=timeout,
        )

    cpdef sh_list_permission_groups(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_LIST_PERMISSION_GROUPS % (self.system_bin,),
            timeout=timeout,
        )

    cpdef sh_input_dpad_tap(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_DPAD_TAP % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_keyboard_tap(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_KEYBOARD_TAP % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_mouse_tap(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_MOUSE_TAP % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_touchpad_tap(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHPAD_TAP % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_gamepad_tap(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_GAMEPAD_TAP % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_touchnavigation_tap(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHNAVIGATION_TAP
            % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_joystick_tap(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_JOYSTICK_TAP % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_touchscreen_tap(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHSCREEN_TAP
            % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_stylus_tap(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_STYLUS_TAP % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_trackball_tap(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TRACKBALL_TAP
            % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_dpad_swipe(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_DPAD_SWIPE
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_dpad_draganddrop(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_DPAD_DRAGANDDROP
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_dpad_roll(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_DPAD_ROLL % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_keyboard_swipe(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_KEYBOARD_SWIPE
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_keyboard_draganddrop(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_KEYBOARD_DRAGANDDROP
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_keyboard_roll(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_KEYBOARD_ROLL
            % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_mouse_swipe(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_MOUSE_SWIPE
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_mouse_draganddrop(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_MOUSE_DRAGANDDROP
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_mouse_roll(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_MOUSE_ROLL % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_touchpad_swipe(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHPAD_SWIPE
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_touchpad_draganddrop(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHPAD_DRAGANDDROP
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_touchpad_roll(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHPAD_ROLL
            % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_gamepad_swipe(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_GAMEPAD_SWIPE
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_gamepad_draganddrop(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_GAMEPAD_DRAGANDDROP
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_gamepad_roll(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_GAMEPAD_ROLL % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_touchnavigation_swipe(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHNAVIGATION_SWIPE
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_touchnavigation_draganddrop(
        self, x1, y1, x2, y2, duration, timeout=10
    ):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHNAVIGATION_DRAGANDDROP
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_touchnavigation_roll(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHNAVIGATION_ROLL
            % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_joystick_swipe(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_JOYSTICK_SWIPE
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_joystick_draganddrop(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_JOYSTICK_DRAGANDDROP
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_joystick_roll(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_JOYSTICK_ROLL
            % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_touchscreen_swipe(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHSCREEN_SWIPE
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_touchscreen_draganddrop(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHSCREEN_DRAGANDDROP
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_touchscreen_roll(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TOUCHSCREEN_ROLL
            % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_stylus_swipe(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_STYLUS_SWIPE
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_stylus_draganddrop(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_STYLUS_DRAGANDDROP
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_stylus_roll(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_STYLUS_ROLL % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_input_trackball_swipe(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TRACKBALL_SWIPE
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_trackball_draganddrop(self, x1, y1, x2, y2, duration, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TRACKBALL_DRAGANDDROP
            % (
                self.system_bin,
                tointstr(x1),
                tointstr(y1),
                tointstr(x2),
                tointstr(y2),
                tointstr(duration),
            ),
            timeout=timeout,
        )

    cpdef sh_input_trackball_roll(self, x, y, timeout=10):
        return self.write_and_wait(
            self._c.SH_INPUT_TRACKBALL_ROLL
            % (self.system_bin, tointstr(x), tointstr(y)),
            timeout=timeout,
        )

    cpdef sh_open_url(self, url, timeout=10):
        return self.write_and_wait(
            self._c.SH_OPEN_URL.format(exe_path=self.system_bin, url=url),
            timeout=timeout,
        )

    cpdef sh_get_bios_information(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_GET_BIOS_INFO.format(exe_path=self.system_bin),
            timeout=timeout,
        )
    cpdef sh_printenv(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_PRINTENV.format(exe_path=self.system_bin),
            timeout=timeout,
        )

    cpdef sh_freeze_proc(self, pid, timeout=10):
        return self.write_and_wait(
            self._c.SH_FREEZE_PROC.format(exe_path=self.system_bin, pid=pid),
            timeout=timeout,
        )

    cpdef sh_unfreeze_proc(self, pid, timeout=10):
        return self.write_and_wait(
            self._c.SH_UNFREEZE_PROC.format(exe_path=self.system_bin, pid=pid),
            timeout=timeout,
        )

    cpdef sh_show_fragments_on_screen_enable(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_SHOW_FRAGMENTS_ON_SCREEN_ENABLE.format(exe_path=self.system_bin),
            timeout=timeout,
        )

    cpdef sh_show_fragments_on_screen_disable(self, timeout=10):
        return self.write_and_wait(
            self._c.SH_SHOW_FRAGMENTS_SCREEN_DISABLE.format(exe_path=self.system_bin),
            timeout=timeout,
        )

    cpdef sh_read_write_remount(self, methods, timeout=100):
        cdef:
            list results = []
            dict remount_dict = {
            1: self._c.SH_READ_WRITE_REMOUNT_V01,
            2: self._c.SH_READ_WRITE_REMOUNT_V02,
            3: self._c.SH_READ_WRITE_REMOUNT_V03,
            4: self._c.SH_READ_WRITE_REMOUNT_V04,
            5: self._c.SH_READ_WRITE_REMOUNT_V05,
            6: self._c.SH_READ_WRITE_REMOUNT_V06,
            7: self._c.SH_READ_WRITE_REMOUNT_V07,
            8: self._c.SH_READ_WRITE_REMOUNT_V08,
            9: self._c.SH_READ_WRITE_REMOUNT_V09,
            10: self._c.SH_READ_WRITE_REMOUNT_V10,
            11: self._c.SH_READ_WRITE_REMOUNT_V11,
            12: self._c.SH_READ_WRITE_REMOUNT_V12,
            13: self._c.SH_READ_WRITE_REMOUNT_V13,
            14: self._c.SH_READ_WRITE_REMOUNT_V14,
            15: self._c.SH_READ_WRITE_REMOUNT_V15,
            16: self._c.SH_READ_WRITE_REMOUNT_V16,
            17: self._c.SH_READ_WRITE_REMOUNT_V17,
            18: self._c.SH_READ_WRITE_REMOUNT_V18,
            19: self._c.SH_READ_WRITE_REMOUNT_V19,
            20: self._c.SH_READ_WRITE_REMOUNT_V20,
            21: self._c.SH_READ_WRITE_REMOUNT_V21,
            22: self._c.SH_READ_WRITE_REMOUNT_V22,
            23: self._c.SH_READ_WRITE_REMOUNT_V23,
            24: self._c.SH_READ_WRITE_REMOUNT_V24,
            25: self._c.SH_READ_WRITE_REMOUNT_V25,
            26: self._c.SH_READ_WRITE_REMOUNT_V26,
            27: self._c.SH_READ_WRITE_REMOUNT_V27,
            28: self._c.SH_READ_WRITE_REMOUNT_V28,
        }
        if isinstance(methods, int):
            methods = [methods]

        for method in methods:
            results.append(self.write_and_wait(remount_dict[method], timeout=timeout))
        return results


    def get_df_lsmod(self, timeout=1000):
        so = list(self.write_and_wait_list(f"""{self.system_bin}lsmod""",timeout=timeout).first)
        if len(so)<2:
            return pd_DataFrame()
        so=so[1:]
        return pd.read_csv(
            StringIO(
                (
                    b"\n".join(
                        b'"' + b'","'.join(y[:3] + [y[3].rstrip(b" |").strip()]) + b'"'
                        for y in [(x + b" |").split(maxsplit=3) for x in so]
                        if len(y)==4
                    )
                ).decode("utf-8", "backslashreplace")
            ),
            encoding="utf-8",
            sep=",",
            index_col=False,
            encoding_errors="backslashreplace",
            on_bad_lines="warn",
            engine="python",
            na_filter=False,
            quoting=1,
            names=[
                "aa_module",
                "aa_size",
                "aa_used_by_no",
                "aa_used_by",
            ],
        )


    def get_df_lsof(self, timeout=1000000):
        so = list(self.write_and_wait_list(f"""{self.system_bin}lsof""", timeout=timeout).first)
        if len(so)<2:
            return pd_DataFrame()
        so=so[1:]
        df = pd.read_csv(
            StringIO(
                (
                    b"\n".join(
                        (
                            b'"' + b'","'.join(y) + b'"'
                            for y in [x.strip().split(maxsplit=5) for x in so]
                            if len(y) == 6
                        )
                    )
                ).decode("utf-8", "backslashreplace")
            ),
            encoding="utf-8",
            sep=",",
            index_col=False,
            encoding_errors="backslashreplace",
            on_bad_lines="warn",
            engine="python",
            na_filter=False,
            quoting=1,
            names=[
                "aa_COMMAND",
                "aa_PID",
                "aa_USER",
                "aa_FD",
                "aa_TYPE",
                "aa_DEVICE_SIZE_NODE_NAME",
            ],
        )

        df.loc[:,"tmpindex"] = df.index.__array__().copy()
        df.loc[:, "aa_DEVICE_SIZE_NODE_NAME"] = (
            df["tmpindex"].astype(str) + "|" + df["aa_DEVICE_SIZE_NODE_NAME"]
        )

        DEVICE_SIZE_NODE_NAME = df.aa_DEVICE_SIZE_NODE_NAME.str.extractall(
            regex_device_size_node_name,
        ).reset_index(drop=True)
        DEVICE_SIZE_NODE_NAME.loc[:, "tmpindex"] = (
            DEVICE_SIZE_NODE_NAME.tmpindex.astype(int)
        )
        DEVICE_SIZE_NODE_NAME.set_index("tmpindex", inplace=True)
        return (
            pd.merge(
                df, DEVICE_SIZE_NODE_NAME, how="left", left_index=True, right_index=True
            )
            .dropna(inplace=False)
            .drop(columns=["tmpindex", "aa_DEVICE_SIZE_NODE_NAME"], inplace=False)
            .reset_index(drop=True)
        )

cpdef letter_normalize_lookup(
    str l, bint case_sens= True, str replace= "", str add_to_printable = ""
):
    cdef:
        object index_tuple
        list v
        str sug,stri_pri
        bint is_printable_letter,is_printable,is_capital
    index_tuple = (l, case_sens, replace, add_to_printable)
    if index_tuple in letter_lookup_dict:
        return letter_lookup_dict[index_tuple]

    v = sorted(unicodedata_name(l).split(), key=len)
    sug = replace
    stri_pri = string_printable + add_to_printable.upper()
    is_printable_letter = v[0] in stri_pri
    is_printable = l in stri_pri
    is_capital = "CAPITAL" in v
    if is_printable_letter:
        sug = v[0]

        if case_sens:
            if not is_capital:
                sug = v[0].lower()
    elif is_printable:
        sug = l
    letter_lookup_dict[index_tuple] = sug
    return sug


cpdef int random_int_function(int minint, int maxint):
    if maxint > minint:
        return random_randint(minint, maxint)
    return minint

@cython.final
cdef class UnicodeInputText:
    cdef:
        str text
        list[bytes] normalized_text
        list[str] cmd
        bint send_each_letter_separately
        dict kwargs
        bytes encoded_text
        str cached_str
        bytes cached_bytes
    def __init__(self,str adb_exe, str device_id, str text, str cmd, bint send_each_letter_separately, object kwargs=None):
        self.text = text
        self.normalized_text = [f"input text '{letter_normalize_lookup(x)}'".encode() if x not in latin_keycombination else latin_keycombination[x] for x in text]
        self.cmd = [adb_exe, "-s", device_id, "shell"]
        self.send_each_letter_separately = send_each_letter_separately
        self.kwargs = kwargs if kwargs is not None else {}
        self.cached_str = ""
        self.cached_bytes=b""

    def __str__(self):
        if not self.cached_str:
            self.cached_str=(b'\n'.join(self.normalized_text)).decode("utf-8","ignore")
        return self.cached_str

    def __repr__(self):
        return self.__str__()

    def __call__(self, int min_press=1, int max_press=4):
        cdef:
            bytes letter
        if self.send_each_letter_separately:
            for letter in self.normalized_text:
                subprocess_run(
                    self.cmd,
                    **{**invisibledict, "env": os_environ, **self.kwargs, "input":letter},
                )
                timesleep(float(random_int_function(min_press, max_press)) / 1000)
        else:
            if not self.cached_bytes:
                self.cached_bytes=b'\n'.join(self.normalized_text)
            subprocess_run(
                self.cmd,
                **{**invisibledict, "env": os_environ, **self.kwargs,"input":self.cached_bytes},
            )

@cython.final
cdef class InputText:
    cdef:
        str text
        str normalized_text
        list[str] cmd
        bint send_each_letter_separately
        dict kwargs

    def __init__(self,str adb_exe, str device_id, str text, str cmd, bint send_each_letter_separately, object kwargs=None):
        self.text = text
        self.normalized_text = "".join(letter_normalize_lookup(x) for x in text)
        self.cmd = [adb_exe, "-s", device_id, "shell", cmd]
        self.send_each_letter_separately = send_each_letter_separately
        self.kwargs = kwargs if kwargs is not None else {}

    def __str__(self):
        return self.normalized_text

    def __repr__(self):
        return self.__str__()

    def __call__(self, int min_press=1, int max_press=4):
        cdef:
            str letter
            list[str] executecmd
        if self.send_each_letter_separately:
            for letter in self.normalized_text:
                executecmd=self.cmd.copy()
                if letter != "'":
                    executecmd[len(executecmd)-1] = executecmd[len(executecmd)-1] +  f" '{letter}'"
                    subprocess_run(
                        executecmd,
                        **{**invisibledict, "env": os_environ, **self.kwargs},
                    )
                else:
                    executecmd[len(executecmd)-1] = executecmd[len(executecmd)-1] +  ''' "'"'''
                    subprocess_run(
                        executecmd,
                        **{**invisibledict, "env": os_environ, **self.kwargs},
                    )
                timesleep(float(random_int_function(min_press, max_press)) / 1000)
        else:
            executecmd=self.cmd.copy()
            executecmd[len(executecmd)-1] = executecmd[len(executecmd)-1] + " " +  self.normalized_text.replace("'", "'\\''")
            subprocess_run(
                executecmd,
                **{**invisibledict, "env": os_environ, **self.kwargs},
            )


@cython.final
cdef class KeyCodePresser:
    cdef:
        str adb_exe
        str device_id
        dict kwargs

    def __init__(
        self,
        str adb_exe,
        str device_id,
        object kwargs=None
    ):
        self.adb_exe = adb_exe
        self.device_id = device_id
        self.kwargs = kwargs if kwargs is not None else {}

    cdef _press(self, str cmd):
        subprocess_run([self.adb_exe, "-s", self.device_id, "shell", cmd],**{**invisibledict,**self.kwargs})

    cpdef long_press_KEYCODE_SOFT_LEFT(self):
        return self._press("input keyevent --longpress 1")

    cpdef short_press_KEYCODE_SOFT_LEFT(self):
        return self._press("input keyevent 1")

    cpdef long_press_KEYCODE_SOFT_RIGHT(self):
        return self._press("input keyevent --longpress 2")

    cpdef short_press_KEYCODE_SOFT_RIGHT(self):
        return self._press("input keyevent 2")

    cpdef long_press_KEYCODE_HOME(self):
        return self._press("input keyevent --longpress 3")

    cpdef short_press_KEYCODE_HOME(self):
        return self._press("input keyevent 3")

    cpdef long_press_KEYCODE_BACK(self):
        return self._press("input keyevent --longpress 4")

    cpdef short_press_KEYCODE_BACK(self):
        return self._press("input keyevent 4")

    cpdef long_press_KEYCODE_CALL(self):
        return self._press("input keyevent --longpress 5")

    cpdef short_press_KEYCODE_CALL(self):
        return self._press("input keyevent 5")

    cpdef long_press_KEYCODE_ENDCALL(self):
        return self._press("input keyevent --longpress 6")

    cpdef short_press_KEYCODE_ENDCALL(self):
        return self._press("input keyevent 6")

    cpdef long_press_KEYCODE_0(self):
        return self._press("input keyevent --longpress 7")

    cpdef short_press_KEYCODE_0(self):
        return self._press("input keyevent 7")

    cpdef long_press_KEYCODE_1(self):
        return self._press("input keyevent --longpress 8")

    cpdef short_press_KEYCODE_1(self):
        return self._press("input keyevent 8")

    cpdef long_press_KEYCODE_2(self):
        return self._press("input keyevent --longpress 9")

    cpdef short_press_KEYCODE_2(self):
        return self._press("input keyevent 9")

    cpdef long_press_KEYCODE_3(self):
        return self._press("input keyevent --longpress 10")

    cpdef short_press_KEYCODE_3(self):
        return self._press("input keyevent 10")

    cpdef long_press_KEYCODE_4(self):
        return self._press("input keyevent --longpress 11")

    cpdef short_press_KEYCODE_4(self):
        return self._press("input keyevent 11")

    cpdef long_press_KEYCODE_5(self):
        return self._press("input keyevent --longpress 12")

    cpdef short_press_KEYCODE_5(self):
        return self._press("input keyevent 12")

    cpdef long_press_KEYCODE_6(self):
        return self._press("input keyevent --longpress 13")

    cpdef short_press_KEYCODE_6(self):
        return self._press("input keyevent 13")

    cpdef long_press_KEYCODE_7(self):
        return self._press("input keyevent --longpress 14")

    cpdef short_press_KEYCODE_7(self):
        return self._press("input keyevent 14")

    cpdef long_press_KEYCODE_8(self):
        return self._press("input keyevent --longpress 15")

    cpdef short_press_KEYCODE_8(self):
        return self._press("input keyevent 15")

    cpdef long_press_KEYCODE_9(self):
        return self._press("input keyevent --longpress 16")

    cpdef short_press_KEYCODE_9(self):
        return self._press("input keyevent 16")

    cpdef long_press_KEYCODE_STAR(self):
        return self._press("input keyevent --longpress 17")

    cpdef short_press_KEYCODE_STAR(self):
        return self._press("input keyevent 17")

    cpdef long_press_KEYCODE_POUND(self):
        return self._press("input keyevent --longpress 18")

    cpdef short_press_KEYCODE_POUND(self):
        return self._press("input keyevent 18")

    cpdef long_press_KEYCODE_DPAD_UP(self):
        return self._press("input keyevent --longpress 19")

    cpdef short_press_KEYCODE_DPAD_UP(self):
        return self._press("input keyevent 19")

    cpdef long_press_KEYCODE_DPAD_DOWN(self):
        return self._press("input keyevent --longpress 20")

    cpdef short_press_KEYCODE_DPAD_DOWN(self):
        return self._press("input keyevent 20")

    cpdef long_press_KEYCODE_DPAD_LEFT(self):
        return self._press("input keyevent --longpress 21")

    cpdef short_press_KEYCODE_DPAD_LEFT(self):
        return self._press("input keyevent 21")

    cpdef long_press_KEYCODE_DPAD_RIGHT(self):
        return self._press("input keyevent --longpress 22")

    cpdef short_press_KEYCODE_DPAD_RIGHT(self):
        return self._press("input keyevent 22")

    cpdef long_press_KEYCODE_DPAD_CENTER(self):
        return self._press("input keyevent --longpress 23")

    cpdef short_press_KEYCODE_DPAD_CENTER(self):
        return self._press("input keyevent 23")

    cpdef long_press_KEYCODE_VOLUME_UP(self):
        return self._press("input keyevent --longpress 24")

    cpdef short_press_KEYCODE_VOLUME_UP(self):
        return self._press("input keyevent 24")

    cpdef long_press_KEYCODE_VOLUME_DOWN(self):
        return self._press("input keyevent --longpress 25")

    cpdef short_press_KEYCODE_VOLUME_DOWN(self):
        return self._press("input keyevent 25")

    cpdef long_press_KEYCODE_POWER(self):
        return self._press("input keyevent --longpress 26")

    cpdef short_press_KEYCODE_POWER(self):
        return self._press("input keyevent 26")

    cpdef long_press_KEYCODE_CAMERA(self):
        return self._press("input keyevent --longpress 27")

    cpdef short_press_KEYCODE_CAMERA(self):
        return self._press("input keyevent 27")

    cpdef long_press_KEYCODE_CLEAR(self):
        return self._press("input keyevent --longpress 28")

    cpdef short_press_KEYCODE_CLEAR(self):
        return self._press("input keyevent 28")

    cpdef long_press_KEYCODE_A(self):
        return self._press("input keyevent --longpress 29")

    cpdef short_press_KEYCODE_A(self):
        return self._press("input keyevent 29")

    cpdef long_press_KEYCODE_B(self):
        return self._press("input keyevent --longpress 30")

    cpdef short_press_KEYCODE_B(self):
        return self._press("input keyevent 30")

    cpdef long_press_KEYCODE_C(self):
        return self._press("input keyevent --longpress 31")

    cpdef short_press_KEYCODE_C(self):
        return self._press("input keyevent 31")

    cpdef long_press_KEYCODE_D(self):
        return self._press("input keyevent --longpress 32")

    cpdef short_press_KEYCODE_D(self):
        return self._press("input keyevent 32")

    cpdef long_press_KEYCODE_E(self):
        return self._press("input keyevent --longpress 33")

    cpdef short_press_KEYCODE_E(self):
        return self._press("input keyevent 33")

    cpdef long_press_KEYCODE_F(self):
        return self._press("input keyevent --longpress 34")

    cpdef short_press_KEYCODE_F(self):
        return self._press("input keyevent 34")

    cpdef long_press_KEYCODE_G(self):
        return self._press("input keyevent --longpress 35")

    cpdef short_press_KEYCODE_G(self):
        return self._press("input keyevent 35")

    cpdef long_press_KEYCODE_H(self):
        return self._press("input keyevent --longpress 36")

    cpdef short_press_KEYCODE_H(self):
        return self._press("input keyevent 36")

    cpdef long_press_KEYCODE_I(self):
        return self._press("input keyevent --longpress 37")

    cpdef short_press_KEYCODE_I(self):
        return self._press("input keyevent 37")

    cpdef long_press_KEYCODE_J(self):
        return self._press("input keyevent --longpress 38")

    cpdef short_press_KEYCODE_J(self):
        return self._press("input keyevent 38")

    cpdef long_press_KEYCODE_K(self):
        return self._press("input keyevent --longpress 39")

    cpdef short_press_KEYCODE_K(self):
        return self._press("input keyevent 39")

    cpdef long_press_KEYCODE_L(self):
        return self._press("input keyevent --longpress 40")

    cpdef short_press_KEYCODE_L(self):
        return self._press("input keyevent 40")

    cpdef long_press_KEYCODE_M(self):
        return self._press("input keyevent --longpress 41")

    cpdef short_press_KEYCODE_M(self):
        return self._press("input keyevent 41")

    cpdef long_press_KEYCODE_N(self):
        return self._press("input keyevent --longpress 42")

    cpdef short_press_KEYCODE_N(self):
        return self._press("input keyevent 42")

    cpdef long_press_KEYCODE_O(self):
        return self._press("input keyevent --longpress 43")

    cpdef short_press_KEYCODE_O(self):
        return self._press("input keyevent 43")

    cpdef long_press_KEYCODE_P(self):
        return self._press("input keyevent --longpress 44")

    cpdef short_press_KEYCODE_P(self):
        return self._press("input keyevent 44")

    cpdef long_press_KEYCODE_Q(self):
        return self._press("input keyevent --longpress 45")

    cpdef short_press_KEYCODE_Q(self):
        return self._press("input keyevent 45")

    cpdef long_press_KEYCODE_R(self):
        return self._press("input keyevent --longpress 46")

    cpdef short_press_KEYCODE_R(self):
        return self._press("input keyevent 46")

    cpdef long_press_KEYCODE_S(self):
        return self._press("input keyevent --longpress 47")

    cpdef short_press_KEYCODE_S(self):
        return self._press("input keyevent 47")

    cpdef long_press_KEYCODE_T(self):
        return self._press("input keyevent --longpress 48")

    cpdef short_press_KEYCODE_T(self):
        return self._press("input keyevent 48")

    cpdef long_press_KEYCODE_U(self):
        return self._press("input keyevent --longpress 49")

    cpdef short_press_KEYCODE_U(self):
        return self._press("input keyevent 49")

    cpdef long_press_KEYCODE_V(self):
        return self._press("input keyevent --longpress 50")

    cpdef short_press_KEYCODE_V(self):
        return self._press("input keyevent 50")

    cpdef long_press_KEYCODE_W(self):
        return self._press("input keyevent --longpress 51")

    cpdef short_press_KEYCODE_W(self):
        return self._press("input keyevent 51")

    cpdef long_press_KEYCODE_X(self):
        return self._press("input keyevent --longpress 52")

    cpdef short_press_KEYCODE_X(self):
        return self._press("input keyevent 52")

    cpdef long_press_KEYCODE_Y(self):
        return self._press("input keyevent --longpress 53")

    cpdef short_press_KEYCODE_Y(self):
        return self._press("input keyevent 53")

    cpdef long_press_KEYCODE_Z(self):
        return self._press("input keyevent --longpress 54")

    cpdef short_press_KEYCODE_Z(self):
        return self._press("input keyevent 54")

    cpdef long_press_KEYCODE_COMMA(self):
        return self._press("input keyevent --longpress 55")

    cpdef short_press_KEYCODE_COMMA(self):
        return self._press("input keyevent 55")

    cpdef long_press_KEYCODE_PERIOD(self):
        return self._press("input keyevent --longpress 56")

    cpdef short_press_KEYCODE_PERIOD(self):
        return self._press("input keyevent 56")

    cpdef long_press_KEYCODE_ALT_LEFT(self):
        return self._press("input keyevent --longpress 57")

    cpdef short_press_KEYCODE_ALT_LEFT(self):
        return self._press("input keyevent 57")

    cpdef long_press_KEYCODE_ALT_RIGHT(self):
        return self._press("input keyevent --longpress 58")

    cpdef short_press_KEYCODE_ALT_RIGHT(self):
        return self._press("input keyevent 58")

    cpdef long_press_KEYCODE_SHIFT_LEFT(self):
        return self._press("input keyevent --longpress 59")

    cpdef short_press_KEYCODE_SHIFT_LEFT(self):
        return self._press("input keyevent 59")

    cpdef long_press_KEYCODE_SHIFT_RIGHT(self):
        return self._press("input keyevent --longpress 60")

    cpdef short_press_KEYCODE_SHIFT_RIGHT(self):
        return self._press("input keyevent 60")

    cpdef long_press_KEYCODE_TAB(self):
        return self._press("input keyevent --longpress 61")

    cpdef short_press_KEYCODE_TAB(self):
        return self._press("input keyevent 61")

    cpdef long_press_KEYCODE_SPACE(self):
        return self._press("input keyevent --longpress 62")

    cpdef short_press_KEYCODE_SPACE(self):
        return self._press("input keyevent 62")

    cpdef long_press_KEYCODE_SYM(self):
        return self._press("input keyevent --longpress 63")

    cpdef short_press_KEYCODE_SYM(self):
        return self._press("input keyevent 63")

    cpdef long_press_KEYCODE_EXPLORER(self):
        return self._press("input keyevent --longpress 64")

    cpdef short_press_KEYCODE_EXPLORER(self):
        return self._press("input keyevent 64")

    cpdef long_press_KEYCODE_ENVELOPE(self):
        return self._press("input keyevent --longpress 65")

    cpdef short_press_KEYCODE_ENVELOPE(self):
        return self._press("input keyevent 65")

    cpdef long_press_KEYCODE_ENTER(self):
        return self._press("input keyevent --longpress 66")

    cpdef short_press_KEYCODE_ENTER(self):
        return self._press("input keyevent 66")

    cpdef long_press_KEYCODE_DEL(self):
        return self._press("input keyevent --longpress 67")

    cpdef short_press_KEYCODE_DEL(self):
        return self._press("input keyevent 67")

    cpdef long_press_KEYCODE_GRAVE(self):
        return self._press("input keyevent --longpress 68")

    cpdef short_press_KEYCODE_GRAVE(self):
        return self._press("input keyevent 68")

    cpdef long_press_KEYCODE_MINUS(self):
        return self._press("input keyevent --longpress 69")

    cpdef short_press_KEYCODE_MINUS(self):
        return self._press("input keyevent 69")

    cpdef long_press_KEYCODE_EQUALS(self):
        return self._press("input keyevent --longpress 70")

    cpdef short_press_KEYCODE_EQUALS(self):
        return self._press("input keyevent 70")

    cpdef long_press_KEYCODE_LEFT_BRACKET(self):
        return self._press("input keyevent --longpress 71")

    cpdef short_press_KEYCODE_LEFT_BRACKET(self):
        return self._press("input keyevent 71")

    cpdef long_press_KEYCODE_RIGHT_BRACKET(self):
        return self._press("input keyevent --longpress 72")

    cpdef short_press_KEYCODE_RIGHT_BRACKET(self):
        return self._press("input keyevent 72")

    cpdef long_press_KEYCODE_BACKSLASH(self):
        return self._press("input keyevent --longpress 73")

    cpdef short_press_KEYCODE_BACKSLASH(self):
        return self._press("input keyevent 73")

    cpdef long_press_KEYCODE_SEMICOLON(self):
        return self._press("input keyevent --longpress 74")

    cpdef short_press_KEYCODE_SEMICOLON(self):
        return self._press("input keyevent 74")

    cpdef long_press_KEYCODE_APOSTROPHE(self):
        return self._press("input keyevent --longpress 75")

    cpdef short_press_KEYCODE_APOSTROPHE(self):
        return self._press("input keyevent 75")

    cpdef long_press_KEYCODE_SLASH(self):
        return self._press("input keyevent --longpress 76")

    cpdef short_press_KEYCODE_SLASH(self):
        return self._press("input keyevent 76")

    cpdef long_press_KEYCODE_AT(self):
        return self._press("input keyevent --longpress 77")

    cpdef short_press_KEYCODE_AT(self):
        return self._press("input keyevent 77")

    cpdef long_press_KEYCODE_NUM(self):
        return self._press("input keyevent --longpress 78")

    cpdef short_press_KEYCODE_NUM(self):
        return self._press("input keyevent 78")

    cpdef long_press_KEYCODE_HEADSETHOOK(self):
        return self._press("input keyevent --longpress 79")

    cpdef short_press_KEYCODE_HEADSETHOOK(self):
        return self._press("input keyevent 79")

    cpdef long_press_KEYCODE_FOCUS(self):
        return self._press("input keyevent --longpress 80")

    cpdef short_press_KEYCODE_FOCUS(self):
        return self._press("input keyevent 80")

    cpdef long_press_KEYCODE_PLUS(self):
        return self._press("input keyevent --longpress 81")

    cpdef short_press_KEYCODE_PLUS(self):
        return self._press("input keyevent 81")

    cpdef long_press_KEYCODE_MENU(self):
        return self._press("input keyevent --longpress 82")

    cpdef short_press_KEYCODE_MENU(self):
        return self._press("input keyevent 82")

    cpdef long_press_KEYCODE_NOTIFICATION(self):
        return self._press("input keyevent --longpress 83")

    cpdef short_press_KEYCODE_NOTIFICATION(self):
        return self._press("input keyevent 83")

    cpdef long_press_KEYCODE_SEARCH(self):
        return self._press("input keyevent --longpress 84")

    cpdef short_press_KEYCODE_SEARCH(self):
        return self._press("input keyevent 84")

    cpdef long_press_KEYCODE_MEDIA_PLAY_PAUSE(self):
        return self._press("input keyevent --longpress 85")

    cpdef short_press_KEYCODE_MEDIA_PLAY_PAUSE(self):
        return self._press("input keyevent 85")

    cpdef long_press_KEYCODE_MEDIA_STOP(self):
        return self._press("input keyevent --longpress 86")

    cpdef short_press_KEYCODE_MEDIA_STOP(self):
        return self._press("input keyevent 86")

    cpdef long_press_KEYCODE_MEDIA_NEXT(self):
        return self._press("input keyevent --longpress 87")

    cpdef short_press_KEYCODE_MEDIA_NEXT(self):
        return self._press("input keyevent 87")

    cpdef long_press_KEYCODE_MEDIA_PREVIOUS(self):
        return self._press("input keyevent --longpress 88")

    cpdef short_press_KEYCODE_MEDIA_PREVIOUS(self):
        return self._press("input keyevent 88")

    cpdef long_press_KEYCODE_MEDIA_REWIND(self):
        return self._press("input keyevent --longpress 89")

    cpdef short_press_KEYCODE_MEDIA_REWIND(self):
        return self._press("input keyevent 89")

    cpdef long_press_KEYCODE_MEDIA_FAST_FORWARD(self):
        return self._press("input keyevent --longpress 90")

    cpdef short_press_KEYCODE_MEDIA_FAST_FORWARD(self):
        return self._press("input keyevent 90")

    cpdef long_press_KEYCODE_MUTE(self):
        return self._press("input keyevent --longpress 91")

    cpdef short_press_KEYCODE_MUTE(self):
        return self._press("input keyevent 91")

    cpdef long_press_KEYCODE_PAGE_UP(self):
        return self._press("input keyevent --longpress 92")

    cpdef short_press_KEYCODE_PAGE_UP(self):
        return self._press("input keyevent 92")

    cpdef long_press_KEYCODE_PAGE_DOWN(self):
        return self._press("input keyevent --longpress 93")

    cpdef short_press_KEYCODE_PAGE_DOWN(self):
        return self._press("input keyevent 93")

    cpdef long_press_KEYCODE_PICTSYMBOLS(self):
        return self._press("input keyevent --longpress 94")

    cpdef short_press_KEYCODE_PICTSYMBOLS(self):
        return self._press("input keyevent 94")

    cpdef long_press_KEYCODE_SWITCH_CHARSET(self):
        return self._press("input keyevent --longpress 95")

    cpdef short_press_KEYCODE_SWITCH_CHARSET(self):
        return self._press("input keyevent 95")

    cpdef long_press_KEYCODE_BUTTON_A(self):
        return self._press("input keyevent --longpress 96")

    cpdef short_press_KEYCODE_BUTTON_A(self):
        return self._press("input keyevent 96")

    cpdef long_press_KEYCODE_BUTTON_B(self):
        return self._press("input keyevent --longpress 97")

    cpdef short_press_KEYCODE_BUTTON_B(self):
        return self._press("input keyevent 97")

    cpdef long_press_KEYCODE_BUTTON_C(self):
        return self._press("input keyevent --longpress 98")

    cpdef short_press_KEYCODE_BUTTON_C(self):
        return self._press("input keyevent 98")

    cpdef long_press_KEYCODE_BUTTON_X(self):
        return self._press("input keyevent --longpress 99")

    cpdef short_press_KEYCODE_BUTTON_X(self):
        return self._press("input keyevent 99")

    cpdef long_press_KEYCODE_BUTTON_Y(self):
        return self._press("input keyevent --longpress 100")

    cpdef short_press_KEYCODE_BUTTON_Y(self):
        return self._press("input keyevent 100")

    cpdef long_press_KEYCODE_BUTTON_Z(self):
        return self._press("input keyevent --longpress 101")

    cpdef short_press_KEYCODE_BUTTON_Z(self):
        return self._press("input keyevent 101")

    cpdef long_press_KEYCODE_BUTTON_L1(self):
        return self._press("input keyevent --longpress 102")

    cpdef short_press_KEYCODE_BUTTON_L1(self):
        return self._press("input keyevent 102")

    cpdef long_press_KEYCODE_BUTTON_R1(self):
        return self._press("input keyevent --longpress 103")

    cpdef short_press_KEYCODE_BUTTON_R1(self):
        return self._press("input keyevent 103")

    cpdef long_press_KEYCODE_BUTTON_L2(self):
        return self._press("input keyevent --longpress 104")

    cpdef short_press_KEYCODE_BUTTON_L2(self):
        return self._press("input keyevent 104")

    cpdef long_press_KEYCODE_BUTTON_R2(self):
        return self._press("input keyevent --longpress 105")

    cpdef short_press_KEYCODE_BUTTON_R2(self):
        return self._press("input keyevent 105")

    cpdef long_press_KEYCODE_BUTTON_THUMBL(self):
        return self._press("input keyevent --longpress 106")

    cpdef short_press_KEYCODE_BUTTON_THUMBL(self):
        return self._press("input keyevent 106")

    cpdef long_press_KEYCODE_BUTTON_THUMBR(self):
        return self._press("input keyevent --longpress 107")

    cpdef short_press_KEYCODE_BUTTON_THUMBR(self):
        return self._press("input keyevent 107")

    cpdef long_press_KEYCODE_BUTTON_START(self):
        return self._press("input keyevent --longpress 108")

    cpdef short_press_KEYCODE_BUTTON_START(self):
        return self._press("input keyevent 108")

    cpdef long_press_KEYCODE_BUTTON_SELECT(self):
        return self._press("input keyevent --longpress 109")

    cpdef short_press_KEYCODE_BUTTON_SELECT(self):
        return self._press("input keyevent 109")

    cpdef long_press_KEYCODE_BUTTON_MODE(self):
        return self._press("input keyevent --longpress 110")

    cpdef short_press_KEYCODE_BUTTON_MODE(self):
        return self._press("input keyevent 110")

    cpdef long_press_KEYCODE_ESCAPE(self):
        return self._press("input keyevent --longpress 111")

    cpdef short_press_KEYCODE_ESCAPE(self):
        return self._press("input keyevent 111")

    cpdef long_press_KEYCODE_FORWARD_DEL(self):
        return self._press("input keyevent --longpress 112")

    cpdef short_press_KEYCODE_FORWARD_DEL(self):
        return self._press("input keyevent 112")

    cpdef long_press_KEYCODE_CTRL_LEFT(self):
        return self._press("input keyevent --longpress 113")

    cpdef short_press_KEYCODE_CTRL_LEFT(self):
        return self._press("input keyevent 113")

    cpdef long_press_KEYCODE_CTRL_RIGHT(self):
        return self._press("input keyevent --longpress 114")

    cpdef short_press_KEYCODE_CTRL_RIGHT(self):
        return self._press("input keyevent 114")

    cpdef long_press_KEYCODE_CAPS_LOCK(self):
        return self._press("input keyevent --longpress 115")

    cpdef short_press_KEYCODE_CAPS_LOCK(self):
        return self._press("input keyevent 115")

    cpdef long_press_KEYCODE_SCROLL_LOCK(self):
        return self._press("input keyevent --longpress 116")

    cpdef short_press_KEYCODE_SCROLL_LOCK(self):
        return self._press("input keyevent 116")

    cpdef long_press_KEYCODE_META_LEFT(self):
        return self._press("input keyevent --longpress 117")

    cpdef short_press_KEYCODE_META_LEFT(self):
        return self._press("input keyevent 117")

    cpdef long_press_KEYCODE_META_RIGHT(self):
        return self._press("input keyevent --longpress 118")

    cpdef short_press_KEYCODE_META_RIGHT(self):
        return self._press("input keyevent 118")

    cpdef long_press_KEYCODE_FUNCTION(self):
        return self._press("input keyevent --longpress 119")

    cpdef short_press_KEYCODE_FUNCTION(self):
        return self._press("input keyevent 119")

    cpdef long_press_KEYCODE_SYSRQ(self):
        return self._press("input keyevent --longpress 120")

    cpdef short_press_KEYCODE_SYSRQ(self):
        return self._press("input keyevent 120")

    cpdef long_press_KEYCODE_BREAK(self):
        return self._press("input keyevent --longpress 121")

    cpdef short_press_KEYCODE_BREAK(self):
        return self._press("input keyevent 121")

    cpdef long_press_KEYCODE_MOVE_HOME(self):
        return self._press("input keyevent --longpress 122")

    cpdef short_press_KEYCODE_MOVE_HOME(self):
        return self._press("input keyevent 122")

    cpdef long_press_KEYCODE_MOVE_END(self):
        return self._press("input keyevent --longpress 123")

    cpdef short_press_KEYCODE_MOVE_END(self):
        return self._press("input keyevent 123")

    cpdef long_press_KEYCODE_INSERT(self):
        return self._press("input keyevent --longpress 124")

    cpdef short_press_KEYCODE_INSERT(self):
        return self._press("input keyevent 124")

    cpdef long_press_KEYCODE_FORWARD(self):
        return self._press("input keyevent --longpress 125")

    cpdef short_press_KEYCODE_FORWARD(self):
        return self._press("input keyevent 125")

    cpdef long_press_KEYCODE_MEDIA_PLAY(self):
        return self._press("input keyevent --longpress 126")

    cpdef short_press_KEYCODE_MEDIA_PLAY(self):
        return self._press("input keyevent 126")

    cpdef long_press_KEYCODE_MEDIA_PAUSE(self):
        return self._press("input keyevent --longpress 127")

    cpdef short_press_KEYCODE_MEDIA_PAUSE(self):
        return self._press("input keyevent 127")

    cpdef long_press_KEYCODE_MEDIA_CLOSE(self):
        return self._press("input keyevent --longpress 128")

    cpdef short_press_KEYCODE_MEDIA_CLOSE(self):
        return self._press("input keyevent 128")

    cpdef long_press_KEYCODE_MEDIA_EJECT(self):
        return self._press("input keyevent --longpress 129")

    cpdef short_press_KEYCODE_MEDIA_EJECT(self):
        return self._press("input keyevent 129")

    cpdef long_press_KEYCODE_MEDIA_RECORD(self):
        return self._press("input keyevent --longpress 130")

    cpdef short_press_KEYCODE_MEDIA_RECORD(self):
        return self._press("input keyevent 130")

    cpdef long_press_KEYCODE_F1(self):
        return self._press("input keyevent --longpress 131")

    cpdef short_press_KEYCODE_F1(self):
        return self._press("input keyevent 131")

    cpdef long_press_KEYCODE_F2(self):
        return self._press("input keyevent --longpress 132")

    cpdef short_press_KEYCODE_F2(self):
        return self._press("input keyevent 132")

    cpdef long_press_KEYCODE_F3(self):
        return self._press("input keyevent --longpress 133")

    cpdef short_press_KEYCODE_F3(self):
        return self._press("input keyevent 133")

    cpdef long_press_KEYCODE_F4(self):
        return self._press("input keyevent --longpress 134")

    cpdef short_press_KEYCODE_F4(self):
        return self._press("input keyevent 134")

    cpdef long_press_KEYCODE_F5(self):
        return self._press("input keyevent --longpress 135")

    cpdef short_press_KEYCODE_F5(self):
        return self._press("input keyevent 135")

    cpdef long_press_KEYCODE_F6(self):
        return self._press("input keyevent --longpress 136")

    cpdef short_press_KEYCODE_F6(self):
        return self._press("input keyevent 136")

    cpdef long_press_KEYCODE_F7(self):
        return self._press("input keyevent --longpress 137")

    cpdef short_press_KEYCODE_F7(self):
        return self._press("input keyevent 137")

    cpdef long_press_KEYCODE_F8(self):
        return self._press("input keyevent --longpress 138")

    cpdef short_press_KEYCODE_F8(self):
        return self._press("input keyevent 138")

    cpdef long_press_KEYCODE_F9(self):
        return self._press("input keyevent --longpress 139")

    cpdef short_press_KEYCODE_F9(self):
        return self._press("input keyevent 139")

    cpdef long_press_KEYCODE_F10(self):
        return self._press("input keyevent --longpress 140")

    cpdef short_press_KEYCODE_F10(self):
        return self._press("input keyevent 140")

    cpdef long_press_KEYCODE_F11(self):
        return self._press("input keyevent --longpress 141")

    cpdef short_press_KEYCODE_F11(self):
        return self._press("input keyevent 141")

    cpdef long_press_KEYCODE_F12(self):
        return self._press("input keyevent --longpress 142")

    cpdef short_press_KEYCODE_F12(self):
        return self._press("input keyevent 142")

    cpdef long_press_KEYCODE_NUM_LOCK(self):
        return self._press("input keyevent --longpress 143")

    cpdef short_press_KEYCODE_NUM_LOCK(self):
        return self._press("input keyevent 143")

    cpdef long_press_KEYCODE_NUMPAD_0(self):
        return self._press("input keyevent --longpress 144")

    cpdef short_press_KEYCODE_NUMPAD_0(self):
        return self._press("input keyevent 144")

    cpdef long_press_KEYCODE_NUMPAD_1(self):
        return self._press("input keyevent --longpress 145")

    cpdef short_press_KEYCODE_NUMPAD_1(self):
        return self._press("input keyevent 145")

    cpdef long_press_KEYCODE_NUMPAD_2(self):
        return self._press("input keyevent --longpress 146")

    cpdef short_press_KEYCODE_NUMPAD_2(self):
        return self._press("input keyevent 146")

    cpdef long_press_KEYCODE_NUMPAD_3(self):
        return self._press("input keyevent --longpress 147")

    cpdef short_press_KEYCODE_NUMPAD_3(self):
        return self._press("input keyevent 147")

    cpdef long_press_KEYCODE_NUMPAD_4(self):
        return self._press("input keyevent --longpress 148")

    cpdef short_press_KEYCODE_NUMPAD_4(self):
        return self._press("input keyevent 148")

    cpdef long_press_KEYCODE_NUMPAD_5(self):
        return self._press("input keyevent --longpress 149")

    cpdef short_press_KEYCODE_NUMPAD_5(self):
        return self._press("input keyevent 149")

    cpdef long_press_KEYCODE_NUMPAD_6(self):
        return self._press("input keyevent --longpress 150")

    cpdef short_press_KEYCODE_NUMPAD_6(self):
        return self._press("input keyevent 150")

    cpdef long_press_KEYCODE_NUMPAD_7(self):
        return self._press("input keyevent --longpress 151")

    cpdef short_press_KEYCODE_NUMPAD_7(self):
        return self._press("input keyevent 151")

    cpdef long_press_KEYCODE_NUMPAD_8(self):
        return self._press("input keyevent --longpress 152")

    cpdef short_press_KEYCODE_NUMPAD_8(self):
        return self._press("input keyevent 152")

    cpdef long_press_KEYCODE_NUMPAD_9(self):
        return self._press("input keyevent --longpress 153")

    cpdef short_press_KEYCODE_NUMPAD_9(self):
        return self._press("input keyevent 153")

    cpdef long_press_KEYCODE_NUMPAD_DIVIDE(self):
        return self._press("input keyevent --longpress 154")

    cpdef short_press_KEYCODE_NUMPAD_DIVIDE(self):
        return self._press("input keyevent 154")

    cpdef long_press_KEYCODE_NUMPAD_MULTIPLY(self):
        return self._press("input keyevent --longpress 155")

    cpdef short_press_KEYCODE_NUMPAD_MULTIPLY(self):
        return self._press("input keyevent 155")

    cpdef long_press_KEYCODE_NUMPAD_SUBTRACT(self):
        return self._press("input keyevent --longpress 156")

    cpdef short_press_KEYCODE_NUMPAD_SUBTRACT(self):
        return self._press("input keyevent 156")

    cpdef long_press_KEYCODE_NUMPAD_ADD(self):
        return self._press("input keyevent --longpress 157")

    cpdef short_press_KEYCODE_NUMPAD_ADD(self):
        return self._press("input keyevent 157")

    cpdef long_press_KEYCODE_NUMPAD_DOT(self):
        return self._press("input keyevent --longpress 158")

    cpdef short_press_KEYCODE_NUMPAD_DOT(self):
        return self._press("input keyevent 158")

    cpdef long_press_KEYCODE_NUMPAD_COMMA(self):
        return self._press("input keyevent --longpress 159")

    cpdef short_press_KEYCODE_NUMPAD_COMMA(self):
        return self._press("input keyevent 159")

    cpdef long_press_KEYCODE_NUMPAD_ENTER(self):
        return self._press("input keyevent --longpress 160")

    cpdef short_press_KEYCODE_NUMPAD_ENTER(self):
        return self._press("input keyevent 160")

    cpdef long_press_KEYCODE_NUMPAD_EQUALS(self):
        return self._press("input keyevent --longpress 161")

    cpdef short_press_KEYCODE_NUMPAD_EQUALS(self):
        return self._press("input keyevent 161")

    cpdef long_press_KEYCODE_NUMPAD_LEFT_PAREN(self):
        return self._press("input keyevent --longpress 162")

    cpdef short_press_KEYCODE_NUMPAD_LEFT_PAREN(self):
        return self._press("input keyevent 162")

    cpdef long_press_KEYCODE_NUMPAD_RIGHT_PAREN(self):
        return self._press("input keyevent --longpress 163")

    cpdef short_press_KEYCODE_NUMPAD_RIGHT_PAREN(self):
        return self._press("input keyevent 163")

    cpdef long_press_KEYCODE_VOLUME_MUTE(self):
        return self._press("input keyevent --longpress 164")

    cpdef short_press_KEYCODE_VOLUME_MUTE(self):
        return self._press("input keyevent 164")

    cpdef long_press_KEYCODE_INFO(self):
        return self._press("input keyevent --longpress 165")

    cpdef short_press_KEYCODE_INFO(self):
        return self._press("input keyevent 165")

    cpdef long_press_KEYCODE_CHANNEL_UP(self):
        return self._press("input keyevent --longpress 166")

    cpdef short_press_KEYCODE_CHANNEL_UP(self):
        return self._press("input keyevent 166")

    cpdef long_press_KEYCODE_CHANNEL_DOWN(self):
        return self._press("input keyevent --longpress 167")

    cpdef short_press_KEYCODE_CHANNEL_DOWN(self):
        return self._press("input keyevent 167")

    cpdef long_press_KEYCODE_ZOOM_IN(self):
        return self._press("input keyevent --longpress 168")

    cpdef short_press_KEYCODE_ZOOM_IN(self):
        return self._press("input keyevent 168")

    cpdef long_press_KEYCODE_ZOOM_OUT(self):
        return self._press("input keyevent --longpress 169")

    cpdef short_press_KEYCODE_ZOOM_OUT(self):
        return self._press("input keyevent 169")

    cpdef long_press_KEYCODE_TV(self):
        return self._press("input keyevent --longpress 170")

    cpdef short_press_KEYCODE_TV(self):
        return self._press("input keyevent 170")

    cpdef long_press_KEYCODE_WINDOW(self):
        return self._press("input keyevent --longpress 171")

    cpdef short_press_KEYCODE_WINDOW(self):
        return self._press("input keyevent 171")

    cpdef long_press_KEYCODE_GUIDE(self):
        return self._press("input keyevent --longpress 172")

    cpdef short_press_KEYCODE_GUIDE(self):
        return self._press("input keyevent 172")

    cpdef long_press_KEYCODE_DVR(self):
        return self._press("input keyevent --longpress 173")

    cpdef short_press_KEYCODE_DVR(self):
        return self._press("input keyevent 173")

    cpdef long_press_KEYCODE_BOOKMARK(self):
        return self._press("input keyevent --longpress 174")

    cpdef short_press_KEYCODE_BOOKMARK(self):
        return self._press("input keyevent 174")

    cpdef long_press_KEYCODE_CAPTIONS(self):
        return self._press("input keyevent --longpress 175")

    cpdef short_press_KEYCODE_CAPTIONS(self):
        return self._press("input keyevent 175")

    cpdef long_press_KEYCODE_SETTINGS(self):
        return self._press("input keyevent --longpress 176")

    cpdef short_press_KEYCODE_SETTINGS(self):
        return self._press("input keyevent 176")

    cpdef long_press_KEYCODE_TV_POWER(self):
        return self._press("input keyevent --longpress 177")

    cpdef short_press_KEYCODE_TV_POWER(self):
        return self._press("input keyevent 177")

    cpdef long_press_KEYCODE_TV_INPUT(self):
        return self._press("input keyevent --longpress 178")

    cpdef short_press_KEYCODE_TV_INPUT(self):
        return self._press("input keyevent 178")

    cpdef long_press_KEYCODE_STB_POWER(self):
        return self._press("input keyevent --longpress 179")

    cpdef short_press_KEYCODE_STB_POWER(self):
        return self._press("input keyevent 179")

    cpdef long_press_KEYCODE_STB_INPUT(self):
        return self._press("input keyevent --longpress 180")

    cpdef short_press_KEYCODE_STB_INPUT(self):
        return self._press("input keyevent 180")

    cpdef long_press_KEYCODE_AVR_POWER(self):
        return self._press("input keyevent --longpress 181")

    cpdef short_press_KEYCODE_AVR_POWER(self):
        return self._press("input keyevent 181")

    cpdef long_press_KEYCODE_AVR_INPUT(self):
        return self._press("input keyevent --longpress 182")

    cpdef short_press_KEYCODE_AVR_INPUT(self):
        return self._press("input keyevent 182")

    cpdef long_press_KEYCODE_PROG_RED(self):
        return self._press("input keyevent --longpress 183")

    cpdef short_press_KEYCODE_PROG_RED(self):
        return self._press("input keyevent 183")

    cpdef long_press_KEYCODE_PROG_GREEN(self):
        return self._press("input keyevent --longpress 184")

    cpdef short_press_KEYCODE_PROG_GREEN(self):
        return self._press("input keyevent 184")

    cpdef long_press_KEYCODE_PROG_YELLOW(self):
        return self._press("input keyevent --longpress 185")

    cpdef short_press_KEYCODE_PROG_YELLOW(self):
        return self._press("input keyevent 185")

    cpdef long_press_KEYCODE_PROG_BLUE(self):
        return self._press("input keyevent --longpress 186")

    cpdef short_press_KEYCODE_PROG_BLUE(self):
        return self._press("input keyevent 186")

    cpdef long_press_KEYCODE_APP_SWITCH(self):
        return self._press("input keyevent --longpress 187")

    cpdef short_press_KEYCODE_APP_SWITCH(self):
        return self._press("input keyevent 187")

    cpdef long_press_KEYCODE_BUTTON_1(self):
        return self._press("input keyevent --longpress 188")

    cpdef short_press_KEYCODE_BUTTON_1(self):
        return self._press("input keyevent 188")

    cpdef long_press_KEYCODE_BUTTON_2(self):
        return self._press("input keyevent --longpress 189")

    cpdef short_press_KEYCODE_BUTTON_2(self):
        return self._press("input keyevent 189")

    cpdef long_press_KEYCODE_BUTTON_3(self):
        return self._press("input keyevent --longpress 190")

    cpdef short_press_KEYCODE_BUTTON_3(self):
        return self._press("input keyevent 190")

    cpdef long_press_KEYCODE_BUTTON_4(self):
        return self._press("input keyevent --longpress 191")

    cpdef short_press_KEYCODE_BUTTON_4(self):
        return self._press("input keyevent 191")

    cpdef long_press_KEYCODE_BUTTON_5(self):
        return self._press("input keyevent --longpress 192")

    cpdef short_press_KEYCODE_BUTTON_5(self):
        return self._press("input keyevent 192")

    cpdef long_press_KEYCODE_BUTTON_6(self):
        return self._press("input keyevent --longpress 193")

    cpdef short_press_KEYCODE_BUTTON_6(self):
        return self._press("input keyevent 193")

    cpdef long_press_KEYCODE_BUTTON_7(self):
        return self._press("input keyevent --longpress 194")

    cpdef short_press_KEYCODE_BUTTON_7(self):
        return self._press("input keyevent 194")

    cpdef long_press_KEYCODE_BUTTON_8(self):
        return self._press("input keyevent --longpress 195")

    cpdef short_press_KEYCODE_BUTTON_8(self):
        return self._press("input keyevent 195")

    cpdef long_press_KEYCODE_BUTTON_9(self):
        return self._press("input keyevent --longpress 196")

    cpdef short_press_KEYCODE_BUTTON_9(self):
        return self._press("input keyevent 196")

    cpdef long_press_KEYCODE_BUTTON_10(self):
        return self._press("input keyevent --longpress 197")

    cpdef short_press_KEYCODE_BUTTON_10(self):
        return self._press("input keyevent 197")

    cpdef long_press_KEYCODE_BUTTON_11(self):
        return self._press("input keyevent --longpress 198")

    cpdef short_press_KEYCODE_BUTTON_11(self):
        return self._press("input keyevent 198")

    cpdef long_press_KEYCODE_BUTTON_12(self):
        return self._press("input keyevent --longpress 199")

    cpdef short_press_KEYCODE_BUTTON_12(self):
        return self._press("input keyevent 199")

    cpdef long_press_KEYCODE_BUTTON_13(self):
        return self._press("input keyevent --longpress 200")

    cpdef short_press_KEYCODE_BUTTON_13(self):
        return self._press("input keyevent 200")

    cpdef long_press_KEYCODE_BUTTON_14(self):
        return self._press("input keyevent --longpress 201")

    cpdef short_press_KEYCODE_BUTTON_14(self):
        return self._press("input keyevent 201")

    cpdef long_press_KEYCODE_BUTTON_15(self):
        return self._press("input keyevent --longpress 202")

    cpdef short_press_KEYCODE_BUTTON_15(self):
        return self._press("input keyevent 202")

    cpdef long_press_KEYCODE_BUTTON_16(self):
        return self._press("input keyevent --longpress 203")

    cpdef short_press_KEYCODE_BUTTON_16(self):
        return self._press("input keyevent 203")

    cpdef long_press_KEYCODE_LANGUAGE_SWITCH(self):
        return self._press("input keyevent --longpress 204")

    cpdef short_press_KEYCODE_LANGUAGE_SWITCH(self):
        return self._press("input keyevent 204")

    cpdef long_press_KEYCODE_MANNER_MODE(self):
        return self._press("input keyevent --longpress 205")

    cpdef short_press_KEYCODE_MANNER_MODE(self):
        return self._press("input keyevent 205")

    cpdef long_press_KEYCODE_3D_MODE(self):
        return self._press("input keyevent --longpress 206")

    cpdef short_press_KEYCODE_3D_MODE(self):
        return self._press("input keyevent 206")

    cpdef long_press_KEYCODE_CONTACTS(self):
        return self._press("input keyevent --longpress 207")

    cpdef short_press_KEYCODE_CONTACTS(self):
        return self._press("input keyevent 207")

    cpdef long_press_KEYCODE_CALENDAR(self):
        return self._press("input keyevent --longpress 208")

    cpdef short_press_KEYCODE_CALENDAR(self):
        return self._press("input keyevent 208")

    cpdef long_press_KEYCODE_MUSIC(self):
        return self._press("input keyevent --longpress 209")

    cpdef short_press_KEYCODE_MUSIC(self):
        return self._press("input keyevent 209")

    cpdef long_press_KEYCODE_CALCULATOR(self):
        return self._press("input keyevent --longpress 210")

    cpdef short_press_KEYCODE_CALCULATOR(self):
        return self._press("input keyevent 210")

    cpdef long_press_KEYCODE_ZENKAKU_HANKAKU(self):
        return self._press("input keyevent --longpress 211")

    cpdef short_press_KEYCODE_ZENKAKU_HANKAKU(self):
        return self._press("input keyevent 211")

    cpdef long_press_KEYCODE_EISU(self):
        return self._press("input keyevent --longpress 212")

    cpdef short_press_KEYCODE_EISU(self):
        return self._press("input keyevent 212")

    cpdef long_press_KEYCODE_MUHENKAN(self):
        return self._press("input keyevent --longpress 213")

    cpdef short_press_KEYCODE_MUHENKAN(self):
        return self._press("input keyevent 213")

    cpdef long_press_KEYCODE_HENKAN(self):
        return self._press("input keyevent --longpress 214")

    cpdef short_press_KEYCODE_HENKAN(self):
        return self._press("input keyevent 214")

    cpdef long_press_KEYCODE_KATAKANA_HIRAGANA(self):
        return self._press("input keyevent --longpress 215")

    cpdef short_press_KEYCODE_KATAKANA_HIRAGANA(self):
        return self._press("input keyevent 215")

    cpdef long_press_KEYCODE_YEN(self):
        return self._press("input keyevent --longpress 216")

    cpdef short_press_KEYCODE_YEN(self):
        return self._press("input keyevent 216")

    cpdef long_press_KEYCODE_RO(self):
        return self._press("input keyevent --longpress 217")

    cpdef short_press_KEYCODE_RO(self):
        return self._press("input keyevent 217")

    cpdef long_press_KEYCODE_KANA(self):
        return self._press("input keyevent --longpress 218")

    cpdef short_press_KEYCODE_KANA(self):
        return self._press("input keyevent 218")

    cpdef long_press_KEYCODE_ASSIST(self):
        return self._press("input keyevent --longpress 219")

    cpdef short_press_KEYCODE_ASSIST(self):
        return self._press("input keyevent 219")

    cpdef long_press_KEYCODE_BRIGHTNESS_DOWN(self):
        return self._press("input keyevent --longpress 220")

    cpdef short_press_KEYCODE_BRIGHTNESS_DOWN(self):
        return self._press("input keyevent 220")

    cpdef long_press_KEYCODE_BRIGHTNESS_UP(self):
        return self._press("input keyevent --longpress 221")

    cpdef short_press_KEYCODE_BRIGHTNESS_UP(self):
        return self._press("input keyevent 221")

    cpdef long_press_KEYCODE_MEDIA_AUDIO_TRACK(self):
        return self._press("input keyevent --longpress 222")

    cpdef short_press_KEYCODE_MEDIA_AUDIO_TRACK(self):
        return self._press("input keyevent 222")

    cpdef long_press_KEYCODE_SLEEP(self):
        return self._press("input keyevent --longpress 223")

    cpdef short_press_KEYCODE_SLEEP(self):
        return self._press("input keyevent 223")

    cpdef long_press_KEYCODE_WAKEUP(self):
        return self._press("input keyevent --longpress 224")

    cpdef short_press_KEYCODE_WAKEUP(self):
        return self._press("input keyevent 224")

    cpdef long_press_KEYCODE_PAIRING(self):
        return self._press("input keyevent --longpress 225")

    cpdef short_press_KEYCODE_PAIRING(self):
        return self._press("input keyevent 225")

    cpdef long_press_KEYCODE_MEDIA_TOP_MENU(self):
        return self._press("input keyevent --longpress 226")

    cpdef short_press_KEYCODE_MEDIA_TOP_MENU(self):
        return self._press("input keyevent 226")

    cpdef long_press_KEYCODE_11(self):
        return self._press("input keyevent --longpress 227")

    cpdef short_press_KEYCODE_11(self):
        return self._press("input keyevent 227")

    cpdef long_press_KEYCODE_12(self):
        return self._press("input keyevent --longpress 228")

    cpdef short_press_KEYCODE_12(self):
        return self._press("input keyevent 228")

    cpdef long_press_KEYCODE_LAST_CHANNEL(self):
        return self._press("input keyevent --longpress 229")

    cpdef short_press_KEYCODE_LAST_CHANNEL(self):
        return self._press("input keyevent 229")

    cpdef long_press_KEYCODE_TV_DATA_SERVICE(self):
        return self._press("input keyevent --longpress 230")

    cpdef short_press_KEYCODE_TV_DATA_SERVICE(self):
        return self._press("input keyevent 230")

    cpdef long_press_KEYCODE_VOICE_ASSIST(self):
        return self._press("input keyevent --longpress 231")

    cpdef short_press_KEYCODE_VOICE_ASSIST(self):
        return self._press("input keyevent 231")

    cpdef long_press_KEYCODE_TV_RADIO_SERVICE(self):
        return self._press("input keyevent --longpress 232")

    cpdef short_press_KEYCODE_TV_RADIO_SERVICE(self):
        return self._press("input keyevent 232")

    cpdef long_press_KEYCODE_TV_TELETEXT(self):
        return self._press("input keyevent --longpress 233")

    cpdef short_press_KEYCODE_TV_TELETEXT(self):
        return self._press("input keyevent 233")

    cpdef long_press_KEYCODE_TV_NUMBER_ENTRY(self):
        return self._press("input keyevent --longpress 234")

    cpdef short_press_KEYCODE_TV_NUMBER_ENTRY(self):
        return self._press("input keyevent 234")

    cpdef long_press_KEYCODE_TV_TERRESTRIAL_ANALOG(self):
        return self._press("input keyevent --longpress 235")

    cpdef short_press_KEYCODE_TV_TERRESTRIAL_ANALOG(self):
        return self._press("input keyevent 235")

    cpdef long_press_KEYCODE_TV_TERRESTRIAL_DIGITAL(self):
        return self._press("input keyevent --longpress 236")

    cpdef short_press_KEYCODE_TV_TERRESTRIAL_DIGITAL(self):
        return self._press("input keyevent 236")

    cpdef long_press_KEYCODE_TV_SATELLITE(self):
        return self._press("input keyevent --longpress 237")

    cpdef short_press_KEYCODE_TV_SATELLITE(self):
        return self._press("input keyevent 237")

    cpdef long_press_KEYCODE_TV_SATELLITE_BS(self):
        return self._press("input keyevent --longpress 238")

    cpdef short_press_KEYCODE_TV_SATELLITE_BS(self):
        return self._press("input keyevent 238")

    cpdef long_press_KEYCODE_TV_SATELLITE_CS(self):
        return self._press("input keyevent --longpress 239")

    cpdef short_press_KEYCODE_TV_SATELLITE_CS(self):
        return self._press("input keyevent 239")

    cpdef long_press_KEYCODE_TV_SATELLITE_SERVICE(self):
        return self._press("input keyevent --longpress 240")

    cpdef short_press_KEYCODE_TV_SATELLITE_SERVICE(self):
        return self._press("input keyevent 240")

    cpdef long_press_KEYCODE_TV_NETWORK(self):
        return self._press("input keyevent --longpress 241")

    cpdef short_press_KEYCODE_TV_NETWORK(self):
        return self._press("input keyevent 241")

    cpdef long_press_KEYCODE_TV_ANTENNA_CABLE(self):
        return self._press("input keyevent --longpress 242")

    cpdef short_press_KEYCODE_TV_ANTENNA_CABLE(self):
        return self._press("input keyevent 242")

    cpdef long_press_KEYCODE_TV_INPUT_HDMI_1(self):
        return self._press("input keyevent --longpress 243")

    cpdef short_press_KEYCODE_TV_INPUT_HDMI_1(self):
        return self._press("input keyevent 243")

    cpdef long_press_KEYCODE_TV_INPUT_HDMI_2(self):
        return self._press("input keyevent --longpress 244")

    cpdef short_press_KEYCODE_TV_INPUT_HDMI_2(self):
        return self._press("input keyevent 244")

    cpdef long_press_KEYCODE_TV_INPUT_HDMI_3(self):
        return self._press("input keyevent --longpress 245")

    cpdef short_press_KEYCODE_TV_INPUT_HDMI_3(self):
        return self._press("input keyevent 245")

    cpdef long_press_KEYCODE_TV_INPUT_HDMI_4(self):
        return self._press("input keyevent --longpress 246")

    cpdef short_press_KEYCODE_TV_INPUT_HDMI_4(self):
        return self._press("input keyevent 246")

    cpdef long_press_KEYCODE_TV_INPUT_COMPOSITE_1(self):
        return self._press("input keyevent --longpress 247")

    cpdef short_press_KEYCODE_TV_INPUT_COMPOSITE_1(self):
        return self._press("input keyevent 247")

    cpdef long_press_KEYCODE_TV_INPUT_COMPOSITE_2(self):
        return self._press("input keyevent --longpress 248")

    cpdef short_press_KEYCODE_TV_INPUT_COMPOSITE_2(self):
        return self._press("input keyevent 248")

    cpdef long_press_KEYCODE_TV_INPUT_COMPONENT_1(self):
        return self._press("input keyevent --longpress 249")

    cpdef short_press_KEYCODE_TV_INPUT_COMPONENT_1(self):
        return self._press("input keyevent 249")

    cpdef long_press_KEYCODE_TV_INPUT_COMPONENT_2(self):
        return self._press("input keyevent --longpress 250")

    cpdef short_press_KEYCODE_TV_INPUT_COMPONENT_2(self):
        return self._press("input keyevent 250")

    cpdef long_press_KEYCODE_TV_INPUT_VGA_1(self):
        return self._press("input keyevent --longpress 251")

    cpdef short_press_KEYCODE_TV_INPUT_VGA_1(self):
        return self._press("input keyevent 251")

    cpdef long_press_KEYCODE_TV_AUDIO_DESCRIPTION(self):
        return self._press("input keyevent --longpress 252")

    cpdef short_press_KEYCODE_TV_AUDIO_DESCRIPTION(self):
        return self._press("input keyevent 252")

    cpdef long_press_KEYCODE_TV_AUDIO_DESCRIPTION_MIX_UP(self):
        return self._press("input keyevent --longpress 253")

    cpdef short_press_KEYCODE_TV_AUDIO_DESCRIPTION_MIX_UP(self):
        return self._press("input keyevent 253")

    cpdef long_press_KEYCODE_TV_AUDIO_DESCRIPTION_MIX_DOWN(self):
        return self._press("input keyevent --longpress 254")

    cpdef short_press_KEYCODE_TV_AUDIO_DESCRIPTION_MIX_DOWN(self):
        return self._press("input keyevent 254")

    cpdef long_press_KEYCODE_TV_ZOOM_MODE(self):
        return self._press("input keyevent --longpress 255")

    cpdef short_press_KEYCODE_TV_ZOOM_MODE(self):
        return self._press("input keyevent 255")

    cpdef long_press_KEYCODE_TV_CONTENTS_MENU(self):
        return self._press("input keyevent --longpress 256")

    cpdef short_press_KEYCODE_TV_CONTENTS_MENU(self):
        return self._press("input keyevent 256")

    cpdef long_press_KEYCODE_TV_MEDIA_CONTEXT_MENU(self):
        return self._press("input keyevent --longpress 257")

    cpdef short_press_KEYCODE_TV_MEDIA_CONTEXT_MENU(self):
        return self._press("input keyevent 257")

    cpdef long_press_KEYCODE_TV_TIMER_PROGRAMMING(self):
        return self._press("input keyevent --longpress 258")

    cpdef short_press_KEYCODE_TV_TIMER_PROGRAMMING(self):
        return self._press("input keyevent 258")

    cpdef long_press_KEYCODE_HELP(self):
        return self._press("input keyevent --longpress 259")

    cpdef short_press_KEYCODE_HELP(self):
        return self._press("input keyevent 259")

    cpdef long_press_KEYCODE_NAVIGATE_PREVIOUS(self):
        return self._press("input keyevent --longpress 260")

    cpdef short_press_KEYCODE_NAVIGATE_PREVIOUS(self):
        return self._press("input keyevent 260")

    cpdef long_press_KEYCODE_NAVIGATE_NEXT(self):
        return self._press("input keyevent --longpress 261")

    cpdef short_press_KEYCODE_NAVIGATE_NEXT(self):
        return self._press("input keyevent 261")

    cpdef long_press_KEYCODE_NAVIGATE_IN(self):
        return self._press("input keyevent --longpress 262")

    cpdef short_press_KEYCODE_NAVIGATE_IN(self):
        return self._press("input keyevent 262")

    cpdef long_press_KEYCODE_NAVIGATE_OUT(self):
        return self._press("input keyevent --longpress 263")

    cpdef short_press_KEYCODE_NAVIGATE_OUT(self):
        return self._press("input keyevent 263")

    cpdef long_press_KEYCODE_STEM_PRIMARY(self):
        return self._press("input keyevent --longpress 264")

    cpdef short_press_KEYCODE_STEM_PRIMARY(self):
        return self._press("input keyevent 264")

    cpdef long_press_KEYCODE_STEM_1(self):
        return self._press("input keyevent --longpress 265")

    cpdef short_press_KEYCODE_STEM_1(self):
        return self._press("input keyevent 265")

    cpdef long_press_KEYCODE_STEM_2(self):
        return self._press("input keyevent --longpress 266")

    cpdef short_press_KEYCODE_STEM_2(self):
        return self._press("input keyevent 266")

    cpdef long_press_KEYCODE_STEM_3(self):
        return self._press("input keyevent --longpress 267")

    cpdef short_press_KEYCODE_STEM_3(self):
        return self._press("input keyevent 267")

    cpdef long_press_KEYCODE_DPAD_UP_LEFT(self):
        return self._press("input keyevent --longpress 268")

    cpdef short_press_KEYCODE_DPAD_UP_LEFT(self):
        return self._press("input keyevent 268")

    cpdef long_press_KEYCODE_DPAD_DOWN_LEFT(self):
        return self._press("input keyevent --longpress 269")

    cpdef short_press_KEYCODE_DPAD_DOWN_LEFT(self):
        return self._press("input keyevent 269")

    cpdef long_press_KEYCODE_DPAD_UP_RIGHT(self):
        return self._press("input keyevent --longpress 270")

    cpdef short_press_KEYCODE_DPAD_UP_RIGHT(self):
        return self._press("input keyevent 270")

    cpdef long_press_KEYCODE_DPAD_DOWN_RIGHT(self):
        return self._press("input keyevent --longpress 271")

    cpdef short_press_KEYCODE_DPAD_DOWN_RIGHT(self):
        return self._press("input keyevent 271")

    cpdef long_press_KEYCODE_MEDIA_SKIP_FORWARD(self):
        return self._press("input keyevent --longpress 272")

    cpdef short_press_KEYCODE_MEDIA_SKIP_FORWARD(self):
        return self._press("input keyevent 272")

    cpdef long_press_KEYCODE_MEDIA_SKIP_BACKWARD(self):
        return self._press("input keyevent --longpress 273")

    cpdef short_press_KEYCODE_MEDIA_SKIP_BACKWARD(self):
        return self._press("input keyevent 273")

    cpdef long_press_KEYCODE_MEDIA_STEP_FORWARD(self):
        return self._press("input keyevent --longpress 274")

    cpdef short_press_KEYCODE_MEDIA_STEP_FORWARD(self):
        return self._press("input keyevent 274")

    cpdef long_press_KEYCODE_MEDIA_STEP_BACKWARD(self):
        return self._press("input keyevent --longpress 275")

    cpdef short_press_KEYCODE_MEDIA_STEP_BACKWARD(self):
        return self._press("input keyevent 275")

    cpdef long_press_KEYCODE_SOFT_SLEEP(self):
        return self._press("input keyevent --longpress 276")

    cpdef short_press_KEYCODE_SOFT_SLEEP(self):
        return self._press("input keyevent 276")

    cpdef long_press_KEYCODE_CUT(self):
        return self._press("input keyevent --longpress 277")

    cpdef short_press_KEYCODE_CUT(self):
        return self._press("input keyevent 277")

    cpdef long_press_KEYCODE_COPY(self):
        return self._press("input keyevent --longpress 278")

    cpdef short_press_KEYCODE_COPY(self):
        return self._press("input keyevent 278")

    cpdef long_press_KEYCODE_PASTE(self):
        return self._press("input keyevent --longpress 279")

    cpdef short_press_KEYCODE_PASTE(self):
        return self._press("input keyevent 279")

    cpdef long_press_KEYCODE_SYSTEM_NAVIGATION_UP(self):
        return self._press("input keyevent --longpress 280")

    cpdef short_press_KEYCODE_SYSTEM_NAVIGATION_UP(self):
        return self._press("input keyevent 280")

    cpdef long_press_KEYCODE_SYSTEM_NAVIGATION_DOWN(self):
        return self._press("input keyevent --longpress 281")

    cpdef short_press_KEYCODE_SYSTEM_NAVIGATION_DOWN(self):
        return self._press("input keyevent 281")

    cpdef long_press_KEYCODE_SYSTEM_NAVIGATION_LEFT(self):
        return self._press("input keyevent --longpress 282")

    cpdef short_press_KEYCODE_SYSTEM_NAVIGATION_LEFT(self):
        return self._press("input keyevent 282")

    cpdef long_press_KEYCODE_SYSTEM_NAVIGATION_RIGHT(self):
        return self._press("input keyevent --longpress 283")

    cpdef short_press_KEYCODE_SYSTEM_NAVIGATION_RIGHT(self):
        return self._press("input keyevent 283")

    cpdef long_press_KEYCODE_ALL_APPS(self):
        return self._press("input keyevent --longpress 284")

    cpdef short_press_KEYCODE_ALL_APPS(self):
        return self._press("input keyevent 284")

    cpdef long_press_KEYCODE_REFRESH(self):
        return self._press("input keyevent --longpress 285")

    cpdef short_press_KEYCODE_REFRESH(self):
        return self._press("input keyevent 285")

    cpdef long_press_KEYCODE_THUMBS_UP(self):
        return self._press("input keyevent --longpress 286")

    cpdef short_press_KEYCODE_THUMBS_UP(self):
        return self._press("input keyevent 286")

    cpdef long_press_KEYCODE_THUMBS_DOWN(self):
        return self._press("input keyevent --longpress 287")

    cpdef short_press_KEYCODE_THUMBS_DOWN(self):
        return self._press("input keyevent 287")

    cpdef long_press_KEYCODE_PROFILE_SWITCH(self):
        return self._press("input keyevent --longpress 288")

    cpdef short_press_KEYCODE_PROFILE_SWITCH(self):
        return self._press("input keyevent 288")

    cpdef long_press_KEYCODE_VIDEO_APP_1(self):
        return self._press("input keyevent --longpress 289")

    cpdef short_press_KEYCODE_VIDEO_APP_1(self):
        return self._press("input keyevent 289")

    cpdef long_press_KEYCODE_VIDEO_APP_2(self):
        return self._press("input keyevent --longpress 290")

    cpdef short_press_KEYCODE_VIDEO_APP_2(self):
        return self._press("input keyevent 290")

    cpdef long_press_KEYCODE_VIDEO_APP_3(self):
        return self._press("input keyevent --longpress 291")

    cpdef short_press_KEYCODE_VIDEO_APP_3(self):
        return self._press("input keyevent 291")

    cpdef long_press_KEYCODE_VIDEO_APP_4(self):
        return self._press("input keyevent --longpress 292")

    cpdef short_press_KEYCODE_VIDEO_APP_4(self):
        return self._press("input keyevent 292")

    cpdef long_press_KEYCODE_VIDEO_APP_5(self):
        return self._press("input keyevent --longpress 293")

    cpdef short_press_KEYCODE_VIDEO_APP_5(self):
        return self._press("input keyevent 293")

    cpdef long_press_KEYCODE_VIDEO_APP_6(self):
        return self._press("input keyevent --longpress 294")

    cpdef short_press_KEYCODE_VIDEO_APP_6(self):
        return self._press("input keyevent 294")

    cpdef long_press_KEYCODE_VIDEO_APP_7(self):
        return self._press("input keyevent --longpress 295")

    cpdef short_press_KEYCODE_VIDEO_APP_7(self):
        return self._press("input keyevent 295")

    cpdef long_press_KEYCODE_VIDEO_APP_8(self):
        return self._press("input keyevent --longpress 296")

    cpdef short_press_KEYCODE_VIDEO_APP_8(self):
        return self._press("input keyevent 296")

    cpdef long_press_KEYCODE_FEATURED_APP_1(self):
        return self._press("input keyevent --longpress 297")

    cpdef short_press_KEYCODE_FEATURED_APP_1(self):
        return self._press("input keyevent 297")

    cpdef long_press_KEYCODE_FEATURED_APP_2(self):
        return self._press("input keyevent --longpress 298")

    cpdef short_press_KEYCODE_FEATURED_APP_2(self):
        return self._press("input keyevent 298")

    cpdef long_press_KEYCODE_FEATURED_APP_3(self):
        return self._press("input keyevent --longpress 299")

    cpdef short_press_KEYCODE_FEATURED_APP_3(self):
        return self._press("input keyevent 299")

    cpdef long_press_KEYCODE_FEATURED_APP_4(self):
        return self._press("input keyevent --longpress 300")

    cpdef short_press_KEYCODE_FEATURED_APP_4(self):
        return self._press("input keyevent 300")

    cpdef long_press_KEYCODE_DEMO_APP_1(self):
        return self._press("input keyevent --longpress 301")

    cpdef short_press_KEYCODE_DEMO_APP_1(self):
        return self._press("input keyevent 301")

    cpdef long_press_KEYCODE_DEMO_APP_2(self):
        return self._press("input keyevent --longpress 302")

    cpdef short_press_KEYCODE_DEMO_APP_2(self):
        return self._press("input keyevent 302")

    cpdef long_press_KEYCODE_DEMO_APP_3(self):
        return self._press("input keyevent --longpress 303")

    cpdef short_press_KEYCODE_DEMO_APP_3(self):
        return self._press("input keyevent 303")

    cpdef long_press_KEYCODE_DEMO_APP_4(self):
        return self._press("input keyevent --longpress 304")

    cpdef short_press_KEYCODE_DEMO_APP_4(self):
        return self._press("input keyevent 304")

cdef str get_short_path_name(str long_name):
    cdef:
        object output_buf,shutiltemp
    if not os.path.exists(long_name):
        shutiltemp=shutil.which(long_name)
        if not shutiltemp:
            return long_name
        long_name=shutiltemp
    if not iswindows:
        return long_name
    try:
        output_buf = ctypes.create_unicode_buffer(8192)
        _ = _GetShortPathNameW(long_name, output_buf, 8192)
        return output_buf.value
    except Exception:
        errwrite()
    return long_name

cdef int convert_to_int(object o, int nan_val=0):
    if isinstance(o,int):
        return o
    if pdisna(o):
        return nan_val
    try:
        return int(o)
    except Exception:
        return nan_val

@cython.final
cdef class InputClick:
    cdef:
        int x
        int y
        list[str] cmd
        dict kwargs

    def __init__(self, str adb_exe, str device_id, object x, object y, cmd="input tap", kwargs=None):
        self.x = convert_to_int(x)
        self.y = convert_to_int(y)
        self.cmd = [adb_exe,"-s",device_id, "shell", cmd]
        self.kwargs = kwargs if kwargs else {}

    def __call__(self, int offset_x=0, int offset_y=0):
        cdef:
            list[str] executecmd = self.cmd.copy()
        executecmd[len(executecmd)-1] = f"{executecmd[len(executecmd)-1]} {int(self.x+offset_x)} {int(self.y+offset_y)}"
        return subprocess_run(executecmd, **{**invisibledict, **self.kwargs})

    def __str__(self):
        return "(offset_x=0, offset_y=0)"

    def __repr__(self):
        return self.__str__()


cpdef get_resolution_of_screen(adb_exe, device_id, kwargs):
    result = [
        list(map(int, x[0].split(b"x")))
        for x in [
            re.findall(
                rb"\b\d+x\d+\b",
                subprocess_run(
                    [adb_exe, "-s", device_id, "shell", "wm size"], **{**invisibledict, 'capture_output':True, **kwargs}
                ).stdout.strip(),
                flags=re.IGNORECASE,
            )
        ]
    ]
    return result[len(result) - 1]

@cython.final
cdef class AdbKeyBoard:
    cdef:
        str adb_exe
        str device_id
        str link
        str save_path
        list[str] valid_adb_keyboards
        dict kwargs

    def __init__(
        self,
        str adb_exe,
        str device_id,
        dict kwargs,
        str save_path,
        str link,
        list[str] valid_adb_keyboards,
    ):
        self.adb_exe = adb_exe
        self.device_id = device_id
        self.link = link
        self.save_path = save_path
        self.valid_adb_keyboards = valid_adb_keyboards
        self.kwargs = kwargs

    cpdef bint download_adbkeyboard_apk(self):
        """
        Download the ADB keyboard APK from the specified URL.

        This method sends an HTTP GET request to the URL defined in 'adb_keyboard_link'.
        If the response status code is 200, it writes the APK content to a local file path
        (stored in 'adb_keyboard_apk_path'). The file is saved for subsequent installation on the device.

        Returns
        -------
        bool
            True if the download is successful (HTTP status code 200), False otherwise.
        """
        cdef:
            bint success=False
        with requests.get(self.link) as r:
            if r.status_code == 200:
                with open(self.save_path, "wb") as f:
                    f.write(r.content)
                    success=True
        return success

    cpdef install_adbkeyboard_apk(self):
        """
        Install the downloaded ADB keyboard APK on the device.

        This method invokes the ADB command to install the ADB keyboard APK that was previously
        downloaded and stored locally (at the path specified by 'adb_keyboard_apk_path'). It uses
        the "-g" and "-t" flags to grant necessary permissions and allow test packages to be installed.
        The APK path is converted using 'get_short_path_name' to ensure compatibility on the target system.

        Returns
        -------
        subprocess.CompletedProcess
            The result from the subprocess call that installs the APK.
        """
        return subprocess_run(
            [self.adb_exe, "-s", self.device_id, "install", "-g", "-t", get_short_path_name(self.save_path) ],
            **{"env":os_environ, **invisibledict, **self.kwargs},
        )

    cpdef list get_all_installed_keyboards(self):
        """
        Retrieve a list of all installed keyboard input methods on the device.

        Returns
        -------
        list of str
            A list containing the names/identifiers of all keyboards installed on the device.
        """
        return [
            x.strip()
            for x in [
                x.strip().strip(":")
                for x in (
                    subprocess_run(
                        [self.adb_exe, "-s", self.device_id, "shell", "ime list -a"],
                        **{"env":os_environ, **invisibledict, **self.kwargs, "capture_output":True},
                    )
                    .stdout.strip()
                    .decode("utf-8")
                    .splitlines()
                )
                if re.search(r"^[^\s]", x)
            ]
        ]

    @cython.boundscheck(True)
    cpdef list activate_adb_keyboard(self):
        """
        Activate the ADB keyboard on the device.

        The method searches through the installed keyboards for a valid ADB keyboard.
        If none is found, it will attempt to download and install the required ADB keyboard APK,
        and then enable and set it as the active input method.

        Returns
        -------
        list
            A list containing the results of the subprocess calls that enable and set the ADB keyboard.
        """
        cdef:
            list keyba
        try:
            keyba = [
                x
                for x in self.get_all_installed_keyboards()
                if x in self.valid_adb_keyboards
            ][0]
        except Exception:
            self.download_adbkeyboard_apk()
            self.install_adbkeyboard_apk()
            keyba = [
                x
                for x in self.get_all_installed_keyboards()
                if x in self.valid_adb_keyboards
            ][0]
        return [subprocess_run(
            [self.adb_exe, "-s", self.device_id, "shell", f"ime enable {keyba}"],
            **{"env":os_environ, **invisibledict, **self.kwargs},
        ),
        subprocess_run(
            [self.adb_exe, "-s", self.device_id, "shell", f"ime set {keyba}"],
            **{"env":os_environ, **invisibledict, **self.kwargs},
        )]

    cpdef disable_adb_keyboard(self):
        """
        Disable the custom ADB keyboard by resetting the input method.

        Returns
        -------
        subprocess.CompletedProcess
            The result from the subprocess call that resets the input method.
        """
        return subprocess_run(
            [self.adb_exe, "-s", self.device_id, "shell", "ime reset"],
            **{"env":os_environ, **invisibledict, **self.kwargs},
        )

    cpdef list send_unicode_text_with_delay(
        self, str text, object delay_range = (0.05, 0.1)
    ):
        """
        Send Unicode text to the device with a configurable delay between each character.

        Each character from the input string is sent individually with a random delay
        between the specified minimum and maximum delay values.

        Parameters
        ----------
        text : str
            The Unicode text to be sent.
        delay_range : tuple of float, optional
            A tuple (min_delay, max_delay) in seconds to wait between sending characters (default is (0.05, 0.1)).

        Returns
        -------
        list
            A list containing the subprocess results for each character sent.
        """
        cdef:
            str t
            list results = []
        for t in list(text):
            results.append(self.send_unicode_text(t))
            timesleep((uniform(*delay_range)))
        return results

    cpdef send_unicode_text(self, str text):
        """
        Send a Unicode text string to the device.

        The text is encoded in Base64 and sent as a broadcast intent using an ADB shell command.
        This approach allows for proper transmission of special and non-ASCII characters.

        Parameters
        ----------
        text : str
            The Unicode text to send.

        Returns
        -------
        subprocess.CompletedProcess
            The result from the subprocess call that sends the broadcast.
        """
        cdef:
            str charsb64
        charsb64 = (
            "'"
            + (b64encode(text.encode("utf-8"))).decode("utf-8").replace("'", "'\\''")
            + "'"
        )
        return subprocess_run(
            [self.adb_exe, "-s", self.device_id, "shell", f"am broadcast -a ADB_INPUT_B64 --es msg {charsb64}"],
            **{"env": os_environ,**invisibledict, **self.kwargs,},
        )


class CyAndroCel:
    """
    A class to automate interactions with Android devices via ADB.

    This class provides methods for managing and automating various device operations,
    including retrieving installed keyboards, activating/disabling custom ADB keyboards,
    and sending Unicode text inputs. It is designed to support both direct command calls and
    more complex interaction flows with the Android device.

    Attributes
    ----------
    adb_exe : str
        The path to the ADB executable.
    device_id : str
        The unique identifier of the target Android device.
    subprocess_timeout : int
        Timeout (in seconds) for subprocess calls.
    tesseract_args : tuple
        Arguments to be passed to the Tesseract OCR executable.
    path_screencap : str
        Command or path used to capture device screenshots.
    path_exe_tesseract : str
        The path to the Tesseract executable.
    system_bin_path : str
        Path to system binaries (if required).
    add_input_tap : bool
        Flag indicating whether to add input tap functionality.
    input_cmd : str
        Command to simulate tap events.
    input_cmd_text : str
        Command to simulate text input events.
    screen_height : int
        The device screen height in pixels.
    screen_width : int
        The device screen width in pixels.
    sh_exe : str
        Shell executable command (default is "sh").
    su_exe : str
        Superuser command (default is "su").
    kwargs : dict
        Additional keyword arguments to pass to subprocess calls.
    tesseract_word_group_limit : int
        Limit for grouping words when processing OCR output.
    tesseract_delete_tmp_files : bool
        Flag indicating whether temporary OCR files should be deleted after processing.
    ui2_download_link1 : str
        URL for downloading the first UIAutomator2 APK.
    ui2_download_link2 : str
        URL for downloading the second UIAutomator2 APK.
    _active_uiautomator2 : bool
        Internal flag tracking the active state of the UIAutomator2 server.
    backend_uiautomator2 : object
        Instance of the UIAutomator2 backend.
    backend_uiautomator_classic : object
        Instance of the UiAutomatorClassic backend.
    backend_fragment_parser : object
        Instance of the FragMentDumper backend.
    backend_window_parser : object
        Instance of the WindowDumper backend.
    """
    def __init__(
        self,
        str adb_exe,
        str device_id,
        int subprocess_timeout = 30,
        bint add_input_tap = True,
        str input_cmd_tap = "input tap",
        str input_cmd_text = "input text",
        str input_cmd_swipe= "input swipe",
        int screen_height = 2400,
        int screen_width = 1080,
        str sh_exe = "sh",
        str su_exe = "su",
        str path_exe_tesseract = "tesseract",
        object tesseract_args = ("-l", "por+eng", "--oem", "3"),
        int tesseract_word_group_limit=20,
        bint tesseract_delete_tmp_files=True,
        str ui2_download_link1="https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator-test_with_hidden_elements.apk",
        str ui2_download_link2="https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator_with_hidden_elements.apk",
        str adb_keyboard_link = "https://github.com/hansalemaos/ADBKeyBoard/raw/refs/heads/master/ADBKeyboard.apk",
        object valid_adb_keyboards = (
            "com.android.adbkeyboard/.AdbIME",
            "com.github.uiautomator/.AdbKeyboard",
        ),
        object kwargs=None,
    ):
        """
        Initialize a CyAndroCel instance with the specified device and automation parameters.

        Parameters
        ----------
        adb_exe : str
            The path to the ADB executable.
        device_id : str
            The unique identifier of the target Android device.
        subprocess_timeout : int, optional
            Timeout in seconds for subprocess calls (default is 30).
        add_input_tap : bool, optional
            Flag to enable input tap functionality (default is True).
        input_cmd_tap : str, optional
            Command to simulate tap events (default is "input tap").
        input_cmd_text : str, optional
            Command to simulate text input events (default is "input text").
        input_cmd_swipe : str, optional
            Command to simulate swipe events (default is "input swipe").
        screen_height : int, optional
            The device screen height in pixels (default is 2400).
        screen_width : int, optional
            The device screen width in pixels (default is 1080).
        sh_exe : str, optional
            Shell executable command (default is "sh").
        su_exe : str, optional
            Superuser command (default is "su").
        path_exe_tesseract : str, optional
            The path to the Tesseract executable (default is "tesseract").
        tesseract_args : tuple, optional
            A tuple of arguments for the Tesseract OCR executable (default is ("-l", "por+eng", "--oem", "3")).
        tesseract_word_group_limit : int, optional
            Limit for grouping words when processing OCR output (default is 20).
        tesseract_delete_tmp_files : bool, optional
            Whether to delete temporary OCR files after processing (default is True).
        ui2_download_link1 : str, optional
            URL for downloading the first UIAutomator2 APK.
        ui2_download_link2 : str, optional
            URL for downloading the second UIAutomator2 APK.
        adb_keyboard_link : str, optional
            URL for downloading the ADB keyboard APK.
        valid_adb_keyboards : tuple, optional
            A tuple containing valid ADB keyboard identifiers.
        kwargs : dict, optional
            Additional keyword arguments to pass to subprocess calls.
        """
        self.adb_exe = get_short_path_name(adb_exe)
        self.device_id = device_id
        self.subprocess_timeout = subprocess_timeout
        self.tesseract_args = list(tesseract_args)
        self.path_screencap = "screencap"
        self.path_exe_tesseract = get_short_path_name(path_exe_tesseract)
        self.system_bin_path = ""
        self.add_input_tap = add_input_tap
        self.input_cmd = input_cmd_tap
        self.input_cmd_text = input_cmd_text
        self.input_cmd_swipe=input_cmd_swipe
        self.screen_height = screen_height
        self.screen_width = screen_width
        self.sh_exe = sh_exe
        self.su_exe = su_exe
        self.kwargs = kwargs if kwargs else {}
        self.tesseract_word_group_limit = tesseract_word_group_limit
        self.tesseract_delete_tmp_files = tesseract_delete_tmp_files
        self.ui2_download_link1 = ui2_download_link1
        self.ui2_download_link2 = ui2_download_link2
        self.adb_keyboard_link = adb_keyboard_link
        self.adb_keyboard_save_path = os.path.join(this_folder, "adbkeyboard.apk")
        self.valid_adb_keyboards = list(valid_adb_keyboards)

        self.adb_keyboard = AdbKeyBoard(
            adb_exe=self.adb_exe,
            device_id=self.device_id,
            kwargs = self.kwargs,
            save_path = self.adb_keyboard_save_path,
            link = self.adb_keyboard_link,
            valid_adb_keyboards = self.valid_adb_keyboards,
        )
        self.backend_window_parser = WindowDumper(
            adb_exe=self.adb_exe,
            device_id=self.device_id,
            timeout=self.subprocess_timeout,
            add_input_tap=self.add_input_tap,
            input_cmd=self.input_cmd,
            screen_height=screen_height,
            screen_width=screen_width,
            kwargs=self.kwargs,
            input_cmd_swipe=input_cmd_swipe
        )
        self.backend_fragment_parser = FragMentDumper(
            adb_exe=self.adb_exe,
            device_id=self.device_id,
            timeout=self.subprocess_timeout,
            add_input_tap=self.add_input_tap,
            input_cmd=self.input_cmd,
            screen_height=screen_height,
            screen_width=screen_width,
            kwargs=self.kwargs,
            input_cmd_swipe=input_cmd_swipe
        )
        self.backend_uiautomator_classic = UiAutomatorClassic(
            adb_exe=self.adb_exe,
            device_id=self.device_id,
            timeout=self.subprocess_timeout,
            add_input_tap=self.add_input_tap,
            input_cmd=self.input_cmd,
            screen_height=screen_height,
            screen_width=screen_width,
            kwargs=self.kwargs,
            input_cmd_swipe=input_cmd_swipe
        )

        self.backend_tesseract = TesserParser(
            adb_exe=self.adb_exe,
            device_id=self.device_id,
            tesseract_path=self.path_exe_tesseract,
            word_group_limit=self.tesseract_word_group_limit,
            delete_tmp_files=self.tesseract_delete_tmp_files,
            tesseract_args=self.tesseract_args,
            add_input_tap=self.add_input_tap,
            input_cmd=self.input_cmd,
            screen_height=screen_height,
            screen_width=screen_width,
            kwargs=self.kwargs,
            input_cmd_swipe=input_cmd_swipe
        )
        self.backend_uiautomator2 = UiAutomator2(
            adb_exe=self.adb_exe,
            device_id=self.device_id,
            download_link1=self.ui2_download_link1,
            download_link2=self.ui2_download_link2,
            timeout=self.subprocess_timeout,
            add_input_tap=self.add_input_tap,
            input_cmd=self.input_cmd,
            screen_height=screen_height,
            screen_width=screen_width,
            kwargs=self.kwargs,
            input_cmd_swipe=input_cmd_swipe
        )
        self._active_uiautomator2 = False
        self.KeyCodes = KeyCodePresser(
            adb_exe=self.adb_exe,
            device_id=self.device_id,
            kwargs=self.kwargs
        )


    @staticmethod
    def get_resolution_of_screen(str adb_exe, str device_id, **kwargs):
        """
        Retrieve the current screen resolution of the device.

        This method uses the ADB shell command 'wm size' to query the device's physical screen size.
        It parses the output (expected in the format "Physical size: 1080x2400"), updates the
        instance's screen_width and screen_height attributes, and returns them as a tuple.

        Returns
        -------
        tuple of int
            A tuple (screen_width, screen_height) representing the device's screen resolution.

        Raises
        ------
        ValueError
            If the screen resolution cannot be parsed from the command output.
        """
        return get_resolution_of_screen(adb_exe, device_id, kwargs)

    def get_df_tesseract(self,
        object tesseract_args=None,
        object word_group_limit=None,
        object delete_tmp_files=None,
    ):
        """
        Retrieve a DataFrame from OCR processing using Tesseract.

        Parameters
        ----------
        tesseract_args : object, optional
            Arguments for Tesseract OCR; defaults to self.tesseract_args.
        word_group_limit : object, optional
            Limit for word grouping; defaults to self.tesseract_word_group_limit.
        delete_tmp_files : object, optional
            Whether to delete temporary files; defaults to self.tesseract_delete_tmp_files.

        Returns
        -------
        DataFrame
            A Pandas DataFrame containing OCR results.
        """
        return self.backend_tesseract.get_df(
        tesseract_args=tesseract_args if tesseract_args is not None else self.tesseract_args,
        word_group_limit=word_group_limit if word_group_limit is not None else self.tesseract_word_group_limit,
        delete_tmp_files=delete_tmp_files if delete_tmp_files is not None else self.tesseract_delete_tmp_files,
    )


    def get_df_uiautomator_classic(self, bint with_screenshot=True, object timeout=None):
        """
        Retrieve a DataFrame from the classic UIAutomator dump.

        Parameters
        ----------
        with_screenshot : bool, optional
            If True, include screenshots in the DataFrame (default True).
        timeout : object, optional
            Timeout for the operation; defaults to self.subprocess_timeout.

        Returns
        -------
        DataFrame
            A Pandas DataFrame representing the UI hierarchy from classic UIAutomator.
        """
        self.stop_uiautomator2_server()
        return self.backend_uiautomator_classic.get_df(
            with_screenshot=with_screenshot,
            timeout=timeout if timeout is not None else self.subprocess_timeout,
        )

    def get_df_fragments(self, bint with_screenshot=True, object timeout=None):
        """
        Retrieve a DataFrame containing UI fragment information.

        Parameters
        ----------
        with_screenshot : bool, optional
            If True, attach screenshots to the DataFrame (default True).
        timeout : object, optional
            Timeout for the operation; defaults to self.subprocess_timeout.

        Returns
        -------
        DataFrame
            A Pandas DataFrame containing UI fragment data.
        """
        return self.backend_fragment_parser.get_df(
            with_screenshot=with_screenshot,
            timeout=timeout if timeout is not None else self.subprocess_timeout,
        )

    def get_df_uiautomator2(self, bint with_screenshot=True, object timeout=None):
        """
        Retrieve a DataFrame using UIAutomator2.

        This method starts the UIAutomator2 server if necessary and then retrieves
        the UI hierarchy as a DataFrame.

        Parameters
        ----------
        with_screenshot : bool, optional
            If True, include screenshots in the DataFrame (default True).
        timeout : object, optional
            Timeout for the operation; defaults to self.subprocess_timeout.

        Returns
        -------
        DataFrame
            A Pandas DataFrame representing the UI hierarchy obtained via UIAutomator2.
        """
        self.start_uiautomator2_server()
        return self.backend_uiautomator2.get_df(
            with_screenshot=with_screenshot,
            timeout=timeout if timeout is not None else self.subprocess_timeout,
        )
    def get_df_window_dump(self, bint with_screenshot=True, object timeout=None):
        """
        Retrieve a DataFrame from a window dump operation.

        Parameters
        ----------
        with_screenshot : bool, optional
            If True, attach screenshots to the DataFrame (default True).
        timeout : object, optional
            Timeout for the operation; defaults to self.subprocess_timeout.

        Returns
        -------
        DataFrame
            A Pandas DataFrame representing the window dump data.
        """
        return self.backend_window_parser.get_df(
            with_screenshot=with_screenshot,
            timeout=timeout if timeout is not None else self.subprocess_timeout,
        )

    def start_uiautomator2_server(self):
        """
        Start the UIAutomator2 server if it is not already active.

        This method invokes the start_server method of the UIAutomator2 backend,
        waits for a short period to allow the server to initialize, and sets the
        internal flag indicating that the server is active.
        """
        if not self._active_uiautomator2:
            self.backend_uiautomator2.start_server()
            timesleep(3)
            self._active_uiautomator2 = True

    def stop_uiautomator2_server(self):
        """
        Stop the UIAutomator2 server if it is currently active.

        This method calls the stop_server method of the UIAutomator2 backend and
        resets the internal active flag.
        """
        if self._active_uiautomator2:
            self.backend_uiautomator2.stop_server()
            self._active_uiautomator2 = False

    def download_and_install_uiautomator2_apks(self):
        """
        Download and install the UIAutomator2 APKs on the target device.

        This method downloads the required APKs using the UIAutomator2 backend's
        download_apks method and then installs them with install_apks.
        """
        self.backend_uiautomator2.download_apks()
        self.backend_uiautomator2.install_apks()

    def get_cmd_input_tap(self, int x, int y):
        """
        Generate a command to simulate a tap event at the specified coordinates.

        Parameters
        ----------
        x : int
            The x-coordinate of the tap location.
        y : int
            The y-coordinate of the tap location.

        Returns
        -------
        InputClick
            An InputClick object configured with the device and tap command.
        """
        return InputTapper(
            x,
            y,
            self.device_id,
            self.adb_exe,
            self.input_cmd,
            self.kwargs
        )

    def get_cmd_input_tap_long(self, int x, int y):
        """
        Generate a command to simulate a tap event at the specified coordinates.

        Parameters
        ----------
        x : int
            The x-coordinate of the tap location.
        y : int
            The y-coordinate of the tap location.

        Returns
        -------
        InputClick
            An InputClick object configured with the device and tap command.
        """
        return InputTapperLong(
            x,
            y,
            self.device_id,
            self.adb_exe,
            self.input_cmd_swipe,
            self.kwargs
        )
    def get_cmd_input_swipe(self, int x_start, int y_start, int x_end, int y_end, int duration):
        """
        Construct and return the swipe input command for the device.

        This method builds a command string for simulating a swipe event on the device using
        the configured swipe command (stored in the 'input_cmd_swipe' attribute). If a duration is provided,
        it appends it to the command; otherwise, it returns the command without a duration.

        Parameters
        ----------
        x_start : int
            The starting x-coordinate of the swipe.
        y_start : int
            The starting y-coordinate of the swipe.
        x_end : int
            The ending x-coordinate of the swipe.
        y_end : int
            The ending y-coordinate of the swipe.
        duration : int, optional
            The duration of the swipe in milliseconds. If provided, it is appended to the command.

        Returns
        -------
        str
            The complete command string to simulate a swipe on the device.

        Example
        -------
        >>> cmd = cyandrocel_instance.get_cmd_input_swipe(100, 200, 300, 400, 500)
        >>> print(cmd)
        "input swipe 100 200 300 400 500"
        """
        return InputSwipe(
            x_start,
            y_start,
            x_end,
            y_end,
            self.device_id,
            self.adb_exe,
            self.input_cmd_swipe,
            self.kwargs,
            duration
        )
    def get_cmd_send_text_unicode_natural(self, str text):
        """
        Generate a command to send text input naturally (letter-by-letter) to the device.

        Parameters
        ----------
        text : str
            The text to be sent.

        Returns
        -------
        InputText
            An InputText object configured for sending text with per-letter delay.
        """
        return UnicodeInputText(
            adb_exe=self.adb_exe,
            device_id=self.device_id,
            text=text,
            cmd=self.input_cmd_text,
            send_each_letter_separately=True,
            kwargs=self.kwargs)


    def get_cmd_send_text_unicode(self, str text):
        """
        Generate a command to send text input to the device.

        Parameters
        ----------
        text : str
            The text to be sent.

        Returns
        -------
        InputText
            An InputText object configured for sending text without per-letter delay.
        """
        return UnicodeInputText(
            adb_exe=self.adb_exe,
            device_id=self.device_id,
            text=text,
            cmd=self.input_cmd_text,
            send_each_letter_separately=False,
            kwargs=self.kwargs)

    def get_cmd_send_text(self, str text):
        """
        Generate a command to send text input to the device.

        Parameters
        ----------
        text : str
            The text to be sent.

        Returns
        -------
        InputText
            An InputText object configured for sending text without per-letter delay.
        """
        return InputText(
            adb_exe=self.adb_exe,
            device_id=self.device_id,
            text=text,
            cmd=self.input_cmd_text,
            send_each_letter_separately=False,
            kwargs=self.kwargs)

    def get_cmd_send_text_natural(self,  str text):
        """
        Generate a command to send text input naturally (letter-by-letter) to the device.

        Parameters
        ----------
        text : str
            The text to be sent.

        Returns
        -------
        InputText
            An InputText object configured for sending text with per-letter delay.
        """
        return InputText(
            adb_exe=self.adb_exe,
            device_id=self.device_id,
            text=text,
            cmd=self.input_cmd_text,
            send_each_letter_separately=True,
            kwargs=self.kwargs)


    def open_shell(
        self,
        int buffer_size=40960,
        bytes exit_command=b"exit",
        bint print_stdout=False,
        bint print_stderr=False,
    ):
        """
        Open an interactive shell on the device via ADB.

        Parameters
        ----------
        buffer_size : int, optional
            The buffer size for the shell output (default 40960).
        exit_command : bytes, optional
            Command to signal shell exit (default b"exit").
        print_stdout : bool, optional
            If True, print standard output to the console.
        print_stderr : bool, optional
            If True, print standard error to the console.

        Returns
        -------
        Shelly
            An instance of the Shelly class representing the open shell.
        """
        return Shelly(
            shell_command=f"{self.adb_exe} -s {self.device_id} shell",
            buffer_size=buffer_size,
            stdout_max_len=buffer_size,
            stderr_max_len=buffer_size,
            exit_command=exit_command,
            print_stdout=print_stdout,
            print_stderr=print_stderr,
            su_exe=self.su_exe,
            finish_cmd="HERE_IS_FINISH",
            system_bin=self.system_bin_path,
        )


add_printer(True)
download_any_parser(cpp_file=cpp_file_ui2, url=url_ui2_parser)
compile_any_parser(cpp_file_pure=cpp_file_pure_ui2, exe_file_pure=exe_file_pure_ui2,exe_file=exe_file_ui2)

download_any_parser(cpp_file=cpp_file_ui1, url=url_ui1_parser)
compile_any_parser(cpp_file_pure=cpp_file_pure_ui1, exe_file_pure=exe_file_pure_ui1,exe_file=exe_file_ui1)

download_any_parser(cpp_file=cpp_file_tesser, url=url_tesser_parser)
compile_any_parser(cpp_file_pure=cpp_file_pure_tesser, exe_file_pure=exe_file_pure_tesser,exe_file=exe_file_tesser)

download_any_parser(cpp_file=cpp_file_fragment, url=url_fragment_parser)
compile_any_parser(cpp_file_pure=cpp_file_pure_fragment, exe_file_pure=exe_file_pure_fragment,exe_file=exe_file_fragment)

DataFrame.d_fm_damerau_levenshtein_distance_1way = (
    d_fm_damerau_levenshtein_distance_1way
)
DataFrame.d_fm_damerau_levenshtein_distance_2ways = (
    d_fm_damerau_levenshtein_distance_2ways
)
DataFrame.d_fm_hemming_distance_1way = d_fm_hemming_distance_1way
DataFrame.d_fm_hemming_distance_2ways = d_fm_hemming_distance_2ways
DataFrame.d_fm_jaro_2ways = d_fm_jaro_2ways
DataFrame.d_fm_jaro_distance_1way = d_fm_jaro_distance_1way
DataFrame.d_fm_jaro_winkler_distance_1way = d_fm_jaro_winkler_distance_1way
DataFrame.d_fm_jaro_winkler_distance_2ways = d_fm_jaro_winkler_distance_2ways
DataFrame.d_fm_levenshtein_distance_1way = d_fm_levenshtein_distance_1way
DataFrame.d_fm_levenshtein_distance_2ways = d_fm_levenshtein_distance_2ways
DataFrame.d_fm_longest_common_subsequence_v0 = d_fm_longest_common_subsequence_v0
DataFrame.d_fm_longest_common_substring_v0 = d_fm_longest_common_substring_v0
DataFrame.d_fm_longest_common_substring_v1 = d_fm_longest_common_substring_v1
DataFrame.d_fm_subsequence_v1 = d_fm_subsequence_v1
DataFrame.d_fm_subsequence_v2 = d_fm_subsequence_v2
DataFrame.bb_save_screenshots_as_png = d_save_screenshots_as_png
DataFrame.bb_save_screenshots_as_ppm = d_save_screenshots_as_ppm
DataFrame.bb_search_for_colors = d_color_search

