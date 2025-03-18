from Cython.Compiler import Options
from setuptools import Extension, setup
from Cython.Build import cythonize
import sys
import platform
import os

try:
    import numpy as np

    numpyincludefolder = np.get_include()
except Exception:
    numpyincludefolder = ""

iswindows = "win" in platform.platform().lower()
name = "uiev"

Options.docstrings = True
Options.embed_pos_in_docstring = True
Options.generate_cleanup_code = False
Options.clear_to_none = True
Options.annotate = True
Options.fast_fail = False
Options.warning_errors = False
Options.error_on_unknown_names = True
Options.error_on_uninitialized = True
Options.convert_range = True
Options.cache_builtins = True
if iswindows:
    Options.gcc_branch_hints = False
else:
    Options.gcc_branch_hints = True
Options.lookup_module_cpdef = False
Options.embed = False
Options.cimport_from_pyx = True
Options.buffer_max_dims = 8
Options.closure_freelist_size = 8


configdict = {
    "py_limited_api": False,
    "name": name,
    "sources": [
        name + ".pyx",
    ],
    "include_dirs": [
        numpyincludefolder,
    ]
    if numpyincludefolder
    else [],
    "define_macros": [
        # ("NPY_NO_DEPRECATED_API", 1),
        # ("CYTHON_ASSUME_SAFE_MACROS", 0),
        # ("CYTHON_AVOID_BORROWED_REFS", 0),
        # ("CYTHON_CLINE_IN_TRACEBACK", 0),
        # ("CYTHON_COMPILING_IN_CPYTHON", 0),
        # ("CYTHON_COMPILING_IN_GRAAL", 0),
        # ("CYTHON_COMPILING_IN_GRAAL", 1),
        # ("CYTHON_COMPILING_IN_LIMITED_API", 0),
        # ("CYTHON_COMPILING_IN_NOGIL", 0),
        # ("CYTHON_COMPILING_IN_PYPY", 0),
        # ("CYTHON_FAST_GIL", 0),
        # ("CYTHON_FAST_PYCALL", 0),
        # ("CYTHON_FAST_THREAD_STATE", 0),
        # ("CYTHON_FUTURE_DIVISION", 1),
        # ("CYTHON_METH_FASTCALL", 0),
        # ("CYTHON_PEP487_INIT_SUBCLASS", 1),
        # ("CYTHON_PEP489_MULTI_PHASE_INIT", 0),
        # ("CYTHON_UNPACK_METHODS", 0),
        # ("CYTHON_UPDATE_DESCRIPTOR_DOC", 0),
        # ("CYTHON_USE_ASYNC_SLOTS", 0),
        # ("CYTHON_USE_CPP_STD_MOVE", 0),
        # ("CYTHON_USE_DICT_VERSIONS", 0),
        # ("CYTHON_USE_EXC_INFO_STACK", 0),
        # ("CYTHON_USE_FREELISTS", 0),
        # ("CYTHON_USE_MODULE_STATE", 0),
        # ("CYTHON_USE_PYLIST_INTERNALS", 0),
        # ("CYTHON_USE_PYLONG_INTERNALS", 0),
        # ("CYTHON_USE_PYTYPE_LOOKUP", 0),
        # ("CYTHON_USE_TP_FINALIZE", 0),
        # ("CYTHON_USE_TYPE_SLOTS", 0),
        # ("CYTHON_USE_TYPE_SPECS", 0),
        # ("CYTHON_USE_UNICODE_INTERNALS", 0),
        # ("CYTHON_USE_UNICODE_WRITER", 0),
    ],
    "undef_macros": [],
    "library_dirs": [],
    "libraries": [],
    "runtime_library_dirs": [],
    "extra_objects": [],
    "extra_compile_args": [
        "/std:c++20",
    ]
    if iswindows
    else [
        "-march=native",
        "-mtune=native",
        "-std=c++2a",
        "-pthread",
    ],
    "extra_link_args": [],
    "export_symbols": [],
    "swig_opts": [],
    "depends": [],
    "language": "c++",
    "optional": None,
}
compiler_directives = {
    "binding": True,
    "boundscheck": False,
    "wraparound": False,
    "initializedcheck": False,
    "nonecheck": False,
    "overflowcheck": False,
    "overflowcheck.fold": True,
    "embedsignature": True,
    "embedsignature.format": "c",  # (c / python / clinic)
    "cdivision": True,
    "cdivision_warnings": True,
    "cpow": True,
    "always_allow_keywords": True,
    "c_api_binop_methods": False,
    "profile": False,
    "linetrace": True,
    "infer_types": True,
    "language_level": 3,  # (2/3/3str)
    "c_string_type": "bytes",  # (bytes / str / unicode)
    "c_string_encoding": "ascii",  # (ascii, default, utf-8, etc.)
    "type_version_tag": False,
    "unraisable_tracebacks": True,
    "iterable_coroutine": True,
    "annotation_typing": True,
    "emit_code_comments": True,
    "cpp_locals": False,
    "legacy_implicit_noexcept": False,
    "optimize.use_switch": True,
    "optimize.unpack_method_calls": True,
    "warn.undeclared": True,  # (default False)
    "warn.unreachable": True,  # (default True)
    "warn.maybe_uninitialized": True,  # (default False)
    "warn.unused": True,  # (default False)
    "warn.unused_arg": True,  # (default False)
    "warn.unused_result": True,  # (default False)
    "warn.multiple_declarators": True,  # (default True)
    "show_performance_hints": True,  # (default True)
}

ext_modules = Extension(**configdict)

setup(
    name=name,
    ext_modules=cythonize(ext_modules, compiler_directives=compiler_directives),
)
sys.exit(0)
