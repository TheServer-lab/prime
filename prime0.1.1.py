#!/usr/bin/env python3
"""
PRIME INTERPRETER - Single-file Programming Language Implementation
==============================================================

A complete implementation of the PRIME programming language with:
- Explicit module exports (export func / export let / export { a, b, fn })
- REPL with balanced braces and expression result printing
- Module-level __init__ auto-run on import
- Deterministic .pbc bytecode format with disassembler
- Assertion-based test harness with temporary module creation/cleanup
- Standalone executable compilation (via PyInstaller)
- Comprehensive I/O operations and standard library

Version: 0.1.2
Changes: Fixed critical bugs, added read/input builtin, # comments, better errors

Architecture:
-------------
1. Lexer (tokenize) - Converts source code to tokens
2. Parser - Converts tokens to bytecode using recursive descent
3. Emitter - Generates and manages bytecode, handles .pbc format
4. Virtual Machine - Executes bytecode with stack-based architecture
5. Standard Library - Built-in functions for I/O, strings, math, etc.

Usage:
------
  python3 prime.py <file.prime>                # Run a PRIME program
  python3 prime.py --compile <file.prime> <out.pbc>  # Compile to bytecode
  python3 prime.py --runpbc <file.pbc>         # Run compiled bytecode
  python3 prime.py --disasm <file.pbc>         # Disassemble bytecode
  python3 prime.py --repl                      # Start interactive REPL
  python3 prime.py --test                      # Run test suite
  python3 prime.py --verify <file.pbc>         # Verify bytecode integrity
  python3 prime.py --version                   # Show version info
  python3 prime.py --compile-exe <file.prime> <out.exe>  # Create standalone executable
  python3 prime.py --compile-py <file.prime> <out.py>    # Create standalone Python script

File Structure:
--------------
.prime   - PRIME source code
.pbc     - PRIME ByteCode (binary format)
.py      - Standalone Python script with embedded bytecode

Note: This is a full reference implementation in a single file for portability.
"""

import sys
import json
import struct
import os
import time
import tempfile
import shutil
import io
import contextlib
import base64
import zlib
import subprocess
import math
import random
import re
import datetime
import platform
import argparse
from dataclasses import dataclass

# =======================
# VERSION INFORMATION
# =======================
VERSION = "0.1.2"
BYTECODE_VERSION = 1  # Increment for breaking changes to bytecode format

# =======================
# LEXER (Tokenization)
# =======================
# Converts source code string into a stream of tokens with line number tracking

KEYWORDS = {
    # Variable declarations
    "let", "set", "const",
    # Control flow
    "if", "else", "elif",
    # Loops
    "loop", "while", "in", "from", "to", "for",
    # Functions
    "func", "return",
    # Literals
    "true", "false", "null",
    # Logical operators
    "and", "or", "not",
    # Error handling
    "attempt", "catch", "throw",
    # I/O and control
    "say", "break", "continue",
    # Modules
    "import", "as",
    # Exports
    "export",
}

@dataclass
class Token:
    """Represents a single token with type, value, and line number."""
    type: str   # "NUM", "STR", "ID", "KW", "SYM", "EOF"
    value: any  # Actual token value (int, float, string, etc.)
    line: int   # Line number in source code (1-indexed)

    def __repr__(self):
        return f"Token({self.type},{self.value},line={self.line})"

def tokenize(src: str):
    """
    Convert source code string into a list of tokens.
    
    Args:
        src: Source code as a string
        
    Returns:
        List of Token objects
        
    Raises:
        SyntaxError: On invalid characters
    
    Token Types:
        NUM: Integer or float literal
        STR: String literal (supports \n, \t escapes)
        ID: Identifier (variable/function name)
        KW: Keyword from KEYWORDS set
        SYM: Symbol/operator (+, -, *, /, etc.)
        EOF: End of file marker
    """
    i = 0
    n = len(src)
    tokens = []
    line = 1
    while i < n:
        c = src[i]
        # Newline tracking
        if c == "\n":
            line += 1
            i += 1
            continue
        # Skip whitespace
        if c.isspace():
            i += 1
            continue
        # Single-line comments (both // and #)
        if c == "/" and i+1 < n and src[i+1] == "/":
            i += 2
            while i < n and src[i] != "\n":
                i += 1
            continue
        # Hash comments
        if c == "#":
            i += 1
            while i < n and src[i] != "\n":
                i += 1
            continue
        # Block comments /* ... */
        if c == "/" and i+1 < n and src[i+1] == "*":
            i += 2
            while i+1 < n and not (src[i] == "*" and src[i+1] == "/"):
                if src[i] == "\n":
                    line += 1
                i += 1
            i += 2  # Skip closing */
            continue
        # Numbers (integers and floats)
        if c.isdigit():
            start = i
            while i < n and (src[i].isdigit() or src[i] == "."):
                i += 1
            s = src[start:i]
            if "." in s:
                tokens.append(Token("NUM", float(s), line))
            else:
                tokens.append(Token("NUM", int(s), line))
            continue
        # String literals (with escape sequences)
        if c == '"':
            i += 1
            start = i
            s_chars = []
            while i < n and src[i] != '"':
                if src[i] == "\\" and i+1 < n:
                    esc = src[i+1]
                    if esc == "n":
                        s_chars.append("\n")
                    elif esc == "t":
                        s_chars.append("\t")
                    elif esc == "\\":
                        s_chars.append("\\")
                    elif esc == '"':
                        s_chars.append('"')
                    else:
                        s_chars.append(esc)
                    i += 2
                    continue
                s_chars.append(src[i])
                i += 1
            s = "".join(s_chars)
            i += 1
            tokens.append(Token("STR", s, line))
            continue
        # Identifiers and keywords
        if c.isalpha() or c == "_":
            start = i
            while i < n and (src[i].isalnum() or src[i] == "_"):
                i += 1
            w = src[start:i]
            if w in KEYWORDS:
                tokens.append(Token("KW", w, line))
            else:
                tokens.append(Token("ID", w, line))
            continue
        # Two-character symbols (==, !=, <=, >=)
        two = src[i:i+2]
        if two in ("==", "!=", "<=", ">="):
            tokens.append(Token("SYM", two, line))
            i += 2
            continue
        # Single-character symbols
        if c in "{}(),;+*/%+-=<>:[].":
            tokens.append(Token("SYM", c, line))
            i += 1
            continue
        # Unknown character
        raise SyntaxError(f"Unknown character '{c}' at position {i}, line {line}")
    # Add EOF token
    tokens.append(Token("EOF", None, line))
    return tokens

# =======================
# EMITTER (Bytecode Generation)
# =======================
# Generates and manages bytecode, handles .pbc file format (PRIME ByteCode)

# FROZEN OPCODE TABLE - DO NOT MODIFY (version 0.1.2)
# Changing these would break existing bytecode files
OPCODES = (
    # Stack operations
    "PUSH_CONST",
    "LOAD",
    "STORE",
    "STORE_CONST",
    # I/O
    "PRINT",
    # Arithmetic
    "ADD", "SUB", "MUL", "DIV", "MOD",
    # Unary operators
    "UNARY_NEG", "NOT",
    # Logical operators
    "AND", "OR",
    # Comparison
    "CMP_EQ", "CMP_NE", "CMP_LT", "CMP_GT", "CMP_LE", "CMP_GE",
    # Control flow
    "JMP", "JMP_IF_FALSE",
    # Functions
    "CALL", "RET",
    # Object access
    "GET_ATTR", "CALL_ATTR",
    # Error handling
    "TRY", "THROW",
    # Termination
    "HALT",
)

# Create frozen mappings from opcode names to IDs and vice versa
OPCODE_TO_ID = {op: i for i, op in enumerate(OPCODES)}
ID_TO_OPCODE = {i: op for op, i in OPCODE_TO_ID.items()}

class Emitter:
    """
    Generates bytecode from parsed AST and handles .pbc file format.
    
    Responsibilities:
    - Emit bytecode instructions with arguments
    - Track function definitions and their entry points
    - Manage export declarations
    - Save/load bytecode in deterministic .pbc format
    - Generate temporary variable names
    
    .pbc File Format (PRIME ByteCode):
    ---------------------------------
    Header (9 bytes):
      - Magic: "PRMB" (4 bytes)
      - Version: 1 byte
      - Metadata length: 4 bytes (big-endian)
    
    Metadata (JSON):
      - functions: dict of function names to (address, parameter_list)
      - debug: list of (filename, line) for each instruction
      - filename: original source filename
      - exports: list of exported symbols
      - version: compiler version string
    
    Instructions:
      - For each instruction:
        - Opcode ID: 2 bytes (big-endian)
        - Argument length: 4 bytes (big-endian)
        - Argument JSON: variable length
    """
    
    def __init__(self, filename="<string>"):
        """Initialize a new Emitter with empty code."""
        self.code = []            # list of (op, arg) tuples
        self.functions = {}       # name -> (address, param_list)
        self.debug = []           # parallel list of (filename, line) for debugging
        self.filename = filename  # source filename for error messages
        self.exports = set()      # explicit exports recorded here
        self._temp_counter = 0    # counter for generating temporary variable names

    def emit(self, op, arg=None, loc=None):
        """
        Emit a bytecode instruction.
        
        Args:
            op: Opcode name (must be in OPCODE_TO_ID)
            arg: Argument value (will be JSON-serialized)
            loc: (filename, line) tuple for debugging
            
        Returns:
            Index of the emitted instruction (for later patching)
            
        Raises:
            ValueError: If opcode is unknown
        """
        if op not in OPCODE_TO_ID:
            raise ValueError(f"Unknown opcode '{op}'")
        self.code.append((op, arg))
        if loc is None:
            self.debug.append((self.filename, None))
        else:
            self.debug.append((self.filename, loc))
        return len(self.code)-1

    def patch(self, idx, arg):
        """
        Patch an instruction's argument at the given index.
        
        Used for forward jumps where target address isn't known yet.
        
        Args:
            idx: Instruction index to patch
            arg: New argument value
        """
        op, _ = self.code[idx]
        self.code[idx] = (op, arg)

    def new_temp(self):
        """
        Generate a new temporary variable name.
        
        Returns:
            String like "__tmp_N" where N is incremented each call
        """
        self._temp_counter += 1
        return f"__tmp_{self._temp_counter}"

    @staticmethod
    def _json_deterministic(obj):
        """
        Convert object to deterministic JSON string.
        
        Uses consistent ordering and minimal whitespace to ensure
        the same input always produces the same bytecode.
        
        Args:
            obj: Any JSON-serializable object
            
        Returns:
            Deterministic JSON string
        """
        return json.dumps(obj, separators=(",", ":"), sort_keys=True, ensure_ascii=False)

    def save_pbc(self, path):
        """
        Save bytecode to a .pbc file.
        
        Args:
            path: File path to save to
            
        Raises:
            IOError: If file cannot be written
        """
        # Prepare metadata
        meta = {
            "functions": self.functions,
            "debug": self.debug,
            "filename": self.filename,
            "exports": sorted(list(self.exports)),
            "version": VERSION
        }
        meta_json = self._json_deterministic(meta).encode("utf-8")
        
        # Write file
        with open(path, "wb") as f:
            # Header
            f.write(b"PRMB")  # Magic number
            f.write(struct.pack("B", BYTECODE_VERSION))  # Version
            f.write(struct.pack(">I", len(meta_json)))  # Metadata length
            
            # Metadata
            f.write(meta_json)
            
            # Instructions
            f.write(struct.pack(">I", len(self.code)))  # Instruction count
            for op, arg in self.code:
                opid = OPCODE_TO_ID[op]
                f.write(struct.pack(">H", opid))  # Opcode ID (2 bytes)
                arg_json = self._json_deterministic(arg).encode("utf-8")
                f.write(struct.pack(">I", len(arg_json)))  # Argument length
                f.write(arg_json)  # Argument data

    @staticmethod
    def load_pbc(path):
        """
        Load bytecode from a .pbc file.
        
        Args:
            path: File path to load from
            
        Returns:
            Tuple: (code, functions, debug, filename, exports, version)
            
        Raises:
            ValueError: If file is not a valid .pbc or version mismatch
            IOError: If file cannot be read
        """
        with open(path, "rb") as f:
            # Verify magic number
            magic = f.read(4)
            if magic != b"PRMB":
                raise ValueError("Not a valid PRIME PBC file (wrong magic number)")
            
            # Check version
            ver = struct.unpack("B", f.read(1))[0]
            if ver != BYTECODE_VERSION:
                raise ValueError(f"Unsupported PBC version: {ver} (expected {BYTECODE_VERSION})")
            
            # Read metadata
            meta_len = struct.unpack(">I", f.read(4))[0]
            meta_json = f.read(meta_len).decode("utf-8")
            meta = json.loads(meta_json)
            
            # Read instructions
            instr_count = struct.unpack(">I", f.read(4))[0]
            code = []
            for _ in range(instr_count):
                opid = struct.unpack(">H", f.read(2))[0]
                oplabel = ID_TO_OPCODE.get(opid, f"OP_{opid}")
                arg_len = struct.unpack(">I", f.read(4))[0]
                arg_json = f.read(arg_len).decode("utf-8")
                arg = json.loads(arg_json)
                code.append((oplabel, arg))
        
        # Extract metadata fields with defaults for backward compatibility
        functions = meta.get("functions", {})
        debug = meta.get("debug", [])
        filename = meta.get("filename", "<pbc>")
        exports = set(meta.get("exports", []))
        version = meta.get("version", "0.1.0")  # Default for older files
        
        return code, functions, debug, filename, exports, version

# =======================
# PARSER (Syntax Analysis → Bytecode)
# =======================
# Converts tokens into bytecode using recursive descent parsing

class Parser:
    """
    Recursive descent parser that converts tokens to bytecode.
    
    Grammar Overview:
    ---------------
    program      : statement* EOF
    statement    : export_block
                 | export_declaration
                 | variable_declaration
                 | assignment
                 | print_statement
                 | function_declaration
                 | if_statement
                 | return_statement
                 | attempt_statement
                 | throw_statement
                 | loop_statement
                 | break_statement
                 | continue_statement
                 | import_statement
                 | expression_statement
    
    expression   : logic_or
    logic_or     : logic_and ('or' logic_and)*
    logic_and    : compare ('and' compare)*
    compare      : add (('<'|'>'|'<='|'>='|'=='|'!=') add)*
    add          : mul (('+'|'-') mul)*
    mul          : unary (('*'|'/'|'%') unary)*
    unary        : ('-'|'not') primary
                 | primary
    primary      : NUM | STR | ID | '(' expression ')'
                 | 'true' | 'false' | 'null'
                 | list_literal | dict_literal
    
    Features:
    ---------
    - Short-circuit evaluation for 'and'/'or'
    - Explicit exports (export func, export let, export {a, b, c})
    - Loops (while, for, from-to)
    - Break/continue with loop stack
    - Dot notation for attribute access
    - List and dictionary literals
    - Error handling with attempt/catch
    """
    
    def __init__(self, tokens, filename="<string>"):
        """Initialize parser with token stream and filename."""
        self.tokens = tokens
        self.pos = 0  # Current position in token stream
        self.em = Emitter(filename=filename)
        self.loop_stack = []  # For tracking break/continue targets
        self.module_exports_declared = set()  # Export tracking
        self.seen_export_block = False  # Only one export block allowed
        self.consts = set()  # Track const variables for reassignment check

    def peek(self):
        """Return current token without consuming it."""
        return self.tokens[self.pos]

    def advance(self):
        """Consume and return current token, move to next."""
        t = self.tokens[self.pos]
        self.pos += 1
        return t

    def accept(self, type_, value=None):
        """
        Conditionally consume token if it matches type and value.
        
        Args:
            type_: Expected token type
            value: Optional expected token value
            
        Returns:
            Token if matched, None otherwise
        """
        if self.peek().type == type_ and (value is None or self.peek().value == value):
            return self.advance()
        return None

    def expect(self, type_, value=None):
        """
        Consume token, raising error if it doesn't match.
        
        Args:
            type_: Expected token type
            value: Optional expected token value
            
        Returns:
            Token if matched
            
        Raises:
            SyntaxError: If token doesn't match
        """
        tok = self.advance()
        if tok.type != type_ or (value is not None and tok.value != value):
            expected = f"{type_} '{value}'" if value else type_
            got = f"{tok.type} '{tok.value}'" if tok.value else tok.type
            raise SyntaxError(f"Expected {expected} at line {tok.line}, got {got}")
        return tok

    def cur_line(self):
        """Get line number of current token."""
        return self.peek().line

    def parse(self):
        """
        Parse entire token stream into bytecode.
        
        Returns:
            Tuple: (code, functions, debug, exports)
        """
        # Parse all top-level statements
        while self.peek().type != "EOF":
            self.statement()
        
        # Store exports metadata (union of explicit exports and module exports)
        self.em.exports = self.module_exports_declared.union(self.em.exports)
        
        # Add HALT instruction at end
        self.em.emit("HALT", None, loc=self.cur_line())
        
        return self.em.code, self.em.functions, self.em.debug, self.em.exports

    def statement(self):
        """Parse a single statement based on current token."""
        p = self.peek()
        
        # Export block: export { a, b, fn }
        if p.type == "KW" and p.value == "export" and self._peek_is_sym("{"):
            self.export_block()
            return
            
        # Export declaration: export func/let/const
        if p.type == "KW" and p.value == "export":
            self.export_declaration()
            return
            
        # Variable declarations and assignments
        if p.type == "KW" and p.value == "let":
            self.variable_declaration("let")
            return
        if p.type == "KW" and p.value == "const":
            self.variable_declaration("const")
            return
        if p.type == "KW" and p.value == "set":
            self.assignment()
            return
            
        # I/O
        if p.type == "KW" and p.value == "say":
            self.print_statement()
            return
            
        # Functions
        if p.type == "KW" and p.value == "func":
            self.func_decl(is_export=False)
            return
            
        # Control flow
        if p.type == "KW" and p.value == "if":
            self.if_stmt()
            return
        if p.type == "KW" and p.value == "return":
            self.return_statement()
            return
        if p.type == "KW" and p.value == "attempt":
            self.attempt_stmt()
            return
        if p.type == "KW" and p.value == "throw":
            self.throw_statement()
            return
            
        # Loops
        if p.type == "KW" and p.value == "loop":
            self.loop_stmt()
            return
        if p.type == "KW" and p.value == "for":  # 'for' is alias for 'loop in'
            self.for_loop_alias()
            return
        if p.type == "KW" and p.value == "break":
            self.break_statement()
            return
        if p.type == "KW" and p.value == "continue":
            self.continue_statement()
            return
            
        # Modules
        if p.type == "KW" and p.value == "import":
            self.import_stmt()
            return
            
        # Fallback: expression statement
        self.expression_statement()

    def _peek_is_sym(self, sym):
        """Check if next token is a specific symbol."""
        nxt = self.tokens[self.pos + 1] if (self.pos + 1) < len(self.tokens) else None
        return nxt is not None and nxt.type == "SYM" and nxt.value == sym

    def export_block(self):
        """Parse export block: export { a, b, c }"""
        if self.seen_export_block:
            raise SyntaxError("Duplicate export block (only one allowed per module)")
        self.seen_export_block = True
        
        p = self.expect("KW", "export")
        self.expect("SYM", "{")
        
        # Parse comma-separated list of identifiers
        while True:
            tok = self.expect("ID")
            self.module_exports_declared.add(tok.value)
            if self.peek().type == "SYM" and self.peek().value == ",":
                self.advance()
                continue
            break
            
        self.expect("SYM", "}")

    def export_declaration(self):
        """Parse export declaration: export func/let/const"""
        p = self.expect("KW", "export")
        nxt = self.peek()
        
        if nxt.type == "KW" and nxt.value == "func":
            self.func_decl(is_export=True)
            return
            
        if nxt.type == "KW" and nxt.value in ("let", "const"):
            kw = self.advance()  # consume let/const
            name = self.expect("ID").value
            self.expect("SYM", "=")
            self.expression()
            
            if kw.value == "const":
                self.em.emit("STORE_CONST", name, loc=p.line)
                self.consts.add(name)
            else:
                self.em.emit("STORE", name, loc=p.line)
                
            self.module_exports_declared.add(name)
            return
            
        raise SyntaxError("export must be followed by func or let/const or an export block")

    def variable_declaration(self, kind):
        """Parse variable declaration: let/const name [= expression]"""
        p = self.expect("KW", kind)
        name = self.expect("ID").value
        
        # Check if there's an initializer
        if self.accept("SYM", "="):
            self.expression()
        else:
            # Default to null if no initializer
            self.em.emit("PUSH_CONST", None, loc=p.line)
        
        if kind == "const":
            self.em.emit("STORE_CONST", name, loc=p.line)
            self.consts.add(name)
        else:
            self.em.emit("STORE", name, loc=p.line)

    def assignment(self):
        """Parse assignment: set name = expression"""
        p = self.expect("KW", "set")
        name = self.expect("ID").value
        
        # Check if variable exists (for better error messages)
        # This checks parser's tracked constants, but runtime will also catch it
        if name in self.consts:
            raise SyntaxError(f"Cannot reassign const '{name}' at line {p.line}")
        
        self.expect("SYM", "=")
        self.expression()
        self.em.emit("STORE", name, loc=p.line)

    def print_statement(self):
        """Parse print statement: say expression"""
        p = self.expect("KW", "say")
        self.expression()
        self.em.emit("PRINT", None, loc=p.line)

    def expression_statement(self):
        """Parse expression as statement (with optional semicolon)."""
        self.expression()
        if self.peek().type == "SYM" and self.peek().value == ";":
            self.advance()

    def func_decl(self, is_export=False):
        """Parse function declaration: func name(params) { body }"""
        p = self.expect("KW", "func")
        name = self.expect("ID").value
        
        # Parse parameter list
        self.expect("SYM", "(")
        params = []
        if not (self.peek().type == "SYM" and self.peek().value == ")"):
            params.append(self.expect("ID").value)
            while self.peek().type == "SYM" and self.peek().value == ",":
                self.advance()
                params.append(self.expect("ID").value)
        self.expect("SYM", ")")
        
        # Emit jump over function body (to be filled when called)
        jmp_idx = self.em.emit("JMP", None, loc=p.line)
        func_addr = len(self.em.code)
        
        # Parse function body
        self.block()
        
        # Implicit return None if no explicit return
        self.em.emit("PUSH_CONST", None, loc=p.line)
        self.em.emit("RET", None, loc=p.line)
        
        # Patch jump to skip function body
        after_idx = len(self.em.code)
        self.em.patch(jmp_idx, after_idx)
        
        # Record function in function table
        self.em.functions[name] = (func_addr, params)
        if is_export:
            self.module_exports_declared.add(name)

    def block(self):
        """Parse block: { statements }"""
        self.expect("SYM", "{")
        while not (self.peek().type == "SYM" and self.peek().value == "}"):
            self.statement()
        self.expect("SYM", "}")

    def if_stmt(self):
        """Parse if statement: if condition { then } [elif ...] [else { else }]"""
        p = self.expect("KW", "if")
        self.expression()  # condition
        
        # Jump if false to else/elif block (or after if)
        jmp_false_idx = self.em.emit("JMP_IF_FALSE", None, loc=p.line)
        
        # Then block
        self.block()
        
        # Jump over else/elif blocks
        jmp_end_idx = self.em.emit("JMP", None, loc=p.line)
        
        # Patch false jump to else/elif address
        else_addr = len(self.em.code)
        self.em.patch(jmp_false_idx, else_addr)
        
        # Handle else if chains and else
        while self.peek().type == "KW" and self.peek().value == "else":
            self.advance()  # consume 'else'
            
            if self.peek().type == "KW" and self.peek().value == "if":
                self.advance()  # consume 'if'
                # elif block
                self.expression()  # condition
                
                # Jump if false to next else/elif or after chain
                jmp_false_elif = self.em.emit("JMP_IF_FALSE", None, loc=self.cur_line())
                
                # Then block for elif
                self.block()
                
                # Jump to end after executing elif
                jmp_over_rest = self.em.emit("JMP", None, loc=self.cur_line())
                
                # Patch previous false jump to current elif address
                next_addr = len(self.em.code)
                self.em.patch(jmp_false_elif, next_addr)
                
                # Update end address for the chain
                end_addr = len(self.em.code)
                self.em.patch(jmp_end_idx, end_addr)
                jmp_end_idx = jmp_over_rest
                
            else:
                # Final else block
                self.block()
                break
        
        # Patch final end jump
        end_addr = len(self.em.code)
        self.em.patch(jmp_end_idx, end_addr)

    def return_statement(self):
        """Parse return statement: return expression"""
        p = self.expect("KW", "return")
        self.expression()
        self.em.emit("RET", None, loc=p.line)

    def attempt_stmt(self):
        """Parse attempt-catch statement: attempt { try } catch Error e { catch }"""
        p = self.expect("KW", "attempt")
        
        # Set up exception handler (address will be patched later)
        try_idx = self.em.emit("TRY", (None, None, None), loc=p.line)
        
        # Try block
        self.block()
        
        # Jump over catch block
        jmp_over_catch = self.em.emit("JMP", None, loc=p.line)
        
        # Catch clause
        self.expect("KW", "catch")
        
        # Parse error type
        if self.peek().type in ("ID", "KW"):
            err_type = self.advance().value
        else:
            raise SyntaxError("Expected error type after catch")
            
        # Optional catch variable
        catch_var = None
        if self.peek().type == "ID":
            catch_var = self.advance().value
            
        # Patch try instruction with catch handler address
        catch_addr = len(self.em.code)
        self.em.patch(try_idx, (catch_addr, err_type, catch_var))
        
        # Store caught error if variable provided
        if catch_var:
            self.em.emit("STORE", catch_var, loc=p.line)
            
        # Catch block
        self.block()
        
        # Patch jump over catch
        end_addr = len(self.em.code)
        self.em.patch(jmp_over_catch, end_addr)

    def throw_statement(self):
        """Parse throw statement: throw expression"""
        p = self.expect("KW", "throw")
        self.expression()
        self.em.emit("THROW", None, loc=p.line)

    def loop_stmt(self):
        """Parse loop statement: loop [while condition | var from expr to expr | var in expr] { body }"""
        p = self.expect("KW", "loop")
        
        # while loop: loop while condition { body }
        if self.peek().type == "KW" and self.peek().value == "while":
            self.while_loop(p)
            return
            
        # Numeric range loop: loop var from expr to expr { body }
        if self.peek().type == "ID":
            varname = self.advance().value
            if self.peek().type == "KW" and self.peek().value == "from":
                self.numeric_range_loop(p, varname)
                return
                
        # Collection iteration: loop var in expr { body }
        if self.peek().type == "KW" and self.peek().value == "in":
            self.advance()
            self.loop_in_stmt(varname)
            return
            
        raise SyntaxError("Invalid loop syntax")

    def while_loop(self, p):
        """Parse while loop: loop while condition { body }"""
        self.advance()  # consume 'while'
        self.expression()  # condition
        
        loop_start = len(self.em.code)
        jmp_false_idx = self.em.emit("JMP_IF_FALSE", None, loc=p.line)
        
        # Setup loop context for break/continue
        ctx = {"breaks": [], "continues": []}
        self.loop_stack.append(ctx)
        
        # Loop body
        self.block()
        
        # Patch continue jumps to here (just before condition check)
        cont_addr = len(self.em.code)
        for ci in ctx["continues"]:
            self.em.patch(ci, cont_addr)
            
        # Jump back to condition check
        self.em.emit("JMP", loop_start, loc=p.line)
        
        # Patch break jumps and condition false jump to here
        end_addr = len(self.em.code)
        for bi in ctx["breaks"]:
            self.em.patch(bi, end_addr)
        self.em.patch(jmp_false_idx, end_addr)
        
        self.loop_stack.pop()

    def numeric_range_loop(self, p, varname):
        """Parse numeric range loop: loop var from start to end { body }"""
        self.expect("KW", "from")
        self.expression()  # start value
        self.em.emit("STORE", varname, loc=p.line)
        
        self.expect("KW", "to")
        self.expression()  # end value
        
        # Store end value in temporary variable
        tmp_end = self.em.new_temp()
        self.em.emit("STORE", tmp_end, loc=p.line)
        
        loop_start = len(self.em.code)
        
        # Check if var <= end
        self.em.emit("LOAD", varname, loc=p.line)
        self.em.emit("LOAD", tmp_end, loc=p.line)
        self.em.emit("CMP_LE", None, loc=p.line)
        jmp_false_idx = self.em.emit("JMP_IF_FALSE", None, loc=p.line)
        
        # Setup loop context
        ctx = {"breaks": [], "continues": []}
        self.loop_stack.append(ctx)
        
        # Loop body
        self.block()
        
        # Patch continue jumps
        cont_addr = len(self.em.code)
        for ci in ctx["continues"]:
            self.em.patch(ci, cont_addr)
            
        # Increment loop variable
        self.em.emit("LOAD", varname, loc=p.line)
        self.em.emit("PUSH_CONST", 1, loc=p.line)
        self.em.emit("ADD", None, loc=p.line)
        self.em.emit("STORE", varname, loc=p.line)
        
        # Jump back to condition check
        self.em.emit("JMP", loop_start, loc=p.line)
        
        # Patch break jumps and condition false jump
        end_addr = len(self.em.code)
        for bi in ctx["breaks"]:
            self.em.patch(bi, end_addr)
        self.em.patch(jmp_false_idx, end_addr)
        
        self.loop_stack.pop()

    def loop_in_stmt(self, varname):
        """Parse collection iteration: loop var in collection { body }"""
        p = self.cur_line()
        self.expression()  # collection
        
        # Store collection in temporary variable
        iter_temp = self.em.new_temp()
        idx_temp = self.em.new_temp()
        self.em.emit("STORE", iter_temp, loc=p)
        
        # Initialize index
        self.em.emit("PUSH_CONST", 0, loc=p)
        self.em.emit("STORE", idx_temp, loc=p)
        
        loop_start = len(self.em.code)
        
        # Check if index < len(collection)
        self.em.emit("LOAD", idx_temp, loc=p)
        self.em.emit("LOAD", iter_temp, loc=p)
        self.em.emit("CALL", ("len", 1), loc=p)
        self.em.emit("CMP_LT", None, loc=p)
        jmp_false_idx = self.em.emit("JMP_IF_FALSE", None, loc=p)
        
        # Get current element: collection[index]
        self.em.emit("LOAD", iter_temp, loc=p)
        self.em.emit("LOAD", idx_temp, loc=p)
        self.em.emit("CALL", ("get", 2), loc=p)
        self.em.emit("STORE", varname, loc=p)
        
        # Setup loop context
        ctx = {"breaks": [], "continues": []}
        self.loop_stack.append(ctx)
        
        # Loop body
        self.block()
        
        # Patch continue jumps
        cont_addr = len(self.em.code)
        for ci in ctx["continues"]:
            self.em.patch(ci, cont_addr)
            
        # Increment index
        self.em.emit("LOAD", idx_temp, loc=p)
        self.em.emit("PUSH_CONST", 1, loc=p)
        self.em.emit("ADD", None, loc=p)
        self.em.emit("STORE", idx_temp, loc=p)
        
        # Jump back to condition check
        self.em.emit("JMP", loop_start, loc=p)
        
        # Patch break jumps and condition false jump
        end_addr = len(self.em.code)
        for bi in ctx["breaks"]:
            self.em.patch(bi, end_addr)
        self.em.patch(jmp_false_idx, end_addr)
        
        self.loop_stack.pop()

    def for_loop_alias(self):
        """Parse for loop (alias for loop in): for var in collection { body }"""
        self.advance()  # consume 'for'
        varname = self.expect("ID").value
        self.expect("KW", "in")
        self.loop_in_stmt(varname)

    def break_statement(self):
        """Parse break statement: break"""
        p = self.expect("KW", "break")
        if not self.loop_stack:
            raise SyntaxError("break outside loop")
        idx = self.em.emit("JMP", None, loc=p.line)
        self.loop_stack[-1]["breaks"].append(idx)

    def continue_statement(self):
        """Parse continue statement: continue"""
        p = self.expect("KW", "continue")
        if not self.loop_stack:
            raise SyntaxError("continue outside loop")
        idx = self.em.emit("JMP", None, loc=p.line)
        self.loop_stack[-1]["continues"].append(idx)

    def import_stmt(self):
        """Parse import statement: import module [as alias]"""
        p = self.expect("KW", "import")
        
        # Module name
        if self.peek().type not in ("ID", "KW"):
            raise SyntaxError("Expected module name")
        name = self.advance().value
        
        # Optional alias
        alias = None
        if self.peek().type == "KW" and self.peek().value == "as":
            self.advance()
            alias = self.expect("ID").value
            
        # Emit import call
        self.em.emit("PUSH_CONST", name, loc=p.line)
        self.em.emit("PUSH_CONST", alias, loc=p.line)
        self.em.emit("CALL", ("__import__", 2), loc=p.line)

    # =======================
    # EXPRESSION PARSING
    # =======================
    
    def expression(self):
        """Parse expression (entry point)."""
        self.logic_or()

    def logic_or(self):
        """Parse logical OR with short-circuit evaluation."""
        self.logic_and()
        while self.peek().type == "KW" and self.peek().value == "or":
            kw = self.advance()
            
            # Short-circuit: if left is true, skip evaluating right
            jmp_eval_right = self.em.emit("JMP_IF_FALSE", None, loc=kw.line)
            self.em.emit("PUSH_CONST", True, loc=kw.line)
            jmp_end = self.em.emit("JMP", None, loc=kw.line)
            
            eval_right_addr = len(self.em.code)
            self.em.patch(jmp_eval_right, eval_right_addr)
            
            self.logic_and()
            
            end_addr = len(self.em.code)
            self.em.patch(jmp_end, end_addr)

    def logic_and(self):
        """Parse logical AND with short-circuit evaluation."""
        self.compare()
        while self.peek().type == "KW" and self.peek().value == "and":
            kw = self.advance()
            
            # Short-circuit: if left is false, skip evaluating right
            jmp_false = self.em.emit("JMP_IF_FALSE", None, loc=kw.line)
            self.compare()
            jmp_end = self.em.emit("JMP", None, loc=kw.line)
            
            false_addr = len(self.em.code)
            self.em.patch(jmp_false, false_addr)
            self.em.emit("PUSH_CONST", False, loc=kw.line)
            
            end_addr = len(self.em.code)
            self.em.patch(jmp_end, end_addr)

    def compare(self):
        """Parse comparison operators: < > <= >= == !="""
        self.add()
        while self.peek().type == "SYM" and self.peek().value in ("<", ">", "<=", ">=", "==", "!="):
            op = self.advance().value
            self.add()
            
            # Emit appropriate comparison opcode
            if op == "<":
                self.em.emit("CMP_LT", None, loc=self.cur_line())
            elif op == ">":
                self.em.emit("CMP_GT", None, loc=self.cur_line())
            elif op == "<=":
                self.em.emit("CMP_LE", None, loc=self.cur_line())
            elif op == ">=":
                self.em.emit("CMP_GE", None, loc=self.cur_line())
            elif op == "==":
                self.em.emit("CMP_EQ", None, loc=self.cur_line())
            elif op == "!=":
                self.em.emit("CMP_NE", None, loc=self.cur_line())

    def add(self):
        """Parse addition and subtraction: + -"""
        self.mul()
        while self.peek().type == "SYM" and self.peek().value in ("+", "-"):
            op = self.advance().value
            self.mul()
            self.em.emit("ADD" if op == "+" else "SUB", None, loc=self.cur_line())

    def mul(self):
        """Parse multiplication, division, and modulo: * / %"""
        self.unary()
        while self.peek().type == "SYM" and self.peek().value in ("*", "/", "%"):
            op = self.advance().value
            self.unary()
            if op == "*":
                self.em.emit("MUL", None, loc=self.cur_line())
            elif op == "/":
                self.em.emit("DIV", None, loc=self.cur_line())
            else:
                self.em.emit("MOD", None, loc=self.cur_line())

    def unary(self):
        """Parse unary operators: - (negation), not"""
        if self.peek().type == "SYM" and self.peek().value == "-":
            self.advance()
            self.primary()
            self.em.emit("UNARY_NEG", None, loc=self.cur_line())
            return
        if self.peek().type == "KW" and self.peek().value == "not":
            self.advance()
            self.primary()
            self.em.emit("NOT", None, loc=self.cur_line())
            return
        self.primary()

    def primary(self):
        """Parse primary expressions: literals, identifiers, parentheses, lists, dicts."""
        t = self.peek()
        
        # Numbers
        if t.type == "NUM":
            self.advance()
            self.em.emit("PUSH_CONST", t.value, loc=t.line)
            return self._parse_dot_chain()
            
        # Strings
        if t.type == "STR":
            self.advance()
            self.em.emit("PUSH_CONST", t.value, loc=t.line)
            return self._parse_dot_chain()
            
        # Boolean and null literals
        if t.type == "KW" and t.value in ("true", "false", "null"):
            self.advance()
            v = True if t.value == "true" else False if t.value == "false" else None
            self.em.emit("PUSH_CONST", v, loc=t.line)
            return self._parse_dot_chain()
            
        # Identifiers (variables, functions)
        if t.type == "ID":
            ident = self.advance().value
            self.em.emit("LOAD", ident, loc=t.line)
            return self._parse_trailers()
            
        # Parenthesized expressions
        if t.type == "SYM" and t.value == "(":
            self.advance()
            self.expression()
            self.expect("SYM", ")")
            return self._parse_dot_chain()
            
        # List literals: [expr, expr, ...]
        if t.type == "SYM" and t.value == "[":
            self.advance()
            elems = []
            if not (self.peek().type == "SYM" and self.peek().value == "]"):
                self.expression()
                elems.append(None)  # placeholder for count
                while self.peek().type == "SYM" and self.peek().value == ",":
                    self.advance()
                    self.expression()
                    elems.append(None)
            self.expect("SYM", "]")
            count = len(elems)
            self.em.emit("CALL", ("__mklist__", count), loc=t.line)
            return self._parse_dot_chain()
            
        # Dictionary literals: {key: value, ...}
        if t.type == "SYM" and t.value == "{":
            self.advance()
            items = []
            if not (self.peek().type == "SYM" and self.peek().value == "}"):
                # Parse key-value pairs
                self.expression()  # key
                self.expect("SYM", ":")
                self.expression()  # value
                items.append(None)  # placeholder
                while self.peek().type == "SYM" and self.peek().value == ",":
                    self.advance()
                    self.expression()
                    self.expect("SYM", ":")
                    self.expression()
                    items.append(None)
            self.expect("SYM", "}")
            count = len(items) * 2  # key + value for each pair
            self.em.emit("CALL", ("__mkdict__", count), loc=t.line)
            return self._parse_dot_chain()
            
        raise SyntaxError(f"Unexpected token {t}")

    def _parse_trailers(self):
        """Parse function calls, indexing, and dot chains after an identifier."""
        while True:
            # Function call: ident(args...)
            if self.peek().type == "SYM" and self.peek().value == "(":
                self.advance()
                argc = 0
                if not (self.peek().type == "SYM" and self.peek().value == ")"):
                    self.expression()
                    argc += 1
                    while self.peek().type == "SYM" and self.peek().value == ",":
                        self.advance()
                        self.expression()
                        argc += 1
                self.expect("SYM", ")")
                self.em.emit("CALL", (None, argc), loc=self.cur_line())
                
            # Indexing: ident[index]
            elif self.peek().type == "SYM" and self.peek().value == "[":
                self.advance()
                self.expression()
                self.expect("SYM", "]")
                self.em.emit("CALL", ("get", 2), loc=self.cur_line())
                
            # Dot notation: ident.attr or ident.method(args)
            elif self.peek().type == "SYM" and self.peek().value == ".":
                self.advance()
                attr = self.expect("ID").value
                
                # Method call: obj.method(args)
                if self.peek().type == "SYM" and self.peek().value == "(":
                    self.advance()
                    argc = 0
                    if not (self.peek().type == "SYM" and self.peek().value == ")"):
                        self.expression()
                        argc += 1
                        while self.peek().type == "SYM" and self.peek().value == ",":
                            self.advance()
                            self.expression()
                            argc += 1
                    self.expect("SYM", ")")
                    self.em.emit("CALL_ATTR", (attr, argc), loc=self.cur_line())
                else:
                    # Attribute access
                    self.em.emit("GET_ATTR", attr, loc=self.cur_line())
            else:
                break

    def _parse_dot_chain(self):
        """Parse dot chains after non-identifier primaries."""
        return self._parse_trailers()

# =======================
# VIRTUAL MACHINE
# =======================
# Executes bytecode with stack-based architecture

class VMError(Exception):
    """Base class for VM runtime errors."""
    pass

class ErrorObject:
    """
    Represents an error/exception in PRIME.
    
    Properties:
    - type: Error type name (e.g., "RuntimeError", "NameError")
    - message: Human-readable error message
    - trace: Stack trace as list of (function_name, filename, line)
    """
    
    def __init__(self, type_name, message=None, trace=None):
        self.type = type_name
        self.message = message if message is not None else ""
        self.trace = trace or []

    def __repr__(self):
        return f"<Error {self.type}: {self.message}>"

class Frame:
    """
    Represents a call frame in the VM.
    
    Each function call creates a new frame with its own:
    - Local variables
    - Constant declarations (const variables)
    - Return address
    - Function name for debugging
    - Entry instruction pointer
    """
    
    def __init__(self, return_ip=None, params=None, func_name=None, entry_ip=None):
        self.vars = {} if params is None else dict(params)
        self.consts = set()  # Track const variables in this frame
        self.return_ip = return_ip  # Instruction to return to
        self.func_name = func_name  # Function name for stack traces
        self.entry_ip = entry_ip  # Starting IP for this frame

class PrimeVM:
    """
    PRIME Virtual Machine.
    
    Stack-based architecture with:
    - Instruction pointer (ip)
    - Value stack
    - Call frames
    - Exception handling stack
    - Built-in functions library
    """
    
    def __init__(self, code, functions, debug, exports=None, cwd=None):
        """
        Initialize VM with bytecode.
        
        Args:
            code: List of (opcode, arg) instructions
            functions: Dict of function_name -> (address, param_list)
            debug: List of (filename, line) for each instruction
            exports: Set of exported symbols
            cwd: Current working directory for imports
        """
        self.code = code
        self.functions = functions
        self.debug = debug
        self.exports = exports or set()
        self.ip = 0  # Instruction pointer
        self.stack = []  # Value stack
        self.frames = [Frame(return_ip=None, params={}, func_name="<global>", entry_ip=0)]
        self.exception_stack = []  # For try-catch blocks
        self.builtins = self._make_builtins()  # Standard library
        
        # Error type hierarchy (for exception matching)
        self.error_parents = {
            # Core errors
            "NameError": "RuntimeError",
            "AttributeError": "RuntimeError",
            "TypeError": "RuntimeError",
            "ValueError": "RuntimeError",
            "StateError": "RuntimeError",
            # Arithmetic errors
            "ArithmeticError": "RuntimeError",
            "DivideByZeroError": "ArithmeticError",
            # I/O errors
            "IOError": "RuntimeError",
            "FileError": "IOError",
            "PermissionError": "IOError",
            "NotFoundError": "IOError",
            # System errors
            "ImportError": "RuntimeError",
            # Control flow errors
            "ControlError": "Error",
            "BreakError": "ControlError",
            "ContinueError": "ControlError",
            # Fatal errors
            "FatalError": None,
            # Base errors
            "RuntimeError": "Error",
        }
        
        self.cwd = cwd or os.getcwd()

    def current_frame_depth(self):
        """Return current call stack depth (0 = global frame)."""
        return len(self.frames) - 1

    def push_frame(self, return_ip, param_bindings, func_name=None, entry_ip=None):
        """Push a new call frame onto the stack."""
        self.frames.append(Frame(return_ip=return_ip, params=param_bindings, 
                               func_name=func_name, entry_ip=entry_ip))

    def pop_frame(self):
        """Pop the current call frame (except global frame)."""
        if len(self.frames) <= 1:
            return None
        self.frames.pop()

    def lookup_var(self, name):
        """
        Look up a variable by name in current scope chain.
        
        Searches from innermost to outermost frame.
        
        Args:
            name: Variable name to look up
            
        Returns:
            Variable value if found
            
        Raises:
            ErrorObject(NameError) if variable not found
        """
        for f in reversed(self.frames):
            if name in f.vars:
                return f.vars[name]
        
        # Variable not found - raise NameError with location info
        if self.ip - 1 < len(self.debug):
            filename, line = self.debug[self.ip - 1]
            # Build helpful error message
            err_msg = f"Undefined variable '{name}'"
            if filename:
                err_msg += f" at {filename}"
            if line:
                err_msg += f":{line}"
            
            # Suggest similar variables if any
            all_vars = set()
            for f in self.frames:
                all_vars.update(f.vars.keys())
            
            similar = []
            for var in all_vars:
                if var.startswith(name[:1]) or name.startswith(var[:1]):
                    similar.append(var)
            
            if similar:
                err_msg += f". Did you mean: {', '.join(similar[:3])}?"
            
            err = ErrorObject("NameError", err_msg, trace=self._build_trace())
            self._raise_error(err)
        else:
            err = ErrorObject("NameError", f"Undefined variable: {name}", trace=self._build_trace())
            self._raise_error(err)

    def store_var(self, name, value):
        """
        Store a value in a variable.
        
        Searches for existing variable declaration in scope chain.
        If not found, creates in current frame.
        
        Args:
            name: Variable name
            value: Value to store
            
        Raises:
            ErrorObject(TypeError) if trying to reassign const
        """
        for f in reversed(self.frames):
            if name in f.vars:
                # Check if it's a const
                if hasattr(f, 'consts') and name in f.consts:
                    err = ErrorObject("TypeError", f"Cannot reassign const '{name}'", 
                                    trace=self._build_trace())
                    self._raise_error(err)
                    return
                f.vars[name] = value
                return
        # New variable in current frame
        self.frames[-1].vars[name] = value

    def store_const(self, name, value):
        """
        Store a constant value (cannot be reassigned).
        
        Args:
            name: Constant name
            value: Value to store
            
        Raises:
            ErrorObject(TypeError) if constant already exists
        """
        for f in reversed(self.frames):
            if name in f.vars:
                err = ErrorObject("TypeError", f"Cannot reassign const '{name}'", 
                                trace=self._build_trace())
                self._raise_error(err)
                return
        self.frames[-1].vars[name] = value
        self.frames[-1].consts.add(name)

    def error_matches(self, errobj: ErrorObject, handler_type: str):
        """
        Check if an error matches a handler type (supports inheritance).
        
        Args:
            errobj: Error object
            handler_type: Type to check against
            
        Returns:
            True if errobj is instance of handler_type (considering hierarchy)
        """
        cur = errobj.type
        while True:
            if cur == handler_type:
                return True
            parent = self.error_parents.get(cur, None)
            if parent is None:
                # Special case: "Error" matches any error type
                return handler_type == "Error" and cur is not None
            cur = parent

    def _build_trace(self):
        """
        Build stack trace from current call frames.
        
        Returns:
            List of (function_name, filename, line) tuples
        """
        trace = []
        for frame in reversed(self.frames):
            func = frame.func_name or "<anon>"
            line = None
            filename = None
            if frame.entry_ip is not None and 0 <= frame.entry_ip < len(self.debug):
                filename, line = self.debug[frame.entry_ip]
            trace.append((func, filename, line))
        return trace

    def _make_builtins(self):
        """
        Create and return the standard library of built-in functions.
        
        Returns:
            Dictionary mapping function names to callable objects
        """
        # =======================
        # I/O OPERATIONS
        # =======================
        
        def bw_say(*args):
            """Print arguments to stdout separated by spaces."""
            print(*args)
            return None
        
        def bw_read(prompt=None):
            """Read input from user with optional prompt."""
            try:
                if prompt is None:
                    return input()
                else:
                    return input(str(prompt))
            except EOFError:
                return ""
        
        # =======================
        # ERROR CONSTRUCTORS
        # =======================
        
        def make_error_ctor(type_name):
            """Factory function to create error constructors."""
            def ctor(msg=None):
                return ErrorObject(type_name, msg)
            return ctor
        
        # =======================
        # COLLECTION OPERATIONS
        # =======================
        
        def bw_len(x):
            """Return length of collection or string."""
            try:
                return len(x)
            except Exception as e:
                raise
        
        def bw_get(coll, idx):
            """Get element at index/key from collection."""
            try:
                return coll[idx]
            except IndexError:
                err = ErrorObject("ValueError", f"Index {idx} out of range", trace=[])
                raise err
            except KeyError:
                err = ErrorObject("KeyError", f"Key {idx} not found", trace=[])
                raise err
            except TypeError:
                err = ErrorObject("TypeError", f"Cannot index object of type {type(coll).__name__}", trace=[])
                raise err
        
        # =======================
        # FILE SYSTEM OPERATIONS
        # =======================
        
        def fs_read(path):
            """Read entire file as string."""
            try:
                with open(path, "r", encoding="utf-8") as f:
                    return f.read()
            except FileNotFoundError:
                err = ErrorObject("NotFoundError", f"File not found: {path}", trace=[])
                raise err
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied: {path}", trace=[])
                raise err
            except IsADirectoryError:
                err = ErrorObject("IOError", f"'{path}' is a directory", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to read '{path}': {str(e)}", trace=[])
                raise err
        
        def fs_write(path, data):
            """Write string data to file (overwrites existing)."""
            try:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(str(data))
                    return None
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied: {path}", trace=[])
                raise err
            except IsADirectoryError:
                err = ErrorObject("IOError", f"'{path}' is a directory", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to write '{path}': {str(e)}", trace=[])
                raise err
        
        def fs_append(path, data):
            """Append string data to file."""
            try:
                with open(path, "a", encoding="utf-8") as f:
                    f.write(str(data))
                    return None
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied: {path}", trace=[])
                raise err
            except IsADirectoryError:
                err = ErrorObject("IOError", f"'{path}' is a directory", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to append to '{path}': {str(e)}", trace=[])
                raise err
        
        def fs_readlines(path):
            """Read file as list of lines."""
            try:
                with open(path, "r", encoding="utf-8") as f:
                    return f.readlines()
            except FileNotFoundError:
                err = ErrorObject("NotFoundError", f"File not found: {path}", trace=[])
                raise err
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied: {path}", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to read '{path}': {str(e)}", trace=[])
                raise err
        
        def fs_exists(path):
            """Check if file or directory exists."""
            return os.path.exists(path)
        
        def fs_isdir(path):
            """Check if path is a directory."""
            return os.path.isdir(path)
        
        def fs_isfile(path):
            """Check if path is a regular file."""
            return os.path.isfile(path)
        
        def fs_listdir(path="."):
            """List directory contents."""
            try:
                return os.listdir(path)
            except FileNotFoundError:
                err = ErrorObject("NotFoundError", f"Directory not found: {path}", trace=[])
                raise err
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied: {path}", trace=[])
                raise err
            except NotADirectoryError:
                err = ErrorObject("IOError", f"'{path}' is not a directory", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to list '{path}': {str(e)}", trace=[])
                raise err
        
        def fs_mkdir(path):
            """Create directory."""
            try:
                os.makedirs(path, exist_ok=True)
                return None
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied: {path}", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to create directory '{path}': {str(e)}", trace=[])
                raise err
        
        def fs_remove(path):
            """Remove file."""
            try:
                os.remove(path)
                return None
            except FileNotFoundError:
                err = ErrorObject("NotFoundError", f"File not found: {path}", trace=[])
                raise err
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied: {path}", trace=[])
                raise err
            except IsADirectoryError:
                err = ErrorObject("IOError", f"'{path}' is a directory, use fs.rmdir", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to remove '{path}': {str(e)}", trace=[])
                raise err
        
        def fs_rmdir(path):
            """Remove empty directory."""
            try:
                os.rmdir(path)
                return None
            except FileNotFoundError:
                err = ErrorObject("NotFoundError", f"Directory not found: {path}", trace=[])
                raise err
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied: {path}", trace=[])
                raise err
            except OSError as e:
                err = ErrorObject("IOError", f"Failed to remove directory '{path}': {str(e)}", trace=[])
                raise err
        
        def fs_rename(src, dst):
            """Rename or move file/directory."""
            try:
                os.rename(src, dst)
                return None
            except FileNotFoundError:
                err = ErrorObject("NotFoundError", f"Source not found: {src}", trace=[])
                raise err
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to rename '{src}' to '{dst}': {str(e)}", trace=[])
                raise err
        
        def fs_copy(src, dst):
            """Copy file."""
            try:
                shutil.copy2(src, dst)
                return None
            except FileNotFoundError:
                err = ErrorObject("NotFoundError", f"Source not found: {src}", trace=[])
                raise err
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to copy '{src}' to '{dst}': {str(e)}", trace=[])
                raise err
        
        def fs_getsize(path):
            """Get file size in bytes."""
            try:
                return os.path.getsize(path)
            except FileNotFoundError:
                err = ErrorObject("NotFoundError", f"File not found: {path}", trace=[])
                raise err
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied: {path}", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to get size of '{path}': {str(e)}", trace=[])
                raise err
        
        def fs_getmtime(path):
            """Get file modification time (seconds since epoch)."""
            try:
                return os.path.getmtime(path)
            except FileNotFoundError:
                err = ErrorObject("NotFoundError", f"File not found: {path}", trace=[])
                raise err
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied: {path}", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to get modification time of '{path}': {str(e)}", trace=[])
                raise err
        
        # =======================
        # TIME OPERATIONS
        # =======================
        
        def t_now():
            """Return current date/time as ISO 8601 string."""
            return datetime.datetime.now().isoformat()
        
        def t_timestamp():
            """Return current timestamp (seconds since epoch)."""
            return time.time()
        
        def t_sleep(seconds):
            """Sleep for specified number of seconds."""
            time.sleep(float(seconds))
            return None
        
        def t_strftime(format_str, timestamp=None):
            """Format timestamp as string (defaults to current time)."""
            if timestamp is None:
                timestamp = time.time()
            return time.strftime(str(format_str), time.localtime(float(timestamp)))
        
        def t_parse(date_str, format_str=None):
            """Parse date string to timestamp."""
            try:
                if format_str:
                    dt = datetime.datetime.strptime(str(date_str), str(format_str))
                else:
                    # Try common formats
                    for fmt in ["%Y-%m-%d", "%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S"]:
                        try:
                            dt = datetime.datetime.strptime(str(date_str), fmt)
                            break
                        except ValueError:
                            continue
                    else:
                        raise ValueError("Cannot parse date string")
                return dt.timestamp()
            except Exception as e:
                err = ErrorObject("ValueError", f"Failed to parse date '{date_str}': {str(e)}", trace=[])
                raise err
        
        # =======================
        # MATHEMATICAL OPERATIONS
        # =======================
        
        def math_abs(x):
            """Return absolute value."""
            return abs(float(x))
        
        def math_floor(x):
            """Return floor of number."""
            return math.floor(float(x))
        
        def math_ceil(x):
            """Return ceiling of number."""
            return math.ceil(float(x))
        
        def math_round(x, ndigits=0):
            """Round number to given decimal places."""
            return round(float(x), int(ndigits))
        
        def math_sqrt(x):
            """Return square root."""
            try:
                return math.sqrt(float(x))
            except ValueError:
                err = ErrorObject("ValueError", f"Math domain error: sqrt({x})", trace=[])
                raise err
        
        def math_pow(x, y):
            """Return x raised to power y."""
            return math.pow(float(x), float(y))
        
        def math_exp(x):
            """Return e raised to power x."""
            return math.exp(float(x))
        
        def math_log(x, base=math.e):
            """Return logarithm of x with given base (default e)."""
            try:
                if base == math.e:
                    return math.log(float(x))
                else:
                    return math.log(float(x), float(base))
            except ValueError:
                err = ErrorObject("ValueError", f"Math domain error: log({x})", trace=[])
                raise err
        
        def math_sin(x):
            """Return sine of x radians."""
            return math.sin(float(x))
        
        def math_cos(x):
            """Return cosine of x radians."""
            return math.cos(float(x))
        
        def math_tan(x):
            """Return tangent of x radians."""
            return math.tan(float(x))
        
        def math_asin(x):
            """Return arc sine in radians."""
            try:
                return math.asin(float(x))
            except ValueError:
                err = ErrorObject("ValueError", f"Math domain error: asin({x})", trace=[])
                raise err
        
        def math_acos(x):
            """Return arc cosine in radians."""
            try:
                return math.acos(float(x))
            except ValueError:
                err = ErrorObject("ValueError", f"Math domain error: acos({x})", trace=[])
                raise err
        
        def math_atan(x):
            """Return arc tangent in radians."""
            return math.atan(float(x))
        
        def math_atan2(y, x):
            """Return atan(y / x) in radians."""
            return math.atan2(float(y), float(x))
        
        # =======================
        # RANDOM OPERATIONS
        # =======================
        
        def random_random():
            """Return random float in [0.0, 1.0)."""
            return random.random()
        
        def random_randint(a, b):
            """Return random integer in [a, b] inclusive."""
            return random.randint(int(a), int(b))
        
        def random_uniform(a, b):
            """Return random float in [a, b)."""
            return random.uniform(float(a), float(b))
        
        def random_choice(seq):
            """Return random element from sequence."""
            try:
                return random.choice(seq)
            except IndexError:
                err = ErrorObject("ValueError", "Cannot choose from empty sequence", trace=[])
                raise err
        
        def random_shuffle(seq):
            """Shuffle sequence in place."""
            random.shuffle(seq)
            return seq
        
        def random_seed(seed=None):
            """Initialize random number generator."""
            random.seed(seed)
            return None
        
        # =======================
        # STRING OPERATIONS
        # =======================
        
        def str_split(s, delim=None):
            """Split string by delimiter (whitespace if None)."""
            return s.split(delim) if delim else s.split()
        
        def str_upper(s):
            """Convert string to uppercase."""
            return s.upper()
        
        def str_lower(s):
            """Convert string to lowercase."""
            return s.lower()
        
        def str_strip(s, chars=None):
            """Strip leading/trailing characters (whitespace if None)."""
            return s.strip(chars) if chars else s.strip()
        
        def str_lstrip(s, chars=None):
            """Strip leading characters (whitespace if None)."""
            return s.lstrip(chars) if chars else s.lstrip()
        
        def str_rstrip(s, chars=None):
            """Strip trailing characters (whitespace if None)."""
            return s.rstrip(chars) if chars else s.rstrip()
        
        def str_replace(s, old, new, count=-1):
            """Replace occurrences of substring."""
            return s.replace(str(old), str(new), int(count))
        
        def str_find(s, sub, start=0, end=None):
            """Find substring, return index or -1 if not found."""
            return s.find(str(sub), int(start), end)
        
        def str_rfind(s, sub, start=0, end=None):
            """Find substring from right, return index or -1 if not found."""
            return s.rfind(str(sub), int(start), end)
        
        def str_startswith(s, prefix):
            """Check if string starts with prefix."""
            return s.startswith(str(prefix))
        
        def str_endswith(s, suffix):
            """Check if string ends with suffix."""
            return s.endswith(str(suffix))
        
        def str_join(sep, iterable):
            """Join iterable of strings with separator."""
            return str(sep).join(str(x) for x in iterable)
        
        def str_format(s, *args):
            """Format string with positional arguments."""
            return s.format(*args)
        
        def str_isalpha(s):
            """Check if all characters are alphabetic."""
            return s.isalpha()
        
        def str_isdigit(s):
            """Check if all characters are digits."""
            return s.isdigit()
        
        def str_isalnum(s):
            """Check if all characters are alphanumeric."""
            return s.isalnum()
        
        def str_isspace(s):
            """Check if all characters are whitespace."""
            return s.isspace()
        
        # =======================
        # TYPE CONVERSION
        # =======================
        
        def to_str(x):
            """Convert value to string."""
            return str(x)
        
        def to_int(x):
            """Convert value to integer."""
            try:
                return int(x)
            except (ValueError, TypeError):
                err = ErrorObject("ValueError", f"Cannot convert '{x}' to integer", trace=[])
                raise err
        
        def to_float(x):
            """Convert value to float."""
            try:
                return float(x)
            except (ValueError, TypeError):
                err = ErrorObject("ValueError", f"Cannot convert '{x}' to float", trace=[])
                raise err
        
        def to_bool(x):
            """Convert value to boolean."""
            return bool(x)
        
        # =======================
        # SYSTEM OPERATIONS
        # =======================
        
        def sys_argv():
            """Return command line arguments (as list of strings)."""
            # Note: sys.argv[0] is the script name
            return sys.argv
        
        def sys_exit(code=0):
            """Exit program with given status code."""
            sys.exit(int(code))
        
        def sys_getenv(name, default=None):
            """Get environment variable."""
            value = os.environ.get(str(name))
            return value if value is not None else default
        
        def sys_platform():
            """Return platform identifier."""
            return platform.platform()
        
        def sys_cwd():
            """Return current working directory."""
            return os.getcwd()
        
        def sys_chdir(path):
            """Change current working directory."""
            try:
                os.chdir(str(path))
                return None
            except FileNotFoundError:
                err = ErrorObject("NotFoundError", f"Directory not found: {path}", trace=[])
                raise err
            except PermissionError:
                err = ErrorObject("PermissionError", f"Permission denied: {path}", trace=[])
                raise err
            except NotADirectoryError:
                err = ErrorObject("IOError", f"'{path}' is not a directory", trace=[])
                raise err
            except Exception as e:
                err = ErrorObject("IOError", f"Failed to change directory to '{path}': {str(e)}", trace=[])
                raise err
        
        # =======================
        # DATA STRUCTURE HELPERS
        # =======================
        
        def bw_mklist(*args):
            """Create list from arguments."""
            return list(args)
        
        def bw_mkdict(*args):
            """Create dictionary from key-value pairs."""
            result = {}
            for i in range(0, len(args), 2):
                key = args[i]
                value = args[i+1] if i+1 < len(args) else None
                result[key] = value
            return result
        
        # =======================
        # IMPORT HELPER
        # =======================
        
        def import_helper(module_name, alias):
            """
            Import a PRIME module (.prime or .pbc).
            
            Args:
                module_name: Name of module to import
                alias: Optional alias for imported symbols
                
            Returns:
                Module object with vars and funcs
                
            Raises:
                ErrorObject(NotFoundError) if module not found
            """
            base = module_name
            pbc_path = os.path.join(self.cwd, base + ".pbc")
            prime_path = os.path.join(self.cwd, base + ".prime")
            module_symbols = {}
            module_functions = {}
            module_debug = []
            module_exports = set()
            
            # Try to load .pbc first, then .prime
            if os.path.exists(pbc_path):
                code, functions, debug, filename, exports, version = Emitter.load_pbc(pbc_path)
                vm = PrimeVM(code, functions, debug, exports=exports, cwd=self.cwd)
                try:
                    vm.run()
                except SystemExit:
                    pass
                module_symbols = vm.frames[0].vars
                module_functions = vm.functions
                module_exports = exports
                
                # Auto-run __init__ if present
                if "__init__" in module_functions:
                    func_addr, params = module_functions["__init__"]
                    # Set up call frame that returns to HALT
                    halt_idx = next((i for i, (op, _) in enumerate(code) if op == "HALT"), len(code))
                    vm.push_frame(halt_idx, {}, func_name="__init__", entry_ip=func_addr)
                    vm.ip = func_addr
                    try:
                        vm.run()
                    except SystemExit:
                        pass
                        
            elif os.path.exists(prime_path):
                with open(prime_path, "r", encoding="utf-8") as f:
                    src = f.read()
                tokens = tokenize(src)
                p = Parser(tokens, filename=prime_path)
                code, functions, debug, exports = p.parse()
                vm = PrimeVM(code, functions, debug, exports=exports, cwd=self.cwd)
                try:
                    vm.run()
                except SystemExit:
                    pass
                module_symbols = vm.frames[0].vars
                module_functions = vm.functions
                module_exports = exports
                
                # Auto-run __init__ if present
                if "__init__" in module_functions:
                    func_addr, params = module_functions["__init__"]
                    halt_idx = next((i for i, (op, _) in enumerate(code) if op == "HALT"), len(code))
                    vm.push_frame(halt_idx, {}, func_name="__init__", entry_ip=func_addr)
                    vm.ip = func_addr
                    try:
                        vm.run()
                    except SystemExit:
                        pass
            else:
                err = ErrorObject("NotFoundError", f"Module {module_name} not found", trace=[])
                raise err
            
            # Build module object exposing only exports if present
            if module_exports:
                exported_vars = {k: module_symbols[k] for k in module_exports if k in module_symbols}
                exported_funcs = {k: module_functions[k] for k in module_exports if k in module_functions}
                module_obj = {"vars": exported_vars, "funcs": exported_funcs}
            else:
                module_obj = {"vars": dict(module_symbols), "funcs": dict(module_functions)}
            
            if alias:
                self.frames[0].vars[alias] = module_obj
                return module_obj
            
            # Otherwise merge exported symbols into global frame
            for k, v in module_obj["vars"].items():
                self.frames[0].vars[k] = v
            for k, v in module_obj["funcs"].items():
                self.functions[k] = v
            return module_obj
        
        # =======================
        # BUILD STANDARD LIBRARY DICTIONARY
        # =======================
        
        built = {
            # I/O
            "say": bw_say,
            "read": bw_read,
            "input": bw_read,  # alias
            
            # Error constructors
            "Error": make_error_ctor("Error"),
            "RuntimeError": make_error_ctor("RuntimeError"),
            "NameError": make_error_ctor("NameError"),
            "AttributeError": make_error_ctor("AttributeError"),
            "TypeError": make_error_ctor("TypeError"),
            "ValueError": make_error_ctor("ValueError"),
            "StateError": make_error_ctor("StateError"),
            "ArithmeticError": make_error_ctor("ArithmeticError"),
            "DivideByZeroError": make_error_ctor("DivideByZeroError"),
            "IOError": make_error_ctor("IOError"),
            "FileError": make_error_ctor("FileError"),
            "PermissionError": make_error_ctor("PermissionError"),
            "NotFoundError": make_error_ctor("NotFoundError"),
            "ImportError": make_error_ctor("ImportError"),
            "ControlError": make_error_ctor("ControlError"),
            "BreakError": make_error_ctor("BreakError"),
            "ContinueError": make_error_ctor("ContinueError"),
            "FatalError": make_error_ctor("FatalError"),
            
            # Collections
            "len": bw_len,
            "get": bw_get,
            
            # File System
            "fs.read": fs_read,
            "fs.write": fs_write,
            "fs.append": fs_append,
            "fs.readlines": fs_readlines,
            "fs.exists": fs_exists,
            "fs.isdir": fs_isdir,
            "fs.isfile": fs_isfile,
            "fs.listdir": fs_listdir,
            "fs.mkdir": fs_mkdir,
            "fs.remove": fs_remove,
            "fs.rmdir": fs_rmdir,
            "fs.rename": fs_rename,
            "fs.copy": fs_copy,
            "fs.getsize": fs_getsize,
            "fs.getmtime": fs_getmtime,
            
            # Time
            "time.now": t_now,
            "time.timestamp": t_timestamp,
            "time.sleep": t_sleep,
            "time.strftime": t_strftime,
            "time.parse": t_parse,
            
            # Math
            "math.abs": math_abs,
            "math.floor": math_floor,
            "math.ceil": math_ceil,
            "math.round": math_round,
            "math.sqrt": math_sqrt,
            "math.pow": math_pow,
            "math.exp": math_exp,
            "math.log": math_log,
            "math.sin": math_sin,
            "math.cos": math_cos,
            "math.tan": math_tan,
            "math.asin": math_asin,
            "math.acos": math_acos,
            "math.atan": math_atan,
            "math.atan2": math_atan2,
            "math.pi": math.pi,
            "math.e": math.e,
            
            # Random
            "random.random": random_random,
            "random.randint": random_randint,
            "random.uniform": random_uniform,
            "random.choice": random_choice,
            "random.shuffle": random_shuffle,
            "random.seed": random_seed,
            
            # Strings
            "str.split": str_split,
            "str.upper": str_upper,
            "str.lower": str_lower,
            "str.strip": str_strip,
            "str.lstrip": str_lstrip,
            "str.rstrip": str_rstrip,
            "str.replace": str_replace,
            "str.find": str_find,
            "str.rfind": str_rfind,
            "str.startswith": str_startswith,
            "str.endswith": str_endswith,
            "str.join": str_join,
            "str.format": str_format,
            "str.isalpha": str_isalpha,
            "str.isdigit": str_isdigit,
            "str.isalnum": str_isalnum,
            "str.isspace": str_isspace,
            
            # Type conversion with aliases
            "to_str": to_str,
            "to_int": to_int,
            "to_float": to_float,
            "to_bool": to_bool,
            "number": to_float,   # alias for to_float
            "int": to_int,        # alias for to_int
            "float": to_float,    # alias for to_float
            "str": to_str,        # alias for to_str
            "bool": to_bool,      # alias for to_bool
            
            # System
            "sys.argv": sys_argv,
            "sys.exit": sys_exit,
            "sys.getenv": sys_getenv,
            "sys.platform": sys_platform,
            "sys.cwd": sys_cwd,
            "sys.chdir": sys_chdir,
            
            # Internal helpers
            "__import__": import_helper,
            "__mklist__": bw_mklist,
            "__mkdict__": bw_mkdict,
        }
        
        return built

    def run(self):
        """
        Execute bytecode until HALT or error.
        
        This is the main execution loop of the VM.
        """
        while True:
            # Check IP bounds
            if self.ip < 0 or self.ip >= len(self.code):
                raise VMError("Instruction pointer out of range")
            
            # Fetch instruction
            op, arg = self.code[self.ip]
            self.ip += 1
            
            # Execute instruction based on opcode
            if op == "PUSH_CONST":
                self.stack.append(arg)
                
            elif op == "LOAD":
                try:
                    v = self.lookup_var(arg)
                except VMError as e:
                    # Should have been handled by lookup_var raising an error
                    continue
                self.stack.append(v)
                
            elif op == "STORE":
                val = None
                if self.stack:
                    val = self.stack.pop()
                self.store_var(arg, val)
                
            elif op == "STORE_CONST":
                val = None
                if self.stack:
                    val = self.stack.pop()
                self.store_const(arg, val)
                
            elif op == "PRINT":
                v = self.stack.pop() if self.stack else None
                print(v)
                
            elif op == "ADD":
                b = self.stack.pop()
                a = self.stack.pop()
                # Handle string concatenation
                if isinstance(a, str) or isinstance(b, str):
                    self.stack.append(str(a) + str(b))
                else:
                    self.stack.append(a + b)
                    
            elif op == "SUB":
                b = self.stack.pop()
                a = self.stack.pop()
                self.stack.append(a - b)
                
            elif op == "MUL":
                b = self.stack.pop()
                a = self.stack.pop()
                self.stack.append(a * b)
                
            elif op == "DIV":
                b = self.stack.pop()
                a = self.stack.pop()
                if b == 0:
                    err = ErrorObject("DivideByZeroError", "division by zero", trace=self._build_trace())
                    self._raise_error(err)
                    continue
                self.stack.append(a / b)
                
            elif op == "MOD":
                b = self.stack.pop()
                a = self.stack.pop()
                self.stack.append(a % b)
                
            elif op == "UNARY_NEG":
                a = self.stack.pop()
                self.stack.append(-a)
                
            elif op == "NOT":
                a = self.stack.pop()
                self.stack.append(not a)
                
            elif op == "AND":
                b = self.stack.pop()
                a = self.stack.pop()
                self.stack.append(a and b)
                
            elif op == "OR":
                b = self.stack.pop()
                a = self.stack.pop()
                self.stack.append(a or b)
                
            elif op == "CMP_EQ":
                b = self.stack.pop()
                a = self.stack.pop()
                self.stack.append(a == b)
                
            elif op == "CMP_NE":
                b = self.stack.pop()
                a = self.stack.pop()
                self.stack.append(a != b)
                
            elif op == "CMP_LT":
                b = self.stack.pop()
                a = self.stack.pop()
                self.stack.append(a < b)
                
            elif op == "CMP_GT":
                b = self.stack.pop()
                a = self.stack.pop()
                self.stack.append(a > b)
                
            elif op == "CMP_LE":
                b = self.stack.pop()
                a = self.stack.pop()
                self.stack.append(a <= b)
                
            elif op == "CMP_GE":
                b = self.stack.pop()
                a = self.stack.pop()
                self.stack.append(a >= b)
                
            elif op == "JMP":
                self.ip = arg
                
            elif op == "JMP_IF_FALSE":
                cond = None
                if self.stack:
                    cond = self.stack.pop()
                if not cond:
                    self.ip = arg
                    
            elif op == "CALL":
                name, argc = arg
                args = []
                for _ in range(argc):
                    args.append(self.stack.pop())
                args.reverse()
                
                if name is None:
                    # Function from stack (e.g., from dot notation)
                    func_obj = self.stack.pop()
                    if isinstance(func_obj, tuple) and len(func_obj) == 2:
                        # It's a (addr, params) tuple
                        func_addr, params = func_obj
                        param_bindings = {}
                        for i, p in enumerate(params):
                            param_bindings[p] = args[i] if i < len(args) else None
                        ret_ip = self.ip
                        self.push_frame(ret_ip, param_bindings, func_name="<lambda>", entry_ip=func_addr)
                        self.ip = func_addr
                        continue
                    else:
                        # Assume it's a callable
                        try:
                            res = func_obj(*args)
                            self.stack.append(res)
                        except Exception as e:
                            if isinstance(e, ErrorObject):
                                self._raise_error(e)
                            else:
                                err = ErrorObject("RuntimeError", str(e), trace=self._build_trace())
                                self._raise_error(err)
                        continue
                        
                elif name in self.functions:
                    # User-defined function
                    func_addr, params = self.functions[name]
                    param_bindings = {}
                    for i, p in enumerate(params):
                        param_bindings[p] = args[i] if i < len(args) else None
                    ret_ip = self.ip
                    self.push_frame(ret_ip, param_bindings, func_name=name, entry_ip=func_addr)
                    self.ip = func_addr
                    continue
                    
                # Check built-in functions
                fn = None
                if name in self.builtins:
                    fn = self.builtins[name]
                    
                if fn:
                    try:
                        res = fn(*args)
                        self.stack.append(res)
                    except ErrorObject as e:
                        self._raise_error(e)
                    except FileNotFoundError as e:
                        err = ErrorObject("NotFoundError", str(e), trace=self._build_trace())
                        self._raise_error(err)
                    except Exception as e:
                        err = ErrorObject("RuntimeError", str(e), trace=self._build_trace())
                        self._raise_error(err)
                    continue
                    
                # Function not found
                err = ErrorObject("ImportError", f"Unknown function '{name}'", trace=self._build_trace())
                self._raise_error(err)
                continue
                
            elif op == "CALL_ATTR":
                attr, argc = arg
                args = []
                for _ in range(argc):
                    args.append(self.stack.pop())
                args.reverse()
                obj = self.stack.pop() if self.stack else None
                
                # Try to get the method from object
                method = None
                if isinstance(obj, dict):
                    if attr in obj:
                        method = obj[attr]
                    elif "funcs" in obj and attr in obj["funcs"]:
                        method = obj["funcs"][attr]
                
                if method is not None:
                    if isinstance(method, tuple) and len(method) == 2:
                        # It's a (addr, params) tuple
                        func_addr, params = method
                        param_bindings = {}
                        for i, p in enumerate(params):
                            param_bindings[p] = args[i] if i < len(args) else None
                        ret_ip = self.ip
                        self.push_frame(ret_ip, param_bindings, func_name=attr, entry_ip=func_addr)
                        self.ip = func_addr
                        continue
                    else:
                        # Assume it's a callable
                        try:
                            res = method(*args)
                            self.stack.append(res)
                        except Exception as e:
                            if isinstance(e, ErrorObject):
                                self._raise_error(e)
                            else:
                                err = ErrorObject("RuntimeError", str(e), trace=self._build_trace())
                                self._raise_error(err)
                        continue
                        
                # Method not found
                err = ErrorObject("AttributeError", f"Object has no method '{attr}'", trace=self._build_trace())
                self._raise_error(err)
                continue
                
            elif op == "GET_ATTR":
                obj = self.stack.pop() if self.stack else None
                if isinstance(obj, dict):
                    if arg in obj:
                        self.stack.append(obj[arg])
                    elif "vars" in obj and arg in obj["vars"]:
                        self.stack.append(obj["vars"][arg])
                    elif "funcs" in obj and arg in obj["funcs"]:
                        self.stack.append(obj["funcs"][arg])
                    else:
                        err = ErrorObject("AttributeError", f"Object has no attribute '{arg}'", trace=self._build_trace())
                        self._raise_error(err)
                elif isinstance(obj, ErrorObject):
                    # Allow accessing error properties
                    if arg == "type":
                        self.stack.append(obj.type)
                    elif arg == "message":
                        self.stack.append(obj.message)
                    elif arg == "trace":
                        self.stack.append(obj.trace)
                    else:
                        err = ErrorObject("AttributeError", f"Error object has no attribute '{arg}'", trace=self._build_trace())
                        self._raise_error(err)
                else:
                    err = ErrorObject("AttributeError", f"Cannot get attribute '{arg}' from non-object", trace=self._build_trace())
                    self._raise_error(err)
                    
            elif op == "RET":
                ret_val = None
                if self.stack:
                    ret_val = self.stack.pop()
                if len(self.frames) <= 1:
                    return  # Return from global scope ends execution
                ret_ip = self.frames[-1].return_ip
                self.pop_frame()
                self.stack.append(ret_val)
                self.ip = ret_ip
                continue
                
            elif op == "TRY":
                handler_ip, error_type, catch_var = arg
                ef = {"handler_ip": handler_ip, "error_type": error_type,
                      "catch_var": catch_var, "frame_depth": self.current_frame_depth()}
                self.exception_stack.append(ef)
                
            elif op == "THROW":
                if not self.stack:
                    err = ErrorObject("RuntimeError", "throw without error object", trace=self._build_trace())
                    self._raise_error(err)
                    continue
                errobj = self.stack.pop()
                if not isinstance(errobj, ErrorObject):
                    errobj = ErrorObject("RuntimeError", str(errobj), trace=self._build_trace())
                errobj.trace = self._build_trace()
                self._raise_error(errobj)
                continue
                
            elif op == "HALT":
                return  # End execution
                
            else:
                raise VMError(f"Unknown opcode: {op}")

    def _raise_error(self, errobj: ErrorObject):
        """
        Raise an error, searching for matching catch handler.
        
        If no handler found, prints error and exits.
        
        Args:
            errobj: Error object to raise
        """
        # Search for matching handler in exception stack
        while self.exception_stack:
            handler = self.exception_stack.pop()
            if handler["frame_depth"] > self.current_frame_depth():
                continue
            if self.error_matches(errobj, handler["error_type"]):
                # Found handler - unwind to handler's frame depth
                while self.current_frame_depth() > handler["frame_depth"]:
                    self.pop_frame()
                self.ip = handler["handler_ip"]
                self.stack.append(errobj)
                return
        
        # No handler found - print error and exit
        current_line = None
        if self.ip > 0 and self.ip - 1 < len(self.debug):
            _, current_line = self.debug[self.ip - 1]
        
        print(f"Uncaught error at line {current_line or '?'}: {errobj}")
        if isinstance(errobj, ErrorObject) and errobj.trace:
            print("Stack trace (most recent call last):")
            for fn, fn_file, fn_line in errobj.trace:
                if fn_file and fn_line:
                    print(f"  in {fn} at {fn_file}:{fn_line}")
                elif fn_file:
                    print(f"  in {fn} at {fn_file}")
                else:
                    print(f"  in {fn}")
        sys.exit(1)

# =======================
# DISASSEMBLER
# =======================
# Displays bytecode in human-readable form with source line mapping

def disassemble_pbc(path):
    """
    Disassemble a .pbc file to show bytecode and source mapping.
    
    Args:
        path: Path to .pbc file
    """
    code, functions, debug, filename, exports, version = Emitter.load_pbc(path)
    print(f"Disassembly of {path} (original file: {filename})")
    print(f"Version: {version}")
    print(f"Functions: {functions}")
    print(f"Exports: {exports}")
    
    # Try to load source code for line mapping
    source_lines = None
    if os.path.exists(filename):
        try:
            with open(filename, "r", encoding="utf-8") as f:
                source_lines = f.readlines()
        except Exception:
            source_lines = None
    
    # Print each instruction
    for i, (op, arg) in enumerate(code):
        dbg = debug[i] if i < len(debug) else (None, None)
        print(f"{i:04d}: {op:<12} {arg!s:<20} ; {dbg}")
        
        # Show source line if available
        if dbg and dbg[0] and dbg[1] and source_lines:
            fn, ln = dbg
            if os.path.exists(fn):
                line_idx = ln-1
                if 0 <= line_idx < len(source_lines):
                    src_line = source_lines[line_idx].rstrip("\n")
                    print(f"       -> {fn}:{ln}  {src_line}")

# =======================
# PBC VERIFICATION
# =======================
# Validates bytecode file integrity

def verify_pbc(path):
    """
    Verify the integrity of a .pbc file.
    
    Checks:
    - Magic number and version
    - Valid opcodes
    - Function addresses within bounds
    - Jump targets within bounds
    
    Args:
        path: Path to .pbc file
        
    Returns:
        True if valid, False otherwise
    """
    try:
        print(f"Verifying {path}...")
        code, functions, debug, filename, exports, version = Emitter.load_pbc(path)
        print(f"✓ Valid PRIME bytecode file (version {version})")
        print(f"  Original source: {filename}")
        print(f"  Bytecode size: {len(code)} instructions")
        print(f"  Functions defined: {len(functions)}")
        print(f"  Exports: {exports}")
        
        # Verify all opcodes are valid
        invalid_opcodes = []
        for i, (op, arg) in enumerate(code):
            if op not in OPCODE_TO_ID:
                invalid_opcodes.append((i, op))
        
        if invalid_opcodes:
            print(f"✗ Found {len(invalid_opcodes)} invalid opcodes:")
            for i, op in invalid_opcodes:
                print(f"  Instruction {i}: {op}")
            return False
        
        print("✓ All opcodes are valid")
        
        # Verify function addresses are within bounds
        invalid_funcs = []
        for name, (addr, params) in functions.items():
            if addr < 0 or addr >= len(code):
                invalid_funcs.append((name, addr))
        
        if invalid_funcs:
            print(f"✗ Found {len(invalid_funcs)} functions with invalid addresses:")
            for name, addr in invalid_funcs:
                print(f"  {name}: address {addr} out of range (0-{len(code)-1})")
            return False
        
        print("✓ All function addresses are valid")
        
        # Verify jump targets
        invalid_jumps = []
        for i, (op, arg) in enumerate(code):
            if op in ("JMP", "JMP_IF_FALSE", "TRY"):
                if arg is not None:
                    if isinstance(arg, (int, float)):
                        target = int(arg)
                        if target < 0 or target >= len(code):
                            invalid_jumps.append((i, op, target))
                    elif op == "TRY" and isinstance(arg, tuple):
                        addr, err_type, catch_var = arg
                        if addr is not None and (addr < 0 or addr >= len(code)):
                            invalid_jumps.append((i, op, addr))
        
        if invalid_jumps:
            print(f"✗ Found {len(invalid_jumps)} invalid jump targets:")
            for i, op, target in invalid_jumps:
                print(f"  Instruction {i} ({op}): target {target} out of range (0-{len(code)-1})")
            return False
        
        print("✓ All jump targets are valid")
        print("✓ PBC file verification successful!")
        return True
        
    except Exception as e:
        print(f"✗ Verification failed: {e}")
        return False

# =======================
# STANDALONE EXECUTABLE COMPILATION (PyInstaller)
# =======================

def compile_to_exe(source_path, exe_path):
    """
    Compile a .prime file into a standalone executable using PyInstaller.
    
    Args:
        source_path: Path to .prime source file
        exe_path: Path for output executable
        
    Returns:
        True if successful, False otherwise
    """
    print(f"Compiling {source_path} to standalone executable {exe_path}...")
    
    # First compile to a standalone Python script
    temp_dir = tempfile.mkdtemp(prefix="prime_exe_")
    temp_py = os.path.join(temp_dir, "standalone.py")
    
    try:
        # Use the existing compile_to_py function
        compile_to_py(source_path, temp_py)
        
        print(f"  Created temporary script: {temp_py}")
        print(f"  Running PyInstaller to create executable...")
        
        # Run PyInstaller
        if sys.platform == "win32":
            # On Windows, create .exe
            cmd = [
                sys.executable, "-m", "pyinstaller",
                "--onefile",
                "--name", os.path.splitext(os.path.basename(exe_path))[0],
                "--distpath", os.path.dirname(exe_path) if os.path.dirname(exe_path) else ".",
                "--workpath", os.path.join(temp_dir, "build"),
                "--specpath", temp_dir,
                "--clean",
                temp_py
            ]
        else:
            # On Unix-like systems
            cmd = [
                sys.executable, "-m", "pyinstaller",
                "--onefile",
                "--name", os.path.splitext(os.path.basename(exe_path))[0],
                "--distpath", os.path.dirname(exe_path) if os.path.dirname(exe_path) else ".",
                "--workpath", os.path.join(temp_dir, "build"),
                "--specpath", temp_dir,
                "--clean",
                temp_py
            ]
        
        # Run PyInstaller
        result = subprocess.run(cmd, capture_output=True, text=True)
        
        if result.returncode != 0:
            print(f"✗ PyInstaller failed:")
            print(f"  Error: {result.stderr}")
            return False
        
        print(f"✓ PyInstaller completed successfully")
        
        # Determine the generated executable path
        if sys.platform == "win32":
            generated_exe = os.path.join(
                os.path.dirname(exe_path) if os.path.dirname(exe_path) else "dist",
                os.path.splitext(os.path.basename(exe_path))[0] + ".exe"
            )
        else:
            generated_exe = os.path.join(
                os.path.dirname(exe_path) if os.path.dirname(exe_path) else "dist",
                os.path.splitext(os.path.basename(exe_path))[0]
            )
        
        # Move to desired location if different
        if generated_exe != exe_path:
            if os.path.exists(generated_exe):
                shutil.move(generated_exe, exe_path)
                print(f"✓ Moved executable to: {exe_path}")
            else:
                # Try to find the executable
                dist_dir = os.path.dirname(generated_exe)
                for f in os.listdir(dist_dir):
                    if f.startswith(os.path.splitext(os.path.basename(exe_path))[0]):
                        shutil.move(os.path.join(dist_dir, f), exe_path)
                        print(f"✓ Found and moved executable to: {exe_path}")
                        break
        
        # Clean up PyInstaller artifacts
        spec_file = os.path.join(temp_dir, f"{os.path.splitext(os.path.basename(exe_path))[0]}.spec")
        if os.path.exists(spec_file):
            os.remove(spec_file)
        
        build_dir = os.path.join(temp_dir, "build")
        if os.path.exists(build_dir):
            shutil.rmtree(build_dir, ignore_errors=True)
        
        dist_dir = os.path.dirname(generated_exe) if generated_exe != exe_path else "dist"
        if os.path.exists(dist_dir) and os.path.isdir(dist_dir):
            # Only remove if it's empty or we created it
            try:
                if not os.listdir(dist_dir):
                    os.rmdir(dist_dir)
            except:
                pass
        
        print(f"✓ Created standalone executable: {exe_path}")
        print(f"  Size: {os.path.getsize(exe_path) if os.path.exists(exe_path) else 0} bytes")
        
        return True
        
    except FileNotFoundError:
        print("✗ PyInstaller not found. Please install it with:")
        print("  pip install pyinstaller")
        return False
    except Exception as e:
        print(f"✗ Error creating executable: {e}")
        return False
    finally:
        # Clean up temporary directory
        try:
            shutil.rmtree(temp_dir, ignore_errors=True)
        except:
            pass

# =======================
# STANDALONE PYTHON SCRIPT COMPILATION
# =======================

def compile_to_py(source_path, py_path):
    """
    Compile a .prime file into a standalone Python script.
    
    Args:
        source_path: Path to .prime source file
        py_path: Path for output Python script
    """
    print(f"Compiling {source_path} to standalone Python script {py_path}...")
    
    # Read and compile the source
    with open(source_path, "r", encoding="utf-8") as f:
        src = f.read()
    
    tokens = tokenize(src)
    p = Parser(tokens, filename=source_path)
    code, functions, debug, exports = p.parse()
    
    # Create a temporary PBC file to get the binary data
    temp_pbc = tempfile.mktemp(suffix=".pbc")
    em = p.em
    em.save_pbc(temp_pbc)
    
    # Read the PBC binary data
    with open(temp_pbc, "rb") as f:
        pbc_data = f.read()
    
    # Clean up
    os.remove(temp_pbc)
    
    # Compress and encode the bytecode
    compressed = zlib.compress(pbc_data, level=9)
    encoded = base64.b85encode(compressed).decode('ascii')
    
    # Create the executable template with enhanced standard library
    exe_template = f'''#!/usr/bin/env python3
"""
PRIME Standalone Executable
Compiled from: {os.path.basename(source_path)}
Compiler Version: {VERSION}
Bytecode Version: {BYTECODE_VERSION}
Created: {time.strftime("%Y-%m-%d %H:%M:%S")}
"""

import sys
import json
import struct
import os
import time
import base64
import zlib
import io
import math
import random
import datetime
import platform
import shutil

# -----------------------
# Version Information
# -----------------------
VERSION = "{VERSION}"
BYTECODE_VERSION = {BYTECODE_VERSION}

# -----------------------
# PRIME Interpreter Core (embedded)
# -----------------------
# Note: This is a minimal version of the PRIME interpreter
# designed to run embedded bytecode.

class ErrorObject:
    def __init__(self, type_name, message=None, trace=None):
        self.type = type_name
        self.message = message if message is not None else ""
        self.trace = trace or []
    def __repr__(self):
        return f"<Error {{self.type}}: {{self.message}}>"

class Frame:
    def __init__(self, return_ip=None, params=None, func_name=None, entry_ip=None):
        self.vars = {{}} if params is None else dict(params)
        self.consts = set()
        self.return_ip = return_ip
        self.func_name = func_name
        self.entry_ip = entry_ip

class PrimeVM:
    def __init__(self, code, functions, debug, exports=None, cwd=None):
        self.code = code
        self.functions = functions
        self.debug = debug
        self.exports = exports or set()
        self.ip = 0
        self.stack = []
        self.frames = [Frame(return_ip=None, params={{}}, func_name="<global>", entry_ip=0)]
        self.exception_stack = []
        self.builtins = self._make_builtins()
        self.error_parents = {{
            "NameError": "RuntimeError",
            "AttributeError": "RuntimeError",
            "TypeError": "RuntimeError",
            "ValueError": "RuntimeError",
            "StateError": "RuntimeError",
            "ArithmeticError": "RuntimeError",
            "DivideByZeroError": "ArithmeticError",
            "IOError": "RuntimeError",
            "FileError": "IOError",
            "PermissionError": "IOError",
            "NotFoundError": "IOError",
            "ImportError": "RuntimeError",
            "ControlError": "Error",
            "BreakError": "ControlError",
            "ContinueError": "ControlError",
            "FatalError": None,
            "RuntimeError": "Error",
        }}
        self.cwd = cwd or os.getcwd()

    def current_frame_depth(self):
        return len(self.frames) - 1

    def push_frame(self, return_ip, param_bindings, func_name=None, entry_ip=None):
        self.frames.append(Frame(return_ip=return_ip, params=param_bindings, 
                                func_name=func_name, entry_ip=entry_ip))

    def pop_frame(self):
        if len(self.frames) <= 1:
            return None
        self.frames.pop()

    def lookup_var(self, name):
        for f in reversed(self.frames):
            if name in f.vars:
                return f.vars[name]
        if self.ip - 1 < len(self.debug):
            filename, line = self.debug[self.ip - 1]
            err_msg = f"Undefined variable '{{name}}'"
            if filename:
                err_msg += f" at {{filename}}"
            if line:
                err_msg += f":{{line}}"
            err = ErrorObject("NameError", err_msg, trace=self._build_trace())
            self._raise_error(err)
        else:
            err = ErrorObject("NameError", f"Undefined variable: {{name}}", trace=self._build_trace())
            self._raise_error(err)

    def store_var(self, name, value):
        for f in reversed(self.frames):
            if name in f.vars:
                if hasattr(f, 'consts') and name in f.consts:
                    err = ErrorObject("TypeError", f"Cannot reassign const '{{name}}'", 
                                    trace=self._build_trace())
                    self._raise_error(err)
                    return
                f.vars[name] = value
                return
        self.frames[-1].vars[name] = value

    def store_const(self, name, value):
        for f in reversed(self.frames):
            if name in f.vars:
                err = ErrorObject("TypeError", f"Cannot reassign const '{{name}}'", 
                                trace=self._build_trace())
                self._raise_error(err)
                return
        self.frames[-1].vars[name] = value
        self.frames[-1].consts.add(name)

    def error_matches(self, errobj, handler_type):
        cur = errobj.type
        while True:
            if cur == handler_type:
                return True
            parent = self.error_parents.get(cur, None)
            if parent is None:
                return handler_type == "Error" and cur is not None
            cur = parent

    def _build_trace(self):
        trace = []
        for frame in reversed(self.frames):
            func = frame.func_name or "<anon>"
            line = None
            filename = None
            if frame.entry_ip is not None and 0 <= frame.entry_ip < len(self.debug):
                filename, line = self.debug[frame.entry_ip]
            trace.append((func, filename, line))
        return trace

    def _make_builtins(self):
        def bw_say(*args):
            print(*args)
            return None
        def bw_read(prompt=None):
            try:
                if prompt is None:
                    return input()
                else:
                    return input(str(prompt))
            except EOFError:
                return ""
        def make_error_ctor(type_name):
            def ctor(msg=None):
                return ErrorObject(type_name, msg)
            return ctor
        def bw_len(x):
            try:
                return len(x)
            except Exception:
                raise
        def bw_get(coll, idx):
            return coll[idx]
        def fs_read(path):
            with open(path, "r", encoding="utf-8") as f:
                return f.read()
        def fs_write(path, data):
            with open(path, "w", encoding="utf-8") as f:
                f.write(str(data))
                return None
        def fs_append(path, data):
            with open(path, "a", encoding="utf-8") as f:
                f.write(str(data))
                return None
        def fs_exists(path):
            return os.path.exists(path)
        def fs_isdir(path):
            return os.path.isdir(path)
        def fs_isfile(path):
            return os.path.isfile(path)
        def fs_listdir(path="."):
            return os.listdir(path)
        def fs_mkdir(path):
            os.makedirs(path, exist_ok=True)
            return None
        def fs_remove(path):
            os.remove(path)
            return None
        def fs_rmdir(path):
            os.rmdir(path)
            return None
        def fs_rename(src, dst):
            os.rename(src, dst)
            return None
        def fs_copy(src, dst):
            shutil.copy2(src, dst)
            return None
        def fs_getsize(path):
            return os.path.getsize(path)
        def fs_getmtime(path):
            return os.path.getmtime(path)
        def t_now():
            return datetime.datetime.now().isoformat()
        def t_timestamp():
            return time.time()
        def t_sleep(s):
            time.sleep(float(s))
            return None
        def t_strftime(format_str, timestamp=None):
            if timestamp is None:
                timestamp = time.time()
            return time.strftime(str(format_str), time.localtime(float(timestamp)))
        def math_abs(x):
            return abs(float(x))
        def math_floor(x):
            return math.floor(float(x))
        def math_ceil(x):
            return math.ceil(float(x))
        def math_round(x, ndigits=0):
            return round(float(x), int(ndigits))
        def math_sqrt(x):
            return math.sqrt(float(x))
        def math_pow(x, y):
            return math.pow(float(x), float(y))
        def math_exp(x):
            return math.exp(float(x))
        def math_log(x, base=math.e):
            if base == math.e:
                return math.log(float(x))
            else:
                return math.log(float(x), float(base))
        def math_sin(x):
            return math.sin(float(x))
        def math_cos(x):
            return math.cos(float(x))
        def math_tan(x):
            return math.tan(float(x))
        def math_asin(x):
            return math.asin(float(x))
        def math_acos(x):
            return math.acos(float(x))
        def math_atan(x):
            return math.atan(float(x))
        def math_atan2(y, x):
            return math.atan2(float(y), float(x))
        def random_random():
            return random.random()
        def random_randint(a, b):
            return random.randint(int(a), int(b))
        def random_uniform(a, b):
            return random.uniform(float(a), float(b))
        def random_choice(seq):
            return random.choice(seq)
        def random_shuffle(seq):
            random.shuffle(seq)
            return seq
        def random_seed(seed=None):
            random.seed(seed)
            return None
        def str_split(s, delim=None):
            return s.split(delim) if delim else s.split()
        def str_upper(s):
            return s.upper()
        def str_lower(s):
            return s.lower()
        def str_strip(s, chars=None):
            return s.strip(chars) if chars else s.strip()
        def str_lstrip(s, chars=None):
            return s.lstrip(chars) if chars else s.lstrip()
        def str_rstrip(s, chars=None):
            return s.rstrip(chars) if chars else s.rstrip()
        def str_replace(s, old, new, count=-1):
            return s.replace(str(old), str(new), int(count))
        def str_find(s, sub, start=0, end=None):
            return s.find(str(sub), int(start), end)
        def str_rfind(s, sub, start=0, end=None):
            return s.rfind(str(sub), int(start), end)
        def str_startswith(s, prefix):
            return s.startswith(str(prefix))
        def str_endswith(s, suffix):
            return s.endswith(str(suffix))
        def str_join(sep, iterable):
            return str(sep).join(str(x) for x in iterable)
        def str_format(s, *args):
            return s.format(*args)
        def str_isalpha(s):
            return s.isalpha()
        def str_isdigit(s):
            return s.isdigit()
        def str_isalnum(s):
            return s.isalnum()
        def str_isspace(s):
            return s.isspace()
        def to_str(x):
            return str(x)
        def to_int(x):
            return int(x)
        def to_float(x):
            return float(x)
        def to_bool(x):
            return bool(x)
        def sys_argv():
            return sys.argv
        def sys_exit(code=0):
            sys.exit(int(code))
        def sys_getenv(name, default=None):
            value = os.environ.get(str(name))
            return value if value is not None else default
        def sys_platform():
            return platform.platform()
        def sys_cwd():
            return os.getcwd()
        def sys_chdir(path):
            os.chdir(str(path))
            return None
        def bw_mklist(*args):
            return list(args)
        def bw_mkdict(*args):
            result = {{}}
            for i in range(0, len(args), 2):
                key = args[i]
                value = args[i+1] if i+1 < len(args) else None
                result[key] = value
            return result

        return {{
            # I/O
            "say": bw_say,
            "read": bw_read,
            "input": bw_read,  # alias
            # Errors
            "Error": make_error_ctor("Error"),
            "RuntimeError": make_error_ctor("RuntimeError"),
            "NameError": make_error_ctor("NameError"),
            "AttributeError": make_error_ctor("AttributeError"),
            "TypeError": make_error_ctor("TypeError"),
            "ValueError": make_error_ctor("ValueError"),
            "ArithmeticError": make_error_ctor("ArithmeticError"),
            "DivideByZeroError": make_error_ctor("DivideByZeroError"),
            "NotFoundError": make_error_ctor("NotFoundError"),
            # Collections
            "len": bw_len,
            "get": bw_get,
            # File System
            "fs.read": fs_read,
            "fs.write": fs_write,
            "fs.append": fs_append,
            "fs.exists": fs_exists,
            "fs.isdir": fs_isdir,
            "fs.isfile": fs_isfile,
            "fs.listdir": fs_listdir,
            "fs.mkdir": fs_mkdir,
            "fs.remove": fs_remove,
            "fs.rmdir": fs_rmdir,
            "fs.rename": fs_rename,
            "fs.copy": fs_copy,
            "fs.getsize": fs_getsize,
            "fs.getmtime": fs_getmtime,
            # Time
            "time.now": t_now,
            "time.timestamp": t_timestamp,
            "time.sleep": t_sleep,
            "time.strftime": t_strftime,
            # Math
            "math.abs": math_abs,
            "math.floor": math_floor,
            "math.ceil": math_ceil,
            "math.round": math_round,
            "math.sqrt": math_sqrt,
            "math.pow": math_pow,
            "math.exp": math_exp,
            "math.log": math_log,
            "math.sin": math_sin,
            "math.cos": math_cos,
            "math.tan": math_tan,
            "math.asin": math_asin,
            "math.acos": math_acos,
            "math.atan": math_atan,
            "math.atan2": math_atan2,
            "math.pi": math.pi,
            "math.e": math.e,
            # Random
            "random.random": random_random,
            "random.randint": random_randint,
            "random.uniform": random_uniform,
            "random.choice": random_choice,
            "random.shuffle": random_shuffle,
            "random.seed": random_seed,
            # Strings
            "str.split": str_split,
            "str.upper": str_upper,
            "str.lower": str_lower,
            "str.strip": str_strip,
            "str.lstrip": str_lstrip,
            "str.rstrip": str_rstrip,
            "str.replace": str_replace,
            "str.find": str_find,
            "str.rfind": str_rfind,
            "str.startswith": str_startswith,
            "str.endswith": str_endswith,
            "str.join": str_join,
            "str.format": str_format,
            "str.isalpha": str_isalpha,
            "str.isdigit": str_isdigit,
            "str.isalnum": str_isalnum,
            "str.isspace": str_isspace,
            # Type conversion with aliases
            "to_str": to_str,
            "to_int": to_int,
            "to_float": to_float,
            "to_bool": to_bool,
            "number": to_float,   # alias for to_float
            "int": to_int,        # alias for to_int
            "float": to_float,    # alias for to_float
            "str": to_str,        # alias for to_str
            "bool": to_bool,      # alias for to_bool
            # System
            "sys.argv": sys_argv,
            "sys.exit": sys_exit,
            "sys.getenv": sys_getenv,
            "sys.platform": sys_platform,
            "sys.cwd": sys_cwd,
            "sys.chdir": sys_chdir,
            # Internal
            "__mklist__": bw_mklist,
            "__mkdict__": bw_mkdict,
        }}

    def run(self):
        while True:
            if self.ip < 0 or self.ip >= len(self.code):
                raise RuntimeError("IP out of range")
            op, arg = self.code[self.ip]
            self.ip += 1

            if op == "PUSH_CONST":
                self.stack.append(arg)
            elif op == "LOAD":
                try:
                    v = self.lookup_var(arg)
                except:
                    continue
                self.stack.append(v)
            elif op == "STORE":
                val = None
                if self.stack:
                    val = self.stack.pop()
                self.store_var(arg, val)
            elif op == "STORE_CONST":
                val = None
                if self.stack:
                    val = self.stack.pop()
                self.store_const(arg, val)
            elif op == "PRINT":
                v = self.stack.pop() if self.stack else None
                print(v)
            elif op == "ADD":
                b = self.stack.pop(); a = self.stack.pop()
                if isinstance(a, str) or isinstance(b, str):
                    self.stack.append(str(a) + str(b))
                else:
                    self.stack.append(a + b)
            elif op == "SUB":
                b = self.stack.pop(); a = self.stack.pop(); self.stack.append(a - b)
            elif op == "MUL":
                b = self.stack.pop(); a = self.stack.pop(); self.stack.append(a * b)
            elif op == "DIV":
                b = self.stack.pop(); a = self.stack.pop()
                if b == 0:
                    err = ErrorObject("DivideByZeroError", "division by zero", 
                                    trace=self._build_trace())
                    self._raise_error(err); continue
                self.stack.append(a / b)
            elif op == "MOD":
                b = self.stack.pop(); a = self.stack.pop(); self.stack.append(a % b)
            elif op == "UNARY_NEG":
                a = self.stack.pop(); self.stack.append(-a)
            elif op == "NOT":
                a = self.stack.pop(); self.stack.append(not a)
            elif op == "AND":
                b = self.stack.pop(); a = self.stack.pop(); self.stack.append(a and b)
            elif op == "OR":
                b = self.stack.pop(); a = self.stack.pop(); self.stack.append(a or b)
            elif op == "CMP_EQ":
                b = self.stack.pop(); a = self.stack.pop(); self.stack.append(a == b)
            elif op == "CMP_NE":
                b = self.stack.pop(); a = self.stack.pop(); self.stack.append(a != b)
            elif op == "CMP_LT":
                b = self.stack.pop(); a = self.stack.pop(); self.stack.append(a < b)
            elif op == "CMP_GT":
                b = self.stack.pop(); a = self.stack.pop(); self.stack.append(a > b)
            elif op == "CMP_LE":
                b = self.stack.pop(); a = self.stack.pop(); self.stack.append(a <= b)
            elif op == "CMP_GE":
                b = self.stack.pop(); a = self.stack.pop(); self.stack.append(a >= b)
            elif op == "JMP":
                self.ip = arg
            elif op == "JMP_IF_FALSE":
                cond = None
                if self.stack:
                    cond = self.stack.pop()
                if not cond:
                    self.ip = arg
            elif op == "CALL":
                name, argc = arg
                args = []
                for _ in range(argc):
                    args.append(self.stack.pop())
                args.reverse()
                if name is None:
                    func_obj = self.stack.pop()
                    if isinstance(func_obj, tuple) and len(func_obj) == 2:
                        func_addr, params = func_obj
                        param_bindings = {{}}
                        for i, p in enumerate(params):
                            param_bindings[p] = args[i] if i < len(args) else None
                        ret_ip = self.ip
                        self.push_frame(ret_ip, param_bindings, func_name="<lambda>", 
                                      entry_ip=func_addr)
                        self.ip = func_addr
                        continue
                    else:
                        try:
                            res = func_obj(*args)
                            self.stack.append(res)
                        except Exception as e:
                            err = ErrorObject("RuntimeError", str(e), trace=self._build_trace())
                            self._raise_error(err)
                        continue
                elif name in self.functions:
                    func_addr, params = self.functions[name]
                    param_bindings = {{}}
                    for i, p in enumerate(params):
                        param_bindings[p] = args[i] if i < len(args) else None
                    ret_ip = self.ip
                    self.push_frame(ret_ip, param_bindings, func_name=name, entry_ip=func_addr)
                    self.ip = func_addr
                    continue
                fn = None
                if name in self.builtins:
                    fn = self.builtins[name]
                if fn:
                    try:
                        res = fn(*args)
                        self.stack.append(res)
                    except Exception as e:
                        err = ErrorObject("RuntimeError", str(e), trace=self._build_trace())
                        self._raise_error(err)
                    continue
                err = ErrorObject("ImportError", f"Unknown function '{{name}}'", 
                                trace=self._build_trace())
                self._raise_error(err)
                continue
            elif op == "CALL_ATTR":
                attr, argc = arg
                args = []
                for _ in range(argc):
                    args.append(self.stack.pop())
                args.reverse()
                obj = self.stack.pop() if self.stack else None
                method = None
                if isinstance(obj, dict):
                    if attr in obj:
                        method = obj[attr]
                    elif "funcs" in obj and attr in obj["funcs"]:
                        method = obj["funcs"][attr]
                if method is not None:
                    if isinstance(method, tuple) and len(method) == 2:
                        func_addr, params = method
                        param_bindings = {{}}
                        for i, p in enumerate(params):
                            param_bindings[p] = args[i] if i < len(args) else None
                        ret_ip = self.ip
                        self.push_frame(ret_ip, param_bindings, func_name=attr, entry_ip=func_addr)
                        self.ip = func_addr
                        continue
                    else:
                        try:
                            res = method(*args)
                            self.stack.append(res)
                        except Exception as e:
                            err = ErrorObject("RuntimeError", str(e), trace=self._build_trace())
                            self._raise_error(err)
                        continue
                err = ErrorObject("AttributeError", f"Object has no method '{{attr}}'", 
                                trace=self._build_trace())
                self._raise_error(err)
                continue
            elif op == "GET_ATTR":
                obj = self.stack.pop() if self.stack else None
                if isinstance(obj, dict):
                    if arg in obj:
                        self.stack.append(obj[arg])
                    elif "vars" in obj and arg in obj["vars"]:
                        self.stack.append(obj["vars"][arg])
                    elif "funcs" in obj and arg in obj["funcs"]:
                        self.stack.append(obj["funcs"][arg])
                    else:
                        err = ErrorObject("AttributeError", f"Object has no attribute '{{arg}}'", 
                                        trace=self._build_trace())
                        self._raise_error(err)
                elif isinstance(obj, ErrorObject):
                    if arg == "type":
                        self.stack.append(obj.type)
                    elif arg == "message":
                        self.stack.append(obj.message)
                    elif arg == "trace":
                        self.stack.append(obj.trace)
                    else:
                        err = ErrorObject("AttributeError", 
                                        f"Error object has no attribute '{{arg}}'", 
                                        trace=self._build_trace())
                        self._raise_error(err)
                else:
                    err = ErrorObject("AttributeError", 
                                    f"Cannot get attribute '{{arg}}' from non-object", 
                                    trace=self._build_trace())
                    self._raise_error(err)
            elif op == "RET":
                ret_val = None
                if self.stack:
                    ret_val = self.stack.pop()
                if len(self.frames) <= 1:
                    return
                ret_ip = self.frames[-1].return_ip
                self.pop_frame()
                self.stack.append(ret_val)
                self.ip = ret_ip
                continue
            elif op == "TRY":
                handler_ip, error_type, catch_var = arg
                ef = {{"handler_ip": handler_ip, "error_type": error_type,
                      "catch_var": catch_var, "frame_depth": self.current_frame_depth()}}
                self.exception_stack.append(ef)
            elif op == "THROW":
                if not self.stack:
                    err = ErrorObject("RuntimeError", "throw without error object", 
                                    trace=self._build_trace())
                    self._raise_error(err); continue
                errobj = self.stack.pop()
                if not isinstance(errobj, ErrorObject):
                    errobj = ErrorObject("RuntimeError", str(errobj), trace=self._build_trace())
                errobj.trace = self._build_trace()
                self._raise_error(errobj); continue
            elif op == "HALT":
                return
            else:
                raise RuntimeError(f"Unknown opcode: {{op}}")

    def _raise_error(self, errobj):
        while self.exception_stack:
            handler = self.exception_stack.pop()
            if handler["frame_depth"] > self.current_frame_depth():
                continue
            if self.error_matches(errobj, handler["error_type"]):
                while self.current_frame_depth() > handler["frame_depth"]:
                    self.pop_frame()
                self.ip = handler["handler_ip"]
                self.stack.append(errobj)
                return
        
        current_line = None
        if self.ip > 0 and self.ip - 1 < len(self.debug):
            _, current_line = self.debug[self.ip - 1]
        
        print(f"Uncaught error at line {{current_line or '?'}}: {{errobj}}")
        if isinstance(errobj, ErrorObject) and errobj.trace:
            print("Stack trace (most recent call last):")
            for fn, fn_file, fn_line in errobj.trace:
                if fn_file and fn_line:
                    print(f"  in {{fn}} at {{fn_file}}:{{fn_line}}")
                elif fn_file:
                    print(f"  in {{fn}} at {{fn_file}}")
                else:
                    print(f"  in {{fn}}")
        sys.exit(1)

# -----------------------
# Embedded Bytecode
# -----------------------
# OPCODE table (frozen)
OPCODES = (
    "PUSH_CONST",
    "LOAD",
    "STORE",
    "STORE_CONST",
    "PRINT",
    "ADD", "SUB", "MUL", "DIV", "MOD",
    "UNARY_NEG", "NOT",
    "AND", "OR",
    "CMP_EQ", "CMP_NE", "CMP_LT", "CMP_GT", "CMP_LE", "CMP_GE",
    "JMP", "JMP_IF_FALSE",
    "CALL", "RET",
    "GET_ATTR", "CALL_ATTR",
    "TRY", "THROW",
    "HALT",
)

OPCODE_TO_ID = {{op: i for i, op in enumerate(OPCODES)}}
ID_TO_OPCODE = {{i: op for op, i in OPCODE_TO_ID.items()}}

def load_embedded_bytecode():
    """Load the embedded bytecode from the compressed base85 data."""
    # Embedded bytecode data (compressed with zlib, encoded with base85)
    embedded_data = "{encoded}"
    
    # Decode and decompress
    compressed = base64.b85decode(embedded_data)
    pbc_data = zlib.decompress(compressed)
    
    # Parse the PBC format
    data = io.BytesIO(pbc_data)
    magic = data.read(4)
    if magic != b"PRMB":
        raise ValueError("Invalid embedded bytecode")
    ver = struct.unpack("B", data.read(1))[0]
    if ver != BYTECODE_VERSION:
        raise ValueError(f"Unsupported bytecode version: {{ver}}")
    meta_len = struct.unpack(">I", data.read(4))[0]
    meta_json = data.read(meta_len).decode("utf-8")
    meta = json.loads(meta_json)
    instr_count = struct.unpack(">I", data.read(4))[0]
    code = []
    for _ in range(instr_count):
        opid = struct.unpack(">H", data.read(2))[0]
        oplabel = ID_TO_OPCODE.get(opid, f"OP_{{opid}}")
        arg_len = struct.unpack(">I", data.read(4))[0]
        arg_json = data.read(arg_len).decode("utf-8")
        arg = json.loads(arg_json)
        code.append((oplabel, arg))
    
    functions = meta.get("functions", {{}})
    debug = meta.get("debug", [])
    filename = meta.get("filename", "<embedded>")
    exports = set(meta.get("exports", []))
    
    return code, functions, debug, filename, exports

# -----------------------
# Main Entry Point
# -----------------------
if __name__ == "__main__":
    print(f"PRIME Standalone Executable v{VERSION}")
    print(f"Source: {os.path.basename(source_path)}")
    print("---")
    
    try:
        # Load and run the embedded bytecode
        code, functions, debug, filename, exports = load_embedded_bytecode()
        vm = PrimeVM(code, functions, debug, exports, cwd=os.getcwd())
        vm.run()
    except Exception as e:
        print(f"Fatal error: {{e}}")
        sys.exit(1)
'''
    
    # Write the executable file
    with open(py_path, "w", encoding="utf-8") as f:
        f.write(exe_template)
    
    # Make it executable on Unix-like systems
    if os.name == 'posix':
        os.chmod(py_path, 0o755)
    
    print(f"✓ Created standalone Python script: {py_path}")
    print(f"  Size: {len(exe_template)} bytes")
    print(f"  Bytecode compressed: {len(pbc_data)} → {len(compressed)} bytes")
    print(f"  To run: python3 {py_path}")
    return True

# =======================
# UTILITY FUNCTIONS
# =======================

def compile_source_to_pbc(src, src_name, out_path):
    """
    Compile source code to .pbc file.
    
    Args:
        src: Source code string
        src_name: Source filename for debugging
        out_path: Output .pbc file path
    """
    tokens = tokenize(src)
    p = Parser(tokens, filename=src_name)
    code, functions, debug, exports = p.parse()
    em = p.em
    em.save_pbc(out_path)
    print(f"Compiled {src_name} -> {out_path} (version {VERSION})")

def run_source_text(src, src_name="<string>", cwd=None):
    """
    Compile and run source code text.
    
    Args:
        src: Source code string
        src_name: Source filename for debugging
        cwd: Current working directory for imports
        
    Returns:
        PrimeVM instance after execution
    """
    tokens = tokenize(src)
    p = Parser(tokens, filename=src_name)
    code, functions, debug, exports = p.parse()
    vm = PrimeVM(code, functions, debug, exports=exports, cwd=(cwd or os.getcwd()))
    vm.run()
    return vm

def run_pbc(path):
    """
    Run compiled bytecode from .pbc file.
    
    Args:
        path: Path to .pbc file
        
    Returns:
        PrimeVM instance after execution
    """
    code, functions, debug, filename, exports, version = Emitter.load_pbc(path)
    print(f"Running PBC {path} (version {version})")
    vm = PrimeVM(code, functions, debug, exports=exports, cwd=os.path.dirname(path) or os.getcwd())
    vm.run()
    return vm

def pretty(value):
    """
    Pretty-print value for REPL output.
    
    Args:
        value: Any value to format
        
    Returns:
        Formatted string representation
    """
    if isinstance(value, ErrorObject):
        return f"<{value.type}: {value.message}>"
    if isinstance(value, list):
        return "[" + ", ".join(pretty(x) for x in value) + "]"
    if isinstance(value, dict):
        items = ", ".join(f"{k}: {pretty(v)}" for k, v in value.items())
        return "{" + items + "}"
    if isinstance(value, str):
        return f'"{value}" (str)'
    return f"{value} ({type(value).__name__})"

# =======================
# REPL (Read-Eval-Print Loop)
# =======================

def needs_more_input(buffer):
    """
    Check if input needs more lines (for balanced braces).
    
    Args:
        buffer: Current input buffer
        
    Returns:
        True if more input needed (unbalanced braces)
    """
    # Simple balanced-brace check
    return buffer.count("{") > buffer.count("}")

def repl():
    """
    Start interactive REPL (Read-Eval-Print Loop).
    
    Features:
    - Balanced brace detection for multi-line input
    - Single-expression result printing
    - Persistent global state between inputs
    """
    print("PRIME REPL — finish input with an empty line. Ctrl+C to quit.")
    print(f"Version: {VERSION}")
    print("Type 'exit' or 'quit' to exit.")
    print("Examples:")
    print("  >>> let x = 10")
    print("  >>> x * 2  # expression is evaluated and printed")
    print("  >>> func add(a, b) { return a + b }")
    print("  >>> add(5, 3)")
    
    global_vm = None
    
    while True:
        try:
            lines = []
            open_braces = 0
            open_parens = 0
            open_brackets = 0
            
            # Read multi-line input
            while True:
                prompt = ">>> " if not lines else "... "
                try:
                    line = input(prompt)
                except EOFError:
                    print()
                    return
                    
                # Check for exit commands
                if line.strip().lower() in ("exit", "quit", ".exit", ".quit"):
                    print("Exiting REPL.")
                    return
                    
                lines.append(line)
                open_braces += line.count("{") - line.count("}")
                open_parens += line.count("(") - line.count(")")
                open_brackets += line.count("[") - line.count("]")
                
                # Stop when user enters a blank line and all are balanced
                if line.strip() == "" and open_braces <= 0 and open_parens <= 0 and open_brackets <= 0:
                    break
                    
            src = "\n".join(lines).strip()
            if not src:
                continue
                
            # Determine if it's an expression (not a statement)
            try:
                tokens = tokenize(src)
                # Skip EOF token
                non_eof = [t for t in tokens if t.type != "EOF"]
                is_expression = (
                    len(non_eof) > 0 and
                    non_eof[0].type != "KW" or
                    non_eof[0].value not in ("let", "func", "if", "attempt", "loop", 
                                            "for", "import", "export", "return", "say",
                                            "set", "const", "break", "continue", "throw")
                )
            except:
                is_expression = False
                
            # Parse and execute
            tokens = tokenize(src)
            p = Parser(tokens, filename="<repl>")
            code, functions, debug, exports = p.parse()
            
            if global_vm is None:
                # First input - create new VM
                vm = PrimeVM(code, functions, debug, exports=exports, cwd=os.getcwd())
                global_vm = vm
                vm.run()
                # Always print result if expression
                if is_expression and vm.stack:
                    val = vm.stack.pop()
                    if val is not None:
                        print(pretty(val))
            else:
                # Subsequent inputs - reuse global state
                vm = PrimeVM(code, functions, debug, exports=exports, cwd=os.getcwd())
                # Share global frame and functions
                vm.frames[0] = global_vm.frames[0]
                for k, v in global_vm.functions.items():
                    vm.functions.setdefault(k, v)
                vm.run()
                # Print result if expression
                if is_expression and vm.stack:
                    val = vm.stack.pop()
                    if val is not None:
                        print(pretty(val))
                # Sync global_vm
                global_vm = vm
                
        except KeyboardInterrupt:
            print("\nExiting REPL.")
            return
        except Exception as e:
            print(f"Error: {e}")

# =======================
# TEST HARNESS
# =======================

def capture_stdout(func, *args, **kwargs):
    """
    Capture stdout from function execution.
    
    Args:
        func: Function to execute
        *args: Function arguments
        **kwargs: Function keyword arguments
        
    Returns:
        Captured stdout as string
    """
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        func(*args, **kwargs)
    return buf.getvalue()

def assert_run_output(src, expected_output, cwd=None):
    """
    Run source code and assert output matches expected.
    
    Args:
        src: Source code string
        expected_output: Expected output string
        cwd: Current working directory for execution
        
    Raises:
        AssertionError: If output doesn't match expected
    """
    out = capture_stdout(lambda: run_source_text(src, "<assert>", cwd=cwd))
    out = out.strip()
    expected = expected_output.strip()
    assert out == expected, f"Assertion failed: expected:\n{expected}\n\nactual:\n{out}"

# Test programs for the test suite
TEST_PROGRAMS = {
    "and_short_circuit": (r'''
let side = 0
let ok = (side != 0) and (10 / side > 1)
attempt {
    if ok {
        say "ok"
    } else {
        say "not ok"
    }
} catch Error e {
    say "caught error while evaluating:", e.message
}
''', "not ok"),
    
    "or_short_circuit": (r'''
let called = 0
func r() {
    set called = called + 1
    return true
}
let res = true or r()
say called
''', "0"),
    
    "loop_from_to": (r'''
let sum = 0
loop i from 1 to 5 {
    set sum = sum + i
}
say sum
''', "15"),
    
    "loop_in_and_break_continue": (r'''
let arr = [1,2,3,4,5]
let s = 0
loop x in arr {
    if x == 3 {
        continue
    }
    if x == 5 {
        break
    }
    set s = s + x
}
say s
''', "7"),
    
    "equality_operators": (r'''
say 1 == 1
say 1 != 2
say "hello" == "hello"
say "hello" != "world"
''', "True\nTrue\nTrue\nTrue"),
    
    "list_indexing": (r'''
let arr = [10, 20, 30]
say arr[0]
say arr[1]
say arr[2]
''', "10\n20\n30"),
    
    "string_concatenation": (r'''
say "hello" + " " + "world"
say "num: " + 42
say 3.14 + " is pi"
''', "hello world\nnum: 42\n3.14 is pi"),
    
    "dictionary_literals": (r'''
let dict = {"name": "John", "age": 30}
say dict["name"]
say dict["age"]
''', "John\n30"),
    
    "dot_notation": (r'''
let obj = {"vars": {"x": 10}, "funcs": {"f": (0, [])}}
say obj.vars.x
''', "10"),
    
    "const_variables": (r'''
const pi = 3.14159
say pi
attempt {
    set pi = 3.14
    say "should not print"
} catch TypeError e {
    say "caught: " + e.message
}
''', "3.14159\ncaught: Cannot reassign const 'pi'"),
    
    "for_loop_alias": (r'''
let sum = 0
for x in [1,2,3,4] {
    set sum = sum + x
}
say sum
''', "10"),
    
    "name_error": (r'''
attempt {
    say undefined_variable
} catch NameError e {
    say "Caught NameError: " + e.message
}
''', "Caught NameError: Undefined variable: undefined_variable"),
    
    "attribute_error": (r'''
let obj = {}
attempt {
    say obj.nonexistent
} catch AttributeError e {
    say "Caught AttributeError: " + e.message
}
''', "Caught AttributeError: Object has no attribute 'nonexistent'"),
    
    # New tests for enhanced I/O
    "file_operations": (r'''
// Create test file
fs.write("test.txt", "Hello, World!")
let content = fs.read("test.txt")
say content
say fs.exists("test.txt")
say fs.isfile("test.txt")
// Clean up
fs.remove("test.txt")
''', "Hello, World!\ntrue\ntrue"),
    
    "math_operations": (r'''
say math.sqrt(16)
say math.pow(2, 8)
say math.round(3.14159, 2)
say math.pi > 3
''', "4.0\n256.0\n3.14\ntrue"),
    
    "string_operations": (r'''
let s = "  Hello, World!  "
say str.strip(s)
say str.upper("hello")
say str.lower("WORLD")
say str.replace("Hello World", "World", "PRIME")
''', "Hello, World!\nHELLO\nworld\nHello PRIME"),
    
    "time_operations": (r'''
let now = time.now()
say str.find(now, "-") > 0
let ts = time.timestamp()
say ts > 1000000000
''', "true\ntrue"),
    
    # New tests for read/input
    "read_input": (r'''
say "What's your name?"
let name = read()
say "Hello, " + name + "!"
''', ""),  # Will test with mock input
    
    # Test for # and /* */ comments
    "comments": (r'''
# This is a hash comment
let x = 1  // This is a double-slash comment
/* This is a
   block comment */
say x
''', "1"),
    
    # Test for let without initializer
    "let_without_initializer": (r'''
let x
say x == null
let y = 10
say y
''', "true\n10"),
    
    # Test for else if
    "else_if": (r'''
let score = 85
if score >= 90 {
    say "A"
} else if score >= 80 {
    say "B"
} else if score >= 70 {
    say "C"
} else {
    say "F"
}
''', "B"),
    
    # Test for type conversion aliases
    "type_conversion": (r'''
say number("3.14") + 1
say int("42")
say float("2.5")
say str(123)
say bool(1)
''', "4.14\n42\n2.5\n123\ntrue"),
}

def run_tests():
    """
    Run the full test suite.
    
    Returns:
        True if all tests pass, False otherwise
    """
    print("=== PRIME Test Suite (assertions) ===")
    print(f"Version: {VERSION}")
    all_passed = True
    
    # Run basic tests
    for name, (src, expected) in TEST_PROGRAMS.items():
        print(f"\n--- Test: {name} ---")
        try:
            # Special handling for read test
            if name == "read_input":
                # Mock input for testing
                import io
                import sys
                old_stdin = sys.stdin
                sys.stdin = io.StringIO("Test User\n")
                out = capture_stdout(lambda: run_source_text(src, "<assert>"))
                sys.stdin = old_stdin
                out = out.strip()
                expected = "What's your name?\nHello, Test User!"
                if out == expected:
                    print("OK")
                else:
                    print("FAIL: expected ->")
                    print(expected)
                    print("actual ->")
                    print(out)
                    all_passed = False
            else:
                assert_run_output(src, expected)
                print("OK")
        except AssertionError as e:
            print("FAIL:", e)
            all_passed = False
        except Exception as e:
            print(f"ERROR: {e}")
            all_passed = False
    
    # Import test: create temp module file, compile to pbc, import, assert output and cleanup
    print("\n--- Test: import_module (with exports and __init__) ---")
    tmpdir = tempfile.mkdtemp(prefix="prime_test_")
    try:
        mod_src = r'''
export { modfn, modval, __init__ }
export func modfn() { say "from module" }
export let modval = 99
export func __init__() { say "initialized" }
'''
        mod_path = os.path.join(tmpdir, "modtest.prime")
        with open(mod_path, "w", encoding="utf-8") as f:
            f.write(mod_src)
        out_pbc = os.path.join(tmpdir, "modtest.pbc")
        compile_source_to_pbc(mod_src, mod_path, out_pbc)
        prog = r'''
import modtest as m
m.funcs.modfn()
say m.vars.modval
'''
        out = capture_stdout(lambda: run_source_text(prog, "<test:import>", cwd=tmpdir))
        out = out.strip()
        expected = "initialized\nfrom module\n99"
        if out == expected:
            print("OK")
        else:
            print("FAIL: expected ->")
            print(expected)
            print("actual ->")
            print(out)
            all_passed = False
    except Exception as e:
        print("Import test failed:", e)
        all_passed = False
    finally:
        try:
            shutil.rmtree(tmpdir)
        except Exception:
            pass
    
    if all_passed:
        print("\n✅ All tests passed!")
    else:
        print("\n❌ Some tests failed!")
    return all_passed

# =======================
# COMMAND-LINE INTERFACE
# =======================

def print_help():
    """Print command-line usage help."""
    print(f"PRIME interpreter v{VERSION}")
    print("Usage:")
    print("  python3 prime.py <file.prime>                     # Run a PRIME program")
    print("  python3 prime.py --compile <file.prime> <out.pbc> # Compile to bytecode")
    print("  python3 prime.py --runpbc <file.pbc>              # Run compiled bytecode")
    print("  python3 prime.py --disasm <file.pbc>              # Disassemble bytecode")
    print("  python3 prime.py --verify <file.pbc>              # Verify bytecode integrity")
    print("  python3 prime.py --repl                           # Start interactive REPL")
    print("  python3 prime.py --test                           # Run test suite")
    print("  python3 prime.py --version                        # Show version info")
    print("  python3 prime.py --compile-exe <file.prime> <out.exe>  # Create standalone executable")
    print("  python3 prime.py --compile-py <file.prime> <out.py>    # Create standalone Python script")
    print("  python3 prime.py --help                           # Show this help")

def print_version():
    """Print version information."""
    print(f"PRIME Interpreter v{VERSION}")
    print(f"Bytecode Version: {BYTECODE_VERSION}")
    print("Opcode Table: FROZEN (0.1.2)")
    print("Features:")
    print("  - Explicit exports (export func/let/{a,b})")
    print("  - Module __init__ auto-run")
    print("  - Deterministic PBC format")
    print("  - Error hierarchy with NameError/AttributeError")
    print("  - REPL with brace balancing and expression auto-print")
    print("  - Test harness with temp modules")
    print("  - Standalone executable compilation")
    print("  - Enhanced standard library with:")
    print("    • read()/input() for user input")
    print("    • File I/O (read, write, append, list, copy, etc.)")
    print("    • Math functions (sqrt, pow, trig, etc.)")
    print("    • String operations (split, replace, format, etc.)")
    print("    • Time functions (now, sleep, format, parse)")
    print("    • Random number generation")
    print("    • System operations (env vars, platform, etc.)")
    print("    • Type conversion utilities (number, int, float, str, bool)")
    print("  - # and /* */ comment support")
    print("  - let without initializer (defaults to null)")
    print("  - else if chains")
    print("  - for loop alias")
    print("  - Better error messages with suggestions")

def main():
    """Main entry point for command-line interface."""
    parser = argparse.ArgumentParser(
        description=f"PRIME Interpreter v{VERSION}",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  prime.py hello.prime               # Run a PRIME program
  prime.py --compile hello.prime hello.pbc  # Compile to bytecode
  prime.py --repl                    # Start interactive REPL
  prime.py --test                    # Run test suite
        """
    )
    
    parser.add_argument("file", nargs="?", help="PRIME source file to run")
    parser.add_argument("--compile", nargs=2, metavar=("SOURCE", "OUTPUT"),
                       help="Compile source to bytecode (.pbc)")
    parser.add_argument("--compile-py", nargs=2, metavar=("SOURCE", "OUTPUT"),
                       help="Compile to standalone Python script")
    parser.add_argument("--compile-exe", nargs=2, metavar=("SOURCE", "OUTPUT"),
                       help="Create standalone executable")
    parser.add_argument("--runpbc", metavar="PBC_FILE", help="Run compiled bytecode")
    parser.add_argument("--disasm", metavar="PBC_FILE", help="Disassemble bytecode")
    parser.add_argument("--verify", metavar="PBC_FILE", help="Verify bytecode integrity")
    parser.add_argument("--repl", action="store_true", help="Start interactive REPL")
    parser.add_argument("--test", action="store_true", help="Run test suite")
    parser.add_argument("--version", action="store_true", help="Show version info")
    
    args = parser.parse_args()
    
    if args.version:
        print_version()
        sys.exit(0)
        
    if args.test:
        success = run_tests()
        sys.exit(0 if success else 1)
        
    if args.compile:
        src_path, out_path = args.compile
        with open(src_path, "r", encoding="utf-8") as f:
            src = f.read()
        compile_source_to_pbc(src, src_path, out_path)
        sys.exit(0)
        
    if args.compile_py:
        src_path, py_path = args.compile_py
        compile_to_py(src_path, py_path)
        sys.exit(0)
        
    if args.compile_exe:
        src_path, exe_path = args.compile_exe
        compile_to_exe(src_path, exe_path)
        sys.exit(0)
        
    if args.runpbc:
        run_pbc(args.runpbc)
        sys.exit(0)
        
    if args.disasm:
        disassemble_pbc(args.disasm)
        sys.exit(0)
        
    if args.verify:
        success = verify_pbc(args.verify)
        sys.exit(0 if success else 1)
        
    if args.repl:
        repl()
        sys.exit(0)
        
    if args.file:
        # Default: run as PRIME script
        with open(args.file, "r", encoding="utf-8") as f:
            src = f.read()
        run_source_text(src, args.file)
        sys.exit(0)
        
    # No arguments - show help
    parser.print_help()
    sys.exit(0)

if __name__ == "__main__":
    main()
