#!/usr/bin/python
import ply.lex as lex
import sys
reserved = {
   'if' : 'IF',
   'then' : 'THEN',
   'else' : 'ELSE',
   'while' : 'WHILE',
   'input' : 'INPUT',
   'print' : 'PRINT',
   'do' : 'DO',
   'for' : 'FOR',
   'new' : 'NEW',
   'true' : 'TRUE',
   'false' : 'FALSE',
   'int' : 'INT',
   'bool' : 'BOOL',
}

tokens = ['LPAREN', 'RPAREN', 'ASSIGN', 'NOT', 'PLUS', 'MINUS', 'MULTIPLY', 'DIVIDE', 'MODULO', 'AND', 'OR', 'EQ', 'NEQ',
          'LT', 'LEQ', 'GT', 'GEQ', 'LBRACE', 'RBRACE', 'SEMICOLON', 'ID', 'NUMBER', 'INC', 'DEC', 'COMMA'] + list(reserved.values())

t_PLUS    = r'\+'
t_MINUS   = r'-'
t_MULTIPLY   = r'\*'
t_DIVIDE  = r'/'
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_LBRACE = r'{'
t_RBRACE = r'}'
t_MODULO = r'%'
t_AND = r'&&'
t_OR = r'\|\|'
t_EQ = r'=='
t_NEQ = r'!='
t_LT = r'<'
t_LEQ = r'<='
t_GT = r'>'
t_GEQ = r'>='
t_NOT = r'!'
t_SEMICOLON = r';'
t_ASSIGN = r'='
t_INC = r'\+\+'
t_DEC = r'--'
t_COMMA = r','

def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    t.type = reserved.get(t.value, 'ID')    # Check for reserved words
    return t

# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_NUMBER(t):
    r'\d+'
    t.value = int(t.value)
    return t

# Error handling rule
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

t_ignore  = ' \t'

lexer = lex.lex()

def g_token(lexer):
    while True :
        t = lexer.token()
        if not t:
            return None
        yield t

if __name__ == '__main__':
    f = open(sys.argv[1], "r")
    lexer.input(f.read())
    for tok in g_token(lexer):
        print("(%s,%r,%d,%d)" % (tok.type, tok.value, tok.lineno,tok.lexpos))
