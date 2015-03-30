import ply.yacc as yacc
from ast import Asgn, BinOP, Var, Num, Inpt, Prnt, Block, If, While, UOP
from lexer import tokens
import sys
import logging
logging.basicConfig(
    level=logging.ERROR,
)
precedence = (
    ('left', 'OR'),
    ('left', 'AND'),
    ('nonassoc', 'EQ', 'LEQ', 'GEQ', 'LT', 'GT', 'NEQ'),
    ('left', 'PLUS', 'MINUS'),
    ('left', 'MULTIPLY', 'DIVIDE', 'MODULO'),
    ('right', 'NOT'),
    ('right', 'UMINUS'),
)
def p_top(p):
    'top : stmt_list'
    p[0] = p[1]
    p[0].is_top = True

def p_stmt_list_single(p):
    'stmt_list : stmt'
    p[0] = Block([p[1]], p.lineno(1))

def p_stmt_list(p):
    'stmt_list : stmt_list stmt'
    p[1] += p[2]
    p[0] = p[1]

def p_stmt(p):
    '''stmt : assign
            | print
            | block
            | if
            | while
    '''
    p[0] = p[1]

def p_assign(p):
    'assign : ID ASSIGN expr SEMICOLON'
    p[0] = Asgn(Var(p[1], p.lineno(1)), p[3], p.lineno(1))

def p_print(p):
    'print : PRINT LPAREN expr RPAREN SEMICOLON'
    p[0] = Prnt(p[3], p.lineno(1))

def p_block(p):
    'block : LBRACE stmt_list RBRACE'
    p[0] = p[2]

def p_if(p):
    '''if : IF expr THEN stmt ELSE stmt
          | IF expr THEN stmt
    '''
    if len(p) > 5 :
        p[0] = If(p[2], p[4], p[6], p.lineno(1))
    else :
        p[0] = If(p[2], p[4], None, p.lineno(1))

def p_while(p):
    'while : WHILE expr DO stmt'
    p[0] = While(p[2], p[4], p.lineno(1))

def p_expr_binop(p):
    '''expr : expr PLUS expr
            | expr MINUS expr
            | expr MULTIPLY expr
            | expr DIVIDE expr
            | expr MODULO expr
            | expr EQ expr
            | expr NEQ expr
            | expr LT expr
            | expr LEQ expr
            | expr GT expr
            | expr GEQ expr
            | expr AND expr
            | expr OR expr
    '''
    p[0] = BinOP(p[1], p[2], p[3], p.lineno(1))

def p_expr_number(p):
    'expr : NUMBER'
    p[0] = Num(p[1], p.lineno(1))

def p_expr_paren(p):
    'expr : LPAREN expr RPAREN'
    p[0] = p[1]

def p_expr_var(p):
    'expr : ID'
    p[0] = Var(p[1], p.lineno(1))

def p_expr_uop(p):
    '''expr : NOT expr
            | MINUS expr %prec UMINUS
    '''
    p[0] = UOP(p[1], p[2], p.lineno(1))
def p_expr_input(p):
    'expr : INPUT LPAREN RPAREN'
    p[0] = Inpt(p.lineno(1))

def p_error(p):
    raise Exception("Syntax error, unexpected '{0}' at line {1}".format(p.value, p.lineno))

parser = yacc.yacc()

if __name__ == "__main__" :
    f = open(sys.argv[1], "r")
    log = logging.getLogger()
    res = parser.parse(f.read(), debug=log)
    print(res)
    print(res.wellformed(set()))
