import ply.yacc as yacc
from ast import Asgn, BinOP, Var, Num, Inpt, Prnt, Block, If, Loop, UOP, Inc, Decl, Type, Dim, New, ArrIndx
from lexer import tokens
import sys
import logging
precedence = (
    ('right', 'ASSIGN'),
    ('left', 'OR'),
    ('left', 'AND'),
    ('nonassoc', 'EQ', 'LEQ', 'GEQ', 'LT', 'GT', 'NEQ'),
    ('left', 'PLUS', 'MINUS'),
    ('left', 'MULTIPLY', 'DIVIDE', 'MODULO'),
    ('right', 'NOT'),
    ('right', 'UMINUS'),
)

def p_prgm(p):
    'prgm : decl_list stmt_list'
    p[0] = Block(p[2], p[1], p.lineno(1))
    p[0].is_top = True

def p_empty(p):
    'empty : '
    p[0] = None

def p_decl_list(p):
    'decl_list : decl decl_list'
    p[2].append(p[1])
    p[0] = p[2]

def p_decl_list_empty(p):
    'decl_list : empty'
    p[0] = []

def p_type(p):
    '''type : INT
            | BOOL'''
    p[0] = Type(p[1])

def p_decl(p):
    'decl : type var_list SEMICOLON'
    p[0] = Decl(p[1], p[2])

def p_var_list(p):
    'var_list : var COMMA var_list'
    p[3].append(p[1])
    p[0] = p[3]

def p_var_list_single(p):
    'var_list : var'
    p[0] = [p[1]]

def p_var(p):
    'var : ID dimstar'
    p[0] = Var(p[1], p.lineno(1))

def p_stmt_list_empty(p):
    'stmt_list : empty'
    p[0] = []

def p_stmt_list(p):
    'stmt_list : stmt_list stmt'
    p[1].append(p[2])
    p[0] = p[1]

def p_stmt(p):
    '''stmt : assign SEMICOLON
            | print SEMICOLON
            | block
            | if
            | loop
    '''
    p[0] = p[1]

def p_lvalue_id(p):
    'lvalue : ID'
    p[0] = Var(p[1], p.lineno(1))
def p_lvalue_arr(p):
    'lvalue : lvalue LBRACKET expr RBRACKET'
    p[0] = ArrIndx(p[1], p[3], linenum=p.lineno(1))

def p_assign(p):
    'assign : lvalue ASSIGN expr'
    p[0] = Asgn(p[1], p[3], p.lineno(1))

def p_assign_incdec_post(p):
    '''assign : lvalue INC
              | lvalue DEC
    '''
    if p[2] == '++':
        p[0] = Inc(p[1], 1, 0)
    else :
        p[0] = Inc(p[1], 1, 1)
def p_assign_incdec_pre(p):
    '''assign : INC lvalue
              | DEC lvalue
    '''
    if p[1] == '++':
        p[0] = Inc(p[2], 0, 0)
    else :
        p[0] = Inc(p[2], 0, 1)
def p_print(p):
    'print : PRINT LPAREN expr RPAREN'
    p[0] = Prnt(p[3], p.lineno(1))

def p_block(p):
    'block : LBRACE decl_list stmt_list RBRACE'
    p[0] = Block(p[3], p[2], p.lineno(1))

def p_if(p):
    '''if : IF expr THEN stmt ELSE stmt
          | IF expr THEN stmt
    '''
    if len(p) > 5 :
        p[0] = If(p[2], p[4], p[6], p.lineno(1))
    else :
        p[0] = If(p[2], p[4], None, p.lineno(1))

def p_while(p):
    'loop : WHILE expr DO stmt'
    p[0] = Loop((p[2], 0), p[4], linenum=p.lineno(1))

def p_do_while(p):
    'loop : DO stmt WHILE expr SEMICOLON'
    p[0] = Loop((p[4], 1), p[2], linenum=p.lineno(1))

def p_assign_or_empty(p):
    '''assign_or_empty : assign
                       | empty '''
    p[0] = p[1]

def p_for(p):
    'loop : FOR LPAREN assign_or_empty SEMICOLON expr SEMICOLON assign_or_empty RPAREN stmt'
    p[0] = Loop((p[5], 0), p[9], pre=p[3], post=p[7], linenum=p.lineno(1))

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

def p_expr_bool(p):
    '''expr : FALSE
            | TRUE'''
    if p[1] == 'true':
        p[0] = Num(1, p.lineno(1))
    else :
        p[0] = Num(0, p.lineno(1))

def p_expr_paren(p):
    'expr : LPAREN expr RPAREN'
    p[0] = p[2]

def p_expr_asgn(p):
    'expr : assign'
    p[0] = p[1]

def p_expr_var(p):
    'expr : lvalue'
    p[0] = p[1]

def p_expr_uop(p):
    '''expr : NOT expr
            | MINUS expr %prec UMINUS
    '''
    p[0] = UOP(p[1], p[2], p.lineno(1))
def p_expr_input(p):
    'expr : INPUT LPAREN RPAREN'
    p[0] = Inpt(p.lineno(1))

def p_dim(p):
    'dim : LBRACKET expr RBRACKET'
    p[0] = Dim(p[2], 0)

def p_dimstar(p):
    'dimstar : dimstar LBRACKET RBRACKET'
    p[0] = p[1]+1

def p_dimstar_empty(p):
    'dimstar : empty'
    p[0] = 0

def p_expr_new(p):
    'expr : NEW type dim dimstar'
    p[3].star = p[4]
    p[0] = New(p[2], p[3])

def p_error(p):
    raise Exception("Syntax error, unexpected '{0}' at line {1}".format(p.value, p.lineno))

parser = yacc.yacc()

if __name__ == "__main__" :
    f = open(sys.argv[1], "r")
    logging.basicConfig(
        level=logging.ERROR,
    )
    log = logging.getLogger()
    res = parser.parse(f.read(), debug=log)
    print(res)
    print(res.wellformed(set()))
