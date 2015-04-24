import ply.yacc as yacc
from lexer import tokens
import ast.ast as ast
import ast.symbol as sym
import ast.expr as expr
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
    'prgm : decl_list'
    p[0] = ast.Program(p[1])

def p_param(p):
    'param : type var'
    p[0] = p[2]

def p_param_list(p):
    'param_list : param_list COMMA param'
    p[1].append(p[3])
    p[0] = p[1]

def p_param_list_single(p):
    'param_list : param'
    p[0] = [p[1]]

def p_param_list_star(p):
    '''param_list_star : param_list
                       | empty'''
    if p[1] is None:
        p[0] = []
    else :
        p[0] = p[1]

def p_args_more(p):
    'arg_plus : arg_plus COMMA expr'
    p[1].append(p[3])
    p[0] = p[1]

def p_args_one(p):
    'arg_plus : expr'
    p[0] = [p[1]]

def p_args(p):
    '''args : arg_plus
            | empty'''
    p[0] = p[1]

def p_fn(p):
    'fn : type ID LPAREN param_list_star RPAREN stmt'
    body = p[6]
    if not isinstance(body, ast.Block):
        body = ast.Block([p[6]], [], p[6].linenum)
    p[0] = ast.Fn(p[2], p[4], p[1], body, p.lineno(1))
    body.is_top = True

def p_empty(p):
    'empty : '
    p[0] = None

def p_decl_list(p):
    'decl_list : decl_list decl'
    p[1].append(p[2])
    p[0] = p[1]

def p_decl_list_empty(p):
    'decl_list : empty'
    p[0] = []

def p_decl(p):
    '''decl : fn
            | var_decl'''
    p[0] = p[1]

def p_type(p):
    '''type : INT
            | BOOL'''
    p[0] = sym.Type(p[1])

def p_type_void(p):
    'type : VOID'
    p[0] = sym.VoidTy()

def p_var_decl_list(p):
    'var_decl_list : var_decl_list var_decl'
    p[1] += p[2]
    p[0] = p[1]

def p_var_decl_list_empty(p):
    'var_decl_list : empty'
    p[0] = []

def p_var_decl(p):
    'var_decl : type var_list SEMICOLON'
    for v in p[2]:
        v.ty = p[1]
    p[0] = p[2]

def p_var_list(p):
    'var_list : var COMMA var_list'
    p[3].append(p[1])
    p[0] = p[3]

def p_var_list_single(p):
    'var_list : var'
    p[0] = [p[1]]

def p_var(p):
    'var : ID dimstar'
    p[0] = expr.Var(p[1], p.lineno(1))

def p_stmt_list_empty(p):
    'stmt_list : empty'
    p[0] = []

def p_stmt_list(p):
    'stmt_list : stmt_list stmt'
    p[1].append(p[2])
    p[0] = p[1]

def p_stmt(p):
    '''stmt : assign SEMICOLON
            | call SEMICOLON
            | print
            | block
            | if
            | loop
            | return
    '''
    p[0] = p[1]

def p_lvalue_id(p):
    'lvalue : ID'
    p[0] = expr.Var(p[1], p.lineno(1))
def p_lvalue_arr(p):
    'lvalue : lvalue LBRACKET expr RBRACKET'
    p[0] = expr.ArrIndx(p[1], p[3], linenum=p.lineno(1))

def p_return(p):
    'return : RETURN expr SEMICOLON'
    p[0] = ast.Return(p[2], p.lineno(1))

def p_return_void(p):
    'return : RETURN SEMICOLON'
    p[0] = ast.Return(None, p.lineno(1))

def p_assign(p):
    'assign : lvalue ASSIGN expr'
    p[0] = expr.Asgn(p[1], p[3], p.lineno(1))

def p_call(p):
    'call : ID LPAREN args RPAREN'
    p[0] = expr.Call(p[1], p[3], p.lineno(1))

def p_assign_incdec_post(p):
    '''assign : lvalue INC
              | lvalue DEC
    '''
    if p[2] == '++':
        p[0] = expr.Inc(p[1], 1, 0)
    else :
        p[0] = expr.Inc(p[1], 1, 1)
def p_assign_incdec_pre(p):
    '''assign : INC lvalue
              | DEC lvalue
    '''
    if p[1] == '++':
        p[0] = expr.Inc(p[2], 0, 0)
    else :
        p[0] = expr.Inc(p[2], 0, 1)
def p_print(p):
    'print : PRINT LPAREN expr RPAREN SEMICOLON'
    p[0] = ast.Prnt(p[3], p.lineno(1))

def p_block(p):
    'block : LBRACE var_decl_list stmt_list RBRACE'
    p[0] = ast.Block(p[3], p[2], p.lineno(1))

def p_if(p):
    '''if : IF expr THEN stmt ELSE stmt
          | IF expr THEN stmt
    '''
    if len(p) > 5 :
        p[0] = ast.If(p[2], p[4], p[6], p.lineno(1))
    else :
        p[0] = ast.If(p[2], p[4], None, p.lineno(1))

def p_while(p):
    'loop : WHILE expr DO stmt'
    p[0] = ast.Loop((p[2], 0), p[4], linenum=p.lineno(1))

def p_do_while(p):
    'loop : DO stmt WHILE expr SEMICOLON'
    p[0] = ast.Loop((p[4], 1), p[2], linenum=p.lineno(1))

def p_assign_or_empty(p):
    '''assign_or_empty : assign
                       | empty '''
    p[0] = p[1]

def p_for(p):
    'loop : FOR LPAREN assign_or_empty SEMICOLON expr SEMICOLON assign_or_empty RPAREN stmt'
    p[0] = ast.Loop((p[5], 0), p[9], pre=p[3], post=p[7], linenum=p.lineno(1))

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
    p[0] = expr.BinOP(p[1], p[2], p[3], p.lineno(1))

def p_expr_number(p):
    'expr : NUMBER'
    p[0] = expr.Num(p[1], p.lineno(1))

def p_expr_bool(p):
    '''expr : FALSE
            | TRUE'''
    if p[1] == 'true':
        p[0] = expr.Num(1, p.lineno(1))
    else :
        p[0] = expr.Num(0, p.lineno(1))

def p_expr_paren(p):
    'expr : LPAREN expr RPAREN'
    p[0] = p[2]

def p_expr_val(p):
    '''expr : assign
            | lvalue
            | call'''
    p[0] = p[1]

def p_expr_uop(p):
    '''expr : NOT expr
            | MINUS expr %prec UMINUS
    '''
    p[0] = expr.UOP(p[1], p[2], p.lineno(1))
def p_expr_input(p):
    'expr : INPUT LPAREN RPAREN'
    p[0] = expr.Inpt(p.lineno(1))

def p_dim(p):
    'dim : LBRACKET expr RBRACKET'
    p[0] = ast.Dim(p[2], 0)

def p_dimstar(p):
    'dimstar : dimstar LBRACKET RBRACKET'
    p[0] = p[1]+1

def p_dimstar_empty(p):
    'dimstar : empty'
    p[0] = 0

def p_expr_new(p):
    'expr : NEW type dim dimstar'
    p[3].star = p[4]
    p[0] = expr.New(p[2], p[3])

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
