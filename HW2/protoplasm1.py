#!/usr/bin/env python
import tokenize
import sys
import re
from instruction import Ins
from IR import IR, nreg

def error(st):
        raise Exception("Unexpected {0}({1}) at {2}, {3}".
                        format(st[1], st[0], st[2][0], st[2][1]))
class VarVer: 
    #this class is used to keep track of variable version
    #since we are using SSA here
    def __init__(self):
        self.d = {}
    def next_ver(self, name):
        if name not in self.d:
            self.d[name] = 0
        else :
            self.d[name] += 1
        return name+"."+str(self.d[name])
    def curr_ver(self, name):
        assert name in self.d
        return name+"."+str(self.d[name])

#methods of AST classes:
# reduce: used to create AST class from symbols
# emit: emit the intermediate code

class Asgn:
    lhs = None
    rhs = None
    def __str__(self):
        return "Asgn({0} = {1})".format(self.lhs, self.rhs)
    def __init__(self, lhs, rhs):
        assert isinstance(lhs, Var)
        self.lhs = lhs
        self.rhs = rhs
    @staticmethod
    def reduce(stack):
        return Asgn(Var(stack[0][1]), Expr.reduce(stack[1 :]))
    def emit(self, varv):
        return self.rhs.emit(varv, self.lhs.name)


class Expr:
    lopr = None
    ropr = None
    op = None
    def emit(self, varv, dst):
        opc = {"+": 1, "-": 2, "*": 3, "//": 4, "%": 5}
        if (isinstance(self.lopr, Num)):
            if (isinstance(self.ropr, Num)):
                #Constant expr
                dst = varv.next_ver(dst)
                rst = eval(str(self.lopr.number)+self.op+str(self.ropr.number))
                return [Ins(6, [dst, rst])]
            else :
                src1 = varv.curr_ver(self.ropr.name)
                dst = varv.next_ver(dst)
                return [Ins(opc[self.op], [dst, src1, self.lopr.number])]
        else :
            if (isinstance(self.ropr, Num)):
                src1 = varv.curr_ver(self.lopr.name)
                dst = varv.next_ver(dst)
                return [Ins(opc[self.op], [dst, src1, self.ropr.number])]
            else :
                src1 = varv.curr_ver(self.lopr.name)
                src2 = varv.curr_ver(self.ropr.name)
                dst = varv.next_ver(dst)
                return [Ins(opc[self.op], [dst, src1, src2])]


    def __str__(self):
        return "Expr({0},{1},{2})".format(self.lopr, self.op, self.ropr)
    def __init__(self, opr1, op, opr2, pos):
        self.lopr = opr1
        self.ropr = opr2
        if op != "+" and op != "-" and op != "*" and op != "/" and op != "%":
            raise Exception("Invalid operator {0} at {1}, {2}".
                                            format(op, pos[0], pos[1]))
        if op != "/":
            self.op = op
        else :
            self.op = "//"
    @staticmethod
    def reduce(stack):
        if len(stack) == 1 :
            if stack[0][0] == tokenize.NUMBER:
                return Num(stack[0][1])
            elif stack[0][0] == tokenize.NAME:
                return Var(stack[0][1])
            else :
                error(stack[0])
        elif len(stack) == 3 :
            return Expr(Expr.reduce([stack[0]]),
                                    stack[1][1],
                                    Expr.reduce([stack[2]]), stack[1][2])
        else :
            raise Exception("Invalid expression at {0}, {1}".format(
                stack[0][2][0], stack[0][2][1]
            ))

class Var:
    name = ""
    def emit(self, varv, dst):
        src = varv.curr_ver(self.name)
        dst = varv.next_ver(dst)
        return [Ins(6, [dst, src])]
    def __init__(self, name):
        self.name = name
    def __str__(self):
        return "Var({0})".format(self.name)
    def __eq__(self, other):
        return self.name == other.name
    def __hash__(self):
        return self.name.__hash__()

class Num:
    number = 0
    def emit(self, varv, dst):
        dst = varv.next_ver(dst)
        return [Ins(6, [dst, self.number])]
    def __str__(self):
        return "Num({0})".format(self.number)
    def __init__(self, num):
        if isinstance(num, str):
            self.number = int(num)
        elif isinstance(num, int):
            self.number = num
        else :
            raise Exception("num is not a number???")

class Inpt:
    lhs = ""
    def __str__(self):
        return "Input({0})".format(self.lhs)
    def __init__(self, lhs):
        self.lhs = lhs
    def emit(self, varv):
        dst = varv.next_ver(self.lhs.name)
        return [Ins(0, [dst])]
    @staticmethod
    def reduce(stack):
        #Some checks
        if stack[1][1] != "(":
            error(stack[1])
        sl = len(stack)
        for n, v in enumerate(stack):
            if v[1] == ")" and n != sl-1 :
                raise Exception("Garbage after ')' in a input statement, at {0}, {1}".
                                                format(stack[n+1][2][0], stack[n+1][2][1]))
        if len(stack) != 3 :
            raise Exception("Arguments passed to input statement, at {0}, {1}".
                                            format(stack[2][2][0], stack[2][2][1]))
        return Inpt(Var(stack[0][1]))

class Prnt:
    expr = ""
    def __str__(self):
        return "Print({0})".format(self.expr)
    def __init__(self, expr):
        self.expr = expr
    def emit(self, varv):
        rst = []
        if isinstance(self.expr, Num):
            rst += [Ins(7, [self.expr.number])]
        else :
            rst += self.expr.emit(varv, "print")
            rst += [Ins(7, [varv.curr_ver("print")])]
        return rst

    @staticmethod
    def reduce(stack):
        #Some checks
        if stack[0][1] != "(":
            error(stack[0])
        sl = len(stack)
        for n, v in enumerate(stack):
            if v[1] == ")" and n != sl-1 :
                raise Exception("Garbage after ')' in a print statement, at {0}, {1}".
                                                format(stack[n+1][2][0], stack[n+1][2][1]))
        if sl != 3 and sl != 5 :
            raise Exception("Argument passed to print is not a number, a variable or "
                        "a valid expr, line {0}".format(stack[0][2][0]))
        return Prnt(Expr.reduce(stack[1 : -1]))

class AST:
    def wellformed(self):
        defined = set([])
        for w, linenum in self.expr_list:
            chk = None
            if isinstance(w, Prnt):
                chk = w.expr
            elif isinstance(w, Asgn):
                defined |= {w.lhs}
                chk = w.rhs
            elif isinstance(w, Inpt):
                defined |= {w.lhs}
            if isinstance(chk, Expr):
                if (isinstance(chk.lopr, Var) and
                        chk.lopr not in defined):
                    print("{0} not defined before line {1}".format(
                        chk.lopr, linenum
                    ))
                    return False
                if (isinstance(chk.ropr, Var) and
                        chk.ropr not in defined):
                    print("{0} not defined before line {1}".format(
                        chk.ropr, linenum
                    ))
                    return False
            if isinstance(chk, Var):
                if chk not in defined:
                    print("{0} not defined before line {1}".format(
                        chk, linenum
                    ))
                    return False
        return True
    expr_list = []
    def __init__(self, elist):
        self.expr_list = elist
    def gencode(self):
        assert self.wellformed()
        res = IR()
        varv = VarVer()
        for e, _ in self.expr_list:
            res += e.emit(varv)
        return res
    def __iadd__(self, obj):
        self.expr_list += [obj]
        return self
    def __str__(self):
        res = "["
        for w, _ in self.expr_list:
            res += str(w)
            res += ", "
        res += "]"
        return res


def parse(filename):
    f = open(filename, "rb")
    state = 0
    step = 0
    stack = []
    ast = AST([])
    for toknum, tokval, start, _, _ in tokenize.tokenize(f.readline):
        #Sort of a push down automaton, but not really
        #state is what rule should we apply:
        #      = 1 : print statement
        #      = 3 : input statement
        #      = 4 : assignment
        #      = 2 : undecided, wait for more symbol

        #when shift, new symbol is push into stack
        #when reduce, the classes' reduce method is called
        if toknum == tokenize.ENCODING:
            continue
        if toknum == tokenize.NEWLINE:
            continue
        if toknum == tokenize.ENDMARKER:
            if state != 0 :
                raise Exception("Unexpected end of file")
        if tokval == ";" or toknum == tokenize.ENDMARKER:
            if state == 1 :
                tmp = Prnt.reduce(stack)
            elif state == 3 :
                tmp = Inpt.reduce(stack)
            elif state == 4 :
                tmp = Asgn.reduce(stack)
            elif state != 0 :
                raise Exception("Unexpected ';' at line {0}".format(start[0]))
            if state != 0 :
                ast += (tmp, start[0])
            state = 0
            stack = []
            continue
        if state == 0 :
            #beginning of a line
            if tokval == "print":
                state = 1
            elif toknum == tokenize.NAME:
                state = 2
                step = 0
                stack = [(toknum, tokval, start)]
            else :
                error((toknum, tokval, start))
        elif state == 1 :
            stack = stack + [(toknum, tokval, start)]
        elif state == 2 :
            if step == 0 :
                if tokval == "=":
                    step = 1
                else :
                    error((toknum, tokval, start))
            elif step == 1 :
                if tokval == "input":
                    state = 3
                else :
                    state = 4
                    stack += [(toknum, tokval, start)]
        else :
            stack += [(toknum, tokval, start)]
    return ast

def main():
    global nreg
    _mynreg = nreg
    if len(sys.argv) > 2:
        _mynreg = int(sys.argv[2])
    else :
        print("If you want, you can specify a second argument to limit the total"
              " number of registers, minimum is 2, maximum is %d" % nreg)
    if _mynreg < 2 :
        _mynreg = 2
    if _mynreg > nreg :
        _mynreg = nreg
    try :
        __tmp = parse(sys.argv[1])
    except Exception as _e:
        print("Parse error: {0}".format(_e))
        sys.exit(1)
    outf = re.sub(r'\.[^.]*$', '.asm', sys.argv[1])
    print("AST:\n{0}".format(__tmp))
    wf = __tmp.wellformed()
    print("Is AST well formed?\n{0}".format(wf))
    if not wf :
        sys.exit(1)
    ir = __tmp.gencode()
    print("IR:\n{0}".format(ir))
    ir.gencode(_mynreg, outf)

if __name__ == "__main__":
    main()
