import IR.instruction as IRI
import IR.operand as IRO
import logging
from . import symbol as sym
class Expr:
    cont = True
    @property
    def is_constant(self):
        return False
    def get_result_const(self, *_):
        assert False
    def get_result_noconst(self, *_):
        assert False
    def get_result(self, st, ir, noconst=False):
        assert isinstance(noconst, bool)
        if self.is_constant:
            res = self.get_result_const(st, ir)
            if noconst:
                n = st.allocator.next_name()
                bb = ir.last_bb
                bb += [IRI.Load(n, res, c=str(self))]
                return n
            return res
        return self.get_result_noconst(st, ir)
    def get_modified(self, _=False):
        return set()

class Call(Expr):
    def __init__(self, name, args, linenum=0):
        self.name = name
        self.args = args
        self.linenum = linenum
    def __str__(self):
        res = "Call(%s" % self.name
        for arg in self.args:
            res += ", %s" % arg
        res += ")"
        return res
    def _get_result(self, st, fn, res):
        args = []
        for arg in self.args:
            args.append(arg.get_result(st, fn))
        bb = fn.last_bb
        bb += [IRI.Invoke(self.name, args, res)]
    def get_result_noconst(self, st, fn):
        res = st.allocator.next_name()
        self._get_result(st, fn, res)
        return res
    def get_modified(self, either=False):
        mod = set()
        for arg in self.args:
            mod |= arg.get_modified()
        return mod
    def emit(self, st, fn):
        #as a statement
        self._get_result(st, fn, None)
    def wellformed(self, st, defined, _=None):
        if self.name not in st.globs:
            logging.error("Function '%s' not declared\n", self.name)
            return False
        func = st.globs[self.name]
        if not func.ty == sym.FnTy():
            logging.error("Trying to call non-function '%s', line %d", self.name,
                          self.linenum)
            return False
        if len(self.args) != len(func.params):
            logging.error("Function '%s' take %d arguments, but got %d, line %d",
                          self.name, len(func.params), len(self.args), self.linenum)
            return False
        for i, arg in enumerate(self.args):
            if not arg.wellformed(st, defined):
                return False
            if not arg.ty == func.params[i].ty:
                logging.error("Argument %d to function '%s' has type '%s', '%s' expected, line %d",
                              i, self.name, arg.ty, func.params[i].ty, self.linenum)
                return False
        self.ty = func.rety
        return True

class New(Expr):
    def __init__(self, t, dim, depth, linenum=0):
        self.t = t
        self.dim = dim
        self.depth = depth
        self.linenum = linenum
    def __str__(self):
        return "New(%s, [%s], []*%d)" % (self.t, self.dim, self.depth)
    @property
    def is_constant(self):
        return False
    def get_result_noconst(self, st, ir):
        res = self.dim.get_result(st, ir, True)
        ndst = st.allocator.next_name()
        bb = ir.last_bb
        #calc (size+1) and (size+1)*4
        szp1 = st.allocator.next_name()
        szp1m4 = st.allocator.next_name()
        bb += [IRI.Arithm('+', szp1, res, 1), IRI.Arithm('*', szp1m4, szp1, 4)]
        bb += [IRI.Invoke("malloc", [szp1m4], ndst, c=str(self))]
        #store the size of the array
        bb += [IRI.Store(IRO.Cell(0, base=ndst), res)]
        ndst2 = st.allocator.next_name()
        bb += [IRI.Arithm('+', ndst2, ndst, 4)]
        return ndst2
    def wellformed(self, st, defined):
        if not self.dim.wellformed(st, defined):
            return False
        if not self.dim.ty == sym.Type('int'):
            logging.error("Array size can't be type %s, line %d", self.dim.ty, self.linenum)
            return False
        ty = sym.ArrayTy(self.t)
        for i in range(0, self.depth):
            ty = sym.ArrayTy(ty)
        self.ty = ty
        return True
    def get_modified(self, either):
        return self.dim.get_modified(either)

class Inc(Expr):
    def __init__(self, lval, pos, op, linenum=None):
        self.pos = pos
        self.op = op
        self.lval = lval
        self.res = None
        self.linenum = linenum
    def __str__(self):
        insn = ['Inc', 'Dec']
        pos = ['Pre', 'Post']
        return "%s%s(%s)" % (pos[self.pos], insn[self.op], self.lval)
    @property
    def is_constant(self):
        return False
    def emit(self, st, ir):
        opn = ['+', '-']
        if not self.res:
            opr = self.lval.get_result(st, ir)
            self.res = opr
            cdst = st.allocator.next_name()
            bb = ir.last_bb
            bb += [IRI.Arithm(opn[self.op], cdst, opr, 1, c=str(self))]
            if self.pos == 0: #pre
                self.res = cdst
            self.lval.assign(st, ir, cdst)
    def get_result_noconst(self, st, ir):
        self.emit(st, ir)
        return self.res
    def wellformed(self, st, dfn, _=None):
        if not self.lval.wellformed(st, dfn):
            return False
        opn = ['++', '--']
        if not self.lval.ty == sym.Type('int'):
            logging.error("'%s' is not defined for type %s, line %d", opn[self.op],
                          self.lval.ty, self.linenum)
            return False
        self.ty = self.lval.ty
        return True
    def get_modified(self, _=False):
        dfn = self.lval.get_modified()
        if isinstance(self.lval, Var):
            dfn |= {self.lval.name}
        return dfn

class Asgn(Expr):
    def __str__(self):
        return "Asgn({0} = {1})".format(self.lhs, self.rhs)
    def __init__(self, lhs, rhs, linenum=0):
        assert isinstance(lhs, Var) or isinstance(lhs, ArrIndx)
        self.lhs = lhs
        self.rhs = rhs
        self.linenum = linenum
        self.res = None
    @property
    def is_constant(self):
        return self.rhs.is_constant
    def get_result_const(self, st, ir):
        self.emit(st, ir)
        return self.rhs.get_result_const(st, ir)
    def get_result_noconst(self, st, ir):
        self.emit(st, ir)
        return self.res
    def emit(self, st, ir):
        if not self.res:
            v = self.rhs.get_result(st, ir, True)
            self.res = v
            self.lhs.assign(st, ir, v)
    def wellformed(self, st, defined, _=None):
        if not self.lhs.wellformed(st, defined, True):
            return False
        if not self.rhs.wellformed(st, defined):
            return False
        if self.lhs.ty != self.rhs.ty:
            logging.error("Can't assign from type '%s' to '%s', line %d", self.rhs.ty,
                          self.lhs.ty, self.linenum)
            return False
        self.ty = self.lhs.ty
        return True
    def get_modified(self, either=False):
        ld = self.lhs.get_modified(either)
        rd = self.rhs.get_modified(either)
        dfn = ld|rd
        if isinstance(self.lhs, Var):
            dfn |= {self.lhs.name}
        return dfn

class UOP(Expr):
    def get_result_noconst(self, st, ir):
        copr = self.opr.get_result(st, ir)
        bb = ir.last_bb
        cdst = st.allocator.next_name()
        if self.op == '!':
            bb += [IRI.Cmp('==', cdst, copr, 0, c=str(self))]
        elif self.op == '-':
            bb += [IRI.Arithm('-', cdst, copr, 0, c=str(self))]
        else :
            assert False
        return cdst
    @property
    def is_constant(self):
        return self.opr.is_constant
    def get_result_const(self, st, ir):
        assert self.is_constant
        oo = self.opr.get_result_const(st, ir)
        if self.op == '!' :
            return not oo
        elif self.op == '-' :
            return -oo
        else :
            assert False
    def __str__(self):
        return "UOP({0},{1})".format(self.op, self.opr)
    def __init__(self, op, opr, linenum=0):
        self.op = op
        self.opr = opr
        self.linenum = linenum
    def wellformed(self, st, defined):
        if not self.opr.wellformed(st, defined):
            return False

        expty = None
        if self.op == '!':
            expty = sym.Type('bool')
        else :
            expty = sym.Type('int')

        if not self.opr.ty == expty:
            logging.error("Operator '%s' is not defined for type %s, line %d",
                          self.op, self.opr.ty, self.linenum)
            return False
        self.ty = self.opr.ty
        return True
    def get_modified(self, either=False):
        return self.opr.get_modified(either)

intint_int = ([sym.Type('int'), sym.Type('int')], sym.Type('int'))
boolbool_bool = ([sym.Type('bool'), sym.Type('bool')], sym.Type('bool'))
intint_bool = ([sym.Type('int'), sym.Type('int')], sym.Type('bool'))
class BinOP(Expr):
    type_tab = {
        "+":[intint_int],
        "-":[intint_int],
        "*":[intint_int],
        "//":[intint_int],
        "%":[intint_int],
        "&":[intint_int, boolbool_bool],
        "|":[intint_int, boolbool_bool],
        "&&":[boolbool_bool],
        "||":[boolbool_bool],
        "==":[intint_bool, boolbool_bool],
        "!=":[intint_bool, boolbool_bool],
        "<":[intint_bool],
        ">":[intint_bool],
        "<=":[intint_bool],
        ">=":[intint_bool],
    }
    def get_result_noconst(self, st, ir):
        arithm = {'+', '-', '*', '//', '%', '&', '|'}
        dst = st.allocator.next_name()
        if self.op not in {'&&', '||'}:
            if self.op in {'//', '%', '-'}:
                #for these operators, we don't want the left to be constant
                lres = self.lopr.get_result(st, ir, True)
            else :
                lres = self.lopr.get_result(st, ir)
            rres = self.ropr.get_result(st, ir)
            bb = ir.last_bb
            if self.op in arithm:
                bb += [IRI.Arithm(self.op, dst, lres, rres, c=str(self))]
            else :
                bb += [IRI.Cmp(self.op, dst, lres, rres, c=str(self))]
            return dst
        if self.op in {'&&', '||'}:
            #emit IR for left operand first
            #left, right might include assignment, so we need additional
            #phi nodes
            lres = self.lopr.get_result(st, ir)
            bb = ir.last_bb
            prologue_name = bb.name
            epname = ir.next_name()

            roprbb = ir.append_bb()
            brop = 1
            if self.op == '||':
                brop = 2
            #jump depending on the left operand.
            #for && jump to epilogue if left == 0
            #for || jump to epilogue if left != 0
            bb += [IRI.Br(brop, lres, epname, roprbb.name, c=str(self.lopr))]

            #emit IR for right operand
            #keep track of what's changed in right
            st.cp_push()
            rres = self.ropr.get_result(st, ir)
            bb = ir.last_bb
            bb += [IRI.Br(0, None, epname, None)]
            m = st.cp_revert()
            roprbb = ir.last_bb

            bb = ir.append_bb(epname)
            for v in m:
                newv, oldv = m[v]
                if oldv is None :
                    continue
                nv = st.allocator.next_name(v)
                bb += [IRI.Phi(nv, prologue_name, oldv, roprbb.name, newv)]
                st.assign(v, nv)

            dst = st.allocator.next_name()
            #generate result
            #for &&, if we jump from prologue, result = 0, otherwise = right operand
            #for ||, if we jump from prologue result = left, otherwise = right
            if self.op == '&&':
                lres = 0
            bb += [IRI.Phi(dst, prologue_name, lres, roprbb.name, rres)]
            return dst
        assert False

    @property
    def is_constant(self):
        return self.lopr.is_constant and self.ropr.is_constant
    def get_result_const(self, st, ir):
        assert self.is_constant
        ll = self.lopr.get_result_const(st, ir)
        rr = self.ropr.get_result_const(st, ir)
        if self.op not in {'&&', '||'} :
            return int(eval("%d %s %d" % (ll, self.op, rr)))
        elif self.op == '&&' :
            if not ll:
                return 0
            else :
                return rr
        elif self.op == '||' :
            if ll :
                return ll
            else :
                return rr
        else :
            assert False
    def __str__(self):
        return "BinOP({0},{1},{2})".format(self.lopr, self.op, self.ropr)
    def __init__(self, opr1, op, opr2, linenum=0):
        self.lopr = opr1
        self.ropr = opr2
        self.linenum = linenum
        if op != "/":
            self.op = op
        else :
            self.op = "//"
        self.ty = None
    def wellformed(self, st, defined):
        if not self.lopr.wellformed(st, defined):
            return False
        defined = defined|self.lopr.get_modified()
        if not self.ropr.wellformed(st, defined):
            return False
        self.ty = sym.pattern_match(self.type_tab[self.op], [self.lopr.ty, self.ropr.ty])
        if self.ty is None:
            logging.error("Operator '%s' is not defined for type (%s, %s), line %d", self.op,
                          self.lopr.ty, self.ropr.ty, self.linenum)
            return False
        return True
    def get_modified(self, either=False):
        ldfn = self.lopr.get_modified(either)
        rdfn = self.ropr.get_modified(either)
        if self.op not in {'&&', '||'} or either:
            return ldfn|rdfn
        return ldfn

class Var(Expr):
    def get_global_addr(self, st, fn):
        assert self.is_global
        bb = fn.last_bb
        addr = st.allocator.next_name()
        bb += [IRI.GetAddrOf(addr, IRO.Global(self.name))]
        return addr

    def get_result_noconst(self, st, fn):
        if self.is_global:
            res = st.allocator.next_name()
            addr = self.get_global_addr(st, fn)
            bb = fn.last_bb
            bb += [IRI.Load(res, IRO.Cell(0, addr))]
            return res
        return st.curr_ver(self.name)
    @property
    def is_constant(self):
        return False
    def __init__(self, name, linenum=0):
        self.name = name
        self.linenum = linenum
        self.ty = None
        self.is_global = None
    def __str__(self):
        return "Var({0})".format(self.name)
    def __eq__(self, other):
        if not isinstance(other, Var):
            assert False, other
            return False
        return self.name == other.name
    def __hash__(self):
        return self.name.__hash__()
    def wellformed(self, st, defined, is_dst=False):
        if self.name not in st:
            if self.name not in st.globs:
                logging.error("Undeclared variable '%s' used at line %d" % (self.name, self.linenum))
                return False
            else :
                self.ty = st.globs[self.name].ty
                self.is_global = True
                return True
        else :
            if self.name not in defined and not is_dst:
                logging.error("Variable '{0}' used before initialization, at line {1}".format(self.name, self.linenum))
                return False
            if self.ty is None:
                self.ty = st.get_ty(self.name)
            return True
    def assign(self, st, fn, var):
        if self.is_global:
            addr = self.get_global_addr(st, fn)
            bb = fn.last_bb
            bb += [IRI.Store(IRO.Cell(0, addr), var)]
        else :
            st.assign(self.name, var)
    def get_modified(self, either=False):
        return set()

class ArrIndx(Expr): #array indexing expr
    def __init__(self, lhs, indx, linenum=0):
        self.lhs = lhs
        self.index = indx
        self.linenum = linenum
        self.ty = None
    def __str__(self):
        return "%s[%s]" % (self.lhs, self.index)
    def get_offset(self, st, fn):
        base = self.lhs.get_result(st, fn, True)
        idx = self.index.get_result(st, fn)
        bb = fn.last_bb

        cmpres = st.allocator.next_name()
        if not isinstance(idx, int):
            #check for idx >= 0
            bb += [IRI.Cmp('>=', cmpres, idx, 0)]
        else :
            cmpres = int(idx >= 0)
        nextbb = fn.next_name()
        bb += [IRI.Br(1, cmpres, fn.mangle()+"_Lbound", nextbb)]
        bb = fn.append_bb(nextbb)

        #load -4(base) for the size of array
        sz = st.allocator.next_name()
        bb += [IRI.Load(sz, IRO.Cell(-4, base=base), c="Get the size of "+str(self.lhs))]

        cmpres = st.allocator.next_name()
        bb += [IRI.Cmp('<', cmpres, idx, sz)]

        nextbb = fn.next_name()
        bb += [IRI.Br(1, cmpres, fn.mangle()+"_Lbound", nextbb)]

        bb = fn.append_bb(nextbb)
        if isinstance(idx, int):
            idx *= 4
        else :
            idx2 = st.allocator.next_name()
            bb += [IRI.Arithm('*', idx2, idx, 4)]
            idx = idx2
        offset = st.allocator.next_name()
        bb += [IRI.Arithm('+', offset, idx, base, c="Address of "+str(self))]
        return offset
    def get_result_noconst(self, st, fn):
        offset = self.get_offset(st, fn)
        result = st.allocator.next_name()
        bb = fn.last_bb
        bb += [IRI.Load(result, IRO.Cell(0, base=offset))]
        return result
    @property
    def is_constant(self):
        return False
    def wellformed(self, st, dfn, _=False):
        if not self.lhs.wellformed(st, dfn, False):
            return False
        if not isinstance(self.lhs.ty, sym.ArrayTy):
            logging.error("%s is not an array, line %d", self.lhs, self.linenum)
            return False
        if not self.index.wellformed(st, dfn):
            return False
        if not self.index.ty == sym.Type('int'):
            logging.error("Array subscription is not 'int' (got '%s'), at line %d", self.index.ty, self.index.linenum)
            return False
        self.ty = self.lhs.ty.inner
        return True
    def get_modified(self, either=False):
        ld = self.lhs.get_modified(either)
        ind = self.index.get_modified(either)
        return ld|ind
    def assign(self, st, fn, v):
        offset = self.get_offset(st, fn)
        bb = fn.last_bb
        bb += [IRI.Store(IRO.Cell(0, base=offset), v)]

class Num(Expr):
    @property
    def is_constant(self):
        return True
    def get_result_const(self, *_):
        return self.number
    def __str__(self):
        return "Num({0})".format(self.number)
    def __init__(self, num, linenum=0):
        self.linenum = linenum
        if isinstance(num, str):
            self.number = int(num)
        elif isinstance(num, int):
            self.number = num
        else :
            raise Exception("num is not a number???")
        self.ty = sym.Type('int')
    def wellformed(self, *_):
        return True

class Inpt(Expr):
    @property
    def is_constant(self):
        return False
    def __str__(self):
        return "Input()"
    def __init__(self, linenum=0):
        self.linenum = linenum
        self.ty = sym.Type('int')
        return
    def get_result_noconst(self, st, fn):
        dst = st.allocator.next_name()
        bb = fn.last_bb
        bb += [IRI.Invoke("input_int", [], dst, c=str(self))]
        return dst
    def wellformed(self, *_):
        return True
