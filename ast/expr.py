import IR.instruction as IRI
import IR.operand as IRO
import logging
class Expr:
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
    def wellformed(self, st, defined):
        for arg in self.args:
            if not arg.wellformed(st, defined):
                return False
        if self.name not in st.globs:
            logging.error("Function %s not declared\n", self.name)
            return False
        return True

class New(Expr):
    def __init__(self, t, dim):
        self.t = t
        self.dim = dim
    def __str__(self):
        return "New(%s, %s)" % (self.t, self.dim)
    @property
    def is_constant(self):
        return False
    def get_result_noconst(self, st, ir):
        res = self.dim.size.get_result(st, ir, True)
        ndst = st.allocator.next_name()
        bb = ir.last_bb
        #calc (size+1) and (size+1)*4
        szp1 = st.allocator.next_name()
        szp1m4 = st.allocator.next_name()
        bb += [IRI.Arithm('+', szp1, res, 1), IRI.Arithm('*', szp1m4, szp1, 4)]
        bb += [IRI.Malloc(ndst, szp1m4, c=str(self))]
        #store the size of the array
        bb += [IRI.Store(IRO.Cell(0, base=ndst), res)]
        ndst2 = st.allocator.next_name()
        bb += [IRI.Arithm('+', ndst2, ndst, 4)]
        return ndst2
    def wellformed(self, st, defined):
        return self.dim.size.wellformed(st, defined)
    def get_modified(self, either):
        return self.dim.size.get_modified(either)

class Inc(Expr):
    def __init__(self, lval, pos, op):
        self.pos = pos
        self.op = op
        self.lval = lval
        self.res = None
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
    def wellformed(self, st, dfn):
        return self.lval.wellformed(st, dfn)
    def get_modified(self, _=False):
        return self.lval.get_modified(is_dst=True)

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
    def wellformed(self, st, defined):
        return self.lhs.wellformed(st, defined, True) and self.rhs.wellformed(st, defined)
    def get_modified(self, either=False):
        return self.lhs.get_modified(either, True)|self.rhs.get_modified(either)

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
        return self.opr.wellformed(st, defined)
    def get_modified(self, either=False):
        return self.opr.get_modified(either)

class BinOP(Expr):
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
    def wellformed(self, st, defined):
        ret = self.lopr.wellformed(st, defined)
        if not ret:
            return False
        defined = defined|self.lopr.get_modified()
        return self.ropr.wellformed(st, defined)
    def get_modified(self, either=False):
        ldfn = self.lopr.get_modified(either)
        rdfn = self.ropr.get_modified(either)
        if self.op not in {'&&', '||'} or either:
            return ldfn|rdfn
        return ldfn

class Var(Expr):
    def get_result_noconst(self, st, ir):
        return st.curr_ver(self.name)
    @property
    def is_constant(self):
        return False
    def __init__(self, name, linenum=0):
        self.name = name
        self.linenum = linenum
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
            logging.error("Undeclared variable '%s' used at line %d" % (self.name, self.linenum))
            return False
        if self.name not in defined and not is_dst:
            logging.error("Variable '{0}' used before initialization, at line {1}".format(self.name, self.linenum))
            return False
        return True
    def assign(self, st, _, var):
        st.assign(self.name, var)
    def get_modified(self, either=False, is_dst=False):
        if is_dst:
            return {self.name}
        return set()

class ArrIndx(Expr): #array indexing expr
    def __init__(self, lhs, indx, linenum=0):
        self.lhs = lhs
        assert isinstance(lhs, ArrIndx) or isinstance(lhs, Var) #XXX remove later
        self.index = indx
        self.linenum = linenum
    def __str__(self):
        return "%s[%s]" % (self.lhs, self.index)
    def get_offset(self, st, fn):
        base = self.lhs.get_result(st, fn, True)
        idx = self.index.get_result(st, fn)
        bb = fn.last_bb

        #load -4(base) for the size of array
        sz = st.allocator.next_name()
        bb += [IRI.Load(sz, IRO.Cell(-4, base=base), c="Get the size of "+str(self.lhs))]

        cmpres = st.allocator.next_name()
        bb += [IRI.Cmp('<', cmpres, idx, sz)]

        nextbb = fn.next_name()
        bb += [IRI.Br(1, cmpres, "Lbound",nextbb )]

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
        return self.lhs.wellformed(st, dfn, False) and self.index.wellformed(st, dfn)
    def get_modified(self, either=False, is_dst=False):
        return self.lhs.get_modified(either, False)|self.index.get_modified(either)
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
        return
    def get_result_noconst(self, st, fn):
        dst = st.allocator.next_name()
        bb = fn.last_bb
        bb += [IRI.Invoke("input_int", [], dst, c=str(self))]
        return dst
    def wellformed(self, *_):
        return True
    def get_modified(self, _=False):
        return set()
