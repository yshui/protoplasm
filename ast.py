from IR import IR, Phi, BB, Arithm, Br, IInpt, IPrnt, Cmp, Load, Ret
import copy
import logging

class VarVer:
    #this class is used to keep track of variable version
    #since we are using SSA here
    def __init__(self):
        self.d = {}
    def get_dfn(self):
        return set(self.d.keys())
    def next_ver(self, name):
        assert isinstance(name, str)
        if name not in self.d:
            self.d[name] = 0
        else :
            self.d[name] += 1
        return "%"+name+"."+str(self.d[name])
    def curr_ver(self, name):
        assert name in self.d, name
        return "%"+name+"."+str(self.d[name])

class Type:
    pass
class Array(Type):
    def __init__(self, inner):
        self.inner = inner

class Expr:
    @property
    def is_constant(self):
        return False
    def const_result(self, *_):
        assert False
    def noconst_emit(self, varv, ir, dst):
        return None
    def const_emit(self, varv, ir, dst):
        assert self.is_constant
        cdst = varv.next_ver(dst)
        res = self.const_result(varv, ir)

        bb = ir.last_bb
        bb += [Load(cdst, res)]
        return cdst
    def emit(self, varv, ir, dst):
        if self.is_constant:
            self.const_emit(varv, ir, dst)
        else :
            self.noconst_emit(varv, ir, dst)
    def get_result(self, varv, ir, noconst=False):
        assert isinstance(noconst, bool)
        if self.is_constant:
            if noconst:
                return self.const_emit(varv, ir, 'tmp')
            else :
                return self.const_result(varv, ir)
        self.noconst_emit(varv, ir, 'tmp')
        return varv.curr_ver('tmp')
    def get_defined(self, _=False):
        return set()

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
    def emit(self, varv, ir, dst=None):
        opr = varv.curr_ver(self.lval.name)
        bb = ir.last_bb
        opn = ['+', '-']
        if not self.res:
            self.res = opr
            cdst = varv.next_ver(self.lval.name)
            bb += [Arithm(opn[self.op], cdst, opr, 1)]
            if self.pos == 0: #pre
                self.res = cdst
        if dst:
            dst = varv.next_ver(dst)
            bb += [Arithm('+', dst, self.res, 0)]
    def get_result(self, varv, ir, noconst=False):
        self.emit(varv, ir)
        return self.res
    def wellformed(self, dfn):
        self.lval.wellformed(dfn)
    def get_defined(self, either=False):
        return self.lval.get_defined(either)

class Asgn(Expr):
    def __str__(self):
        return "Asgn({0} = {1})".format(self.lhs, self.rhs)
    def __init__(self, lhs, rhs, linenum=0):
        assert isinstance(lhs, Var)
        self.lhs = lhs
        self.rhs = rhs
        self.linenum = linenum
        self.res = None
    @property
    def is_constant(self):
        return self.rhs.is_constant
    def const_result(self, varv, ir):
        self.emit(varv, ir)
        return self.rhs.const_result(varv, ir)
    def emit(self, varv, ir, dst=None):
        if self.res:
            return
        self.rhs.emit(varv, ir, self.lhs.name)
        self.res = varv.curr_ver(self.lhs.name)
        if dst:
            dst = varv.next_ver(dst)
            bb = ir.last_bb
            bb += [Arithm('+', dst, self.lhs.name, 0)]
    def get_result(self, varv, ir, noconst=False):
        if self.is_constant and not noconst:
            return self.const_result(varv, ir)
        else :
            self.emit(varv, ir)
            return self.res
    def wellformed(self, defined):
        return self.rhs.wellformed(defined)
    def get_defined(self, either=False):
        return {self.lhs.name}|self.rhs.get_defined(either)

class UOP(Expr):
    def noconst_emit(self, varv, ir, dst):
        copr = self.opr.get_result(varv, ir)
        bb = ir.last_bb
        cdst = varv.next_ver(dst)
        if self.op == '!':
            bb += [Cmp('==', copr, 0, cdst)]
        elif self.op == '-':
            bb += [Arithm('-', cdst, copr, 0)]
        else :
            assert False
    @property
    def is_constant(self):
        return self.opr.is_constant
    def const_result(self, varv, ir):
        assert self.is_constant
        oo = self.opr.const_result(varv, ir)
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
    def wellformed(self, defined):
        return self.opr.wellformed(defined)
    def get_defined(self, either=False):
        return self.opr.get_defined(either)

class BinOP(Expr):
    def noconst_emit(self, varv, ir, dst):
        arithm = {'+', '-', '*', '//', '%', '&', '|'}
        if self.op not in {'&&', '||'}:
            if self.op in {'//', '%', '-'}:
                #for these operators, we don't want the left to be constant
                lres = self.lopr.get_result(varv, ir, True)
            else :
                lres = self.lopr.get_result(varv, ir)
            rres = self.ropr.get_result(varv, ir)
            bb = ir.last_bb
            dst = varv.next_ver(dst)
            if self.op in arithm:
                bb += [Arithm(self.op, dst, lres, rres)]
            else :
                bb += [Cmp(self.op, lres, rres, dst)]
        elif self.op in {'&&', '||'}:
            #emit IR for left operand first
            lres = self.lopr.get_result(varv, ir)
            bb = ir.last_bb
            prologue_name = bb.name
            epname = ir.next_name()

            roprbb = ir.append_bb(None)
            brop = 1
            if self.op == '||':
                brop = 2
            #jump depending on the left operand.
            #for && jump to epilogue if left == 0
            #for || jump to epilogue if left != 0
            bb += [Br(brop, lres, epname, roprbb.name)]

            #emit IR for right operand
            rres = self.ropr.get_result(varv, ir)
            bb = ir.last_bb
            bb += [Br(0, None, epname, None)]

            bb = ir.append_bb(epname)
            dst = varv.next_ver(dst)

            #generate result
            #for &&, if we jump from prologue, result = 0, otherwise = right operand
            #for ||, if we jump from prologue result = left, otherwise = right
            if self.op == '&&':
                lres = 0
            bb += [Phi(dst, prologue_name, lres, roprbb.name, rres)]
        else :
            assert False

    @property
    def is_constant(self):
        return self.lopr.is_constant and self.ropr.is_constant
    def const_result(self, varv, ir):
        assert self.is_constant
        ll = self.lopr.const_result(varv, ir)
        rr = self.ropr.const_result(varv, ir)
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
    def wellformed(self, defined):
        return self.lopr.wellformed(defined) and self.ropr.wellformed(defined)
    def get_defined(self, either=False):
        ldfn = self.lopr.get_defined(either)
        rdfn = self.ropr.get_defined(either)
        if self.op not in {'&&', '||'} or either:
            return ldfn|rdfn
        return ldfn

class Var(Expr):
    def noconst_emit(self, varv, ir, dst):
        src = varv.curr_ver(self.name)
        dst = varv.next_ver(dst)
        bb = ir.last_bb
        bb += [Arithm('+', dst, src, 0)]
    @property
    def is_constant(self):
        return False
    def get_result(self, varv, ir, _=False):
        return varv.curr_ver(self.name)
    def __init__(self, name, linenum=0):
        self.name = name
        self.linenum = linenum
    def __str__(self):
        return "Var({0})".format(self.name)
    def __eq__(self, other):
        return self.name == other.name
    def __hash__(self):
        return self.name.__hash__()
    def wellformed(self, defined):
        if self.name not in defined:
            logging.error("Variable {0} used at line {1}, but not defined".format(self.name, self.linenum))
            return False
        return True

class Num(Expr):
    @property
    def is_constant(self):
        return True
    def const_result(self, varv, ir):
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
    def wellformed(self, defined):
        return True

class Inpt:
    @property
    def is_constant(self):
        return False
    def __str__(self):
        return "Input()"
    def __init__(self, linenum=0):
        self.linenum = linenum
        return
    def emit(self, varv, ir, dst):
        dst = varv.next_ver(dst)
        bb = ir.last_bb
        bb += [IInpt(dst)]
    def get_result(self, varv, ir):
        self.emit(varv, ir, 'tmp')
        return varv.curr_ver('tmp')
    def wellformed(self, defined):
        return True
    def get_defined(self, _=False):
        return set()

class Prnt:
    def __str__(self):
        return "Print({0})".format(self.expr)
    def __init__(self, expr, linenum=0):
        self.linenum = linenum
        self.expr = expr
    def emit(self, varv, ir):
        res = self.expr.get_result(varv, ir)
        bb = ir.last_bb
        bb += [IPrnt(res)]
    def get_defined(self, either=False):
        return self.expr.get_defined(either)
    def wellformed(self, defined):
        return self.expr.wellformed(defined)

class If:
    def __init__(self, cond, then, e, linenum=0):
        self.cond = cond
        self.then = then
        self.e = e
        self.linenum = linenum
    def __str__(self):
        res = 'If('+str(self.cond)+')->{'+str(self.then)
        if self.e:
            res += ',Else->'+str(self.e)+'}'
        else :
            res += '}'
        return res
    def emit(self, varv, ir):
        res = self.cond.get_result(varv, ir)
        pdfn = varv.get_dfn()
        tmod = self.then.get_defined(True)
        emod = set()
        if self.e:
            emod = self.e.get_defined(True)
        mod = tmod|emod

        tbbname = ir.next_name()
        epname = ir.next_name()
        ebbname = ir.next_name()
        prologue = ir.last_bb
        if self.e :
            prologue += [Br(1, res, ebbname, tbbname)]
        else :
            prologue += [Br(1, res, epname, tbbname)]
        pmap = {}
        for v in mod&pdfn:
            pmap[v] = varv.curr_ver(v)

        thenb = ir.append_bb(tbbname)
        self.then.emit(varv, ir)
        thenb = ir.last_bb
        thenb += [Br(0, None, epname, None)]
        #get last version
        thenmap = {}
        for v in tmod:
            thenmap[v] = varv.curr_ver(v)

        elsemap = {}
        if self.e :
            elseb = ir.append_bb(ebbname)
            self.e.emit(varv, ir)
            elseb = ir.last_bb
            elseb += [Br(0, None, epname, None)]
            for v in emod:
                elsemap[v] = varv.curr_ver(v)

        ep = ir.append_bb(epname)
        if self.e:
            tgt2b = elseb.name
        else :
            tgt2b = prologue.name
        #Add phi nodes here
        #Unused phis will be removed later
        for v in mod:
            if v in tmod :
                tgt1 = thenmap[v]
                if v in emod :
                    tgt2 = elsemap[v]
                elif v in pdfn:
                    tgt2 = pmap[v]
                else :
                    continue
            elif v in emod :
                tgt2 = elsemap[v]
                if v in pdfn :
                    tgt1 = pmap[v]
                else :
                    continue
            nv = varv.next_ver(v)
            ep += [Phi(nv, tgt2b, tgt2, thenb.name, tgt1)]

    def wellformed(self, defined):
        try :
            assert self.cond.wellformed(defined)
            defined = defined|self.cond.get_defined()
            assert self.then.wellformed(defined)
            if self.e :
                assert self.e.wellformed(defined)
        except AssertionError :
            return False
        return True
    def get_defined(self, either=False):
        cond_dfn = self.cond.get_defined(either)
        if not self.e :
            #in case the then branch is not run
            if either :
                return cond_dfn|self.then.get_defined(either)
            return cond_dfn
        #variables must be in both branch to be defined
        td = self.then.get_defined(either)
        te = self.e.get_defined(either)
        if either :
            return cond_dfn|td|te
        return (td&te)|cond_dfn

class Loop:
    def __init__(self, cond, do, pre=None, post=None, linenum=0):
        #cond is (condition position, condition)
        self.pre = pre
        self.post = post
        self.cond, self.cond_pos = cond
        self.do = do
        self.linenum = linenum
    def __str__(self):
        cp = ['Pre', 'Post']
        return 'For(%s;%s<%s>;%s){%s}' % (self.pre, self.cond, cp[self.cond_pos], self.post, self.do)
    def emit(self, varv, ir):
        #emit pre
        if self.pre:
            self.pre.emit(varv, ir)
        pdfn = varv.get_dfn()
        mod = self.do.get_defined(True)|self.cond.get_defined(True)
        if self.post:
            mod |= self.post.get_defined(True)
        before = ir.last_bb
        prname = ir.next_name()
        epname = ir.next_name()
        bname = ir.next_name()
        prologue = None
        body = None
        lbname = None #loopback name

        if self.cond_pos == 0:
            before += [Br(0, None, prname, None)]
        else :
            before += [Br(0, None, bname, None)]

        old_var = {}
        lb_var = {}
        var_phi = {}
        for v in mod&pdfn:
            old_var[v] = varv.curr_ver(v)
            var_phi[v] = varv.next_ver(v)

        def emit_prologue(is_end):
            nonlocal prname, ir, lb_var, lbname, varv, prologue
            prologue = ir.append_bb(prname)
            res = self.cond.get_result(varv, ir)
            prologue_end = ir.last_bb
            prologue_end += [Br(1, res, epname, bname)]
            if is_end:
                lbname = prologue_end.name
                for v in mod&pdfn:
                    lb_var[v] = varv.curr_ver(v)

        def emit_body(is_end):
            nonlocal bname, ir, lb_var, lbname, varv, body
            body = ir.append_bb(bname)
            bname = body.name
            self.do.emit(varv, ir)
            if self.post:
                self.post.emit(varv, ir)
            body_end = ir.last_bb
            body_end += [Br(0, None, prname, None)]
            if is_end:
                lbname = body_end.name
                for v in mod&pdfn:
                    lb_var[v] = varv.curr_ver(v)

        if self.cond_pos == 0: #pre
            emit_prologue(False)
            emit_body(True)
        else :
            emit_body(False)
            emit_prologue(True)

        phis = []
        for v in mod&pdfn:
            i = Phi(var_phi[v], before.name, old_var[v], lbname, lb_var[v])
            phis.append(i)

        if self.cond_pos == 0:
            prologue.phis = phis
        else :
            body.phis = phis

        epilogue = ir.append_bb(epname)
        for v in var_phi:
            dst = varv.next_ver(v)
            epilogue += [Arithm('+', dst, var_phi[v], 0)]

    def wellformed(self, defined):
        try :
            if self.pre:
                assert self.pre.wellformed(defined)
                defined = defined|self.pre.get_defined()
            if self.cond_pos == 0:
                assert self.cond.wellformed(defined)
                defined = defined|self.cond.get_defined()
            assert self.do.wellformed(defined)
            defined = defined|self.do.get_defined()
            if self.post:
                assert self.post.wellformed(defined)
                defined = defined|self.post.get_defined()
            if self.cond_pos == 1:
                assert self.cond.wellformed(defined)
        except AssertionError :
            return False
        return True
    def get_defined(self, either=False):
        #if a loop is not run, nothing is defined
        #so defined is only what defined in the condition
        res = self.cond.get_defined(either)
        if self.cond_pos == 1 or either: #post
            #loop well run at least once
            res = res|self.do.get_defined(either)
            if self.post:
                res = res|self.post.get_defined(either)
        if self.pre :
            res = res|self.pre.get_defined(either)
        return res

class Block:
    def emit(self, varv, ir):
        for w in self.expr_list:
            w.emit(varv, ir)
        if self.is_top:
            bb = ir.last_bb
            if bb.br:
                bb = ir.append_bb("Lend")
            bb += [Ret()]

    def wellformed(self, _def):
        defined = copy.copy(_def)
        for w in self.expr_list:
            if not w.wellformed(defined):
                return False
            defined |= w.get_defined()
        return True
    def get_defined(self, either=False):
        defined = set()
        for w in self.expr_list:
            defined |= w.get_defined(either)
        return defined
    def __init__(self, elist, linenum=0):
        self.expr_list = elist
        self.is_top = False
        self.linenum = linenum
    def gencode(self):
        assert self.wellformed(set())
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
        for w in self.expr_list:
            res += str(w)
            res += ", "
        res += "]"
        return res

