from IR import IR, Phi, BB, Arithm, Br, IInpt, IPrnt, Cmp, Load, Ret
import copy
import logging

class SymTable:
    #this class is used to keep track of variable version
    #since we are using SSA here
    def __init__(self, dlist=None, prototype=None):
        self.d = {}
        self.nchild = {}
        self.t = {}
        self.prototype = prototype
        self.modified = {}
        self.mstack = []
        self.root = {}
        self.d[0] = -1
        if prototype:
            self.root[0] = self.prototype.root[0]
        else :
            self.root[0] = self
            self.nchild[0] = 0
        if dlist:
            for d in dlist:
                for v in d.vlist:
                    self.new_var(v.name, d.t)

    def __contains__(self, other):
        if other in self.d:
            return True
        if not self.prototype:
            return False
        return other in self.prototype

    def cp_push(self):
        #restart nonlocal variable accounting
        self.mstack.append(self.modified)
        self.modified = {}

    def cp_pop(self):
        m = self.modified
        if self.mstack:
            self.modified = self.mstack.pop()
            for v in m:
                if v not in self.modified:
                    self.modified[v] = m[v]
        return m

    def get_dclr(self):
        res = set(self.d.keys())
        if self.prototype:
            res |= self.prototype.get_dclr()
        return res

    def get_dfn(self): #get all possibly initialized variable
        res = set([x for x in self.d if self.d[x] >= 0])
        if self.prototype:
            res |= self.prototype.get_dfn()
        return res

    def get_root(self, name):
        if not self.prototype or name not in self.prototype:
            if name in self.d:
                return self
            return None
        return self.prototype.get_root(name)

    def new_var(self, name, t=None):
        self.d[name] = -1
        self.root[name] = self.get_root(name)
        self.nchild[name] = 0
        self.t[name] = t

    def new_child(self, name):
        assert self.root[name] == self
        self.nchild[name] += 1
        return self.nchild[name]-1

    def build_name(self, name):
        ver = self.d[name]
        assert ver >= 0, "Uninitialized variable %s" % name
        res = "%s.%d" % (name, ver)
        if name == 0:
            res = res[2:]
        return "%"+res

    def is_initialized(self, name):
        if name in self.d:
            return self.d[name] >= 0
        assert self.prototype
        return self.prototype.is_initialized(name)

    def next_ver(self, name):
        assert isinstance(name, str) or name == 0
        if name not in self.modified and self.is_initialized(name) and name != 0:
            self.modified[name] = self.curr_ver(name)
        if name not in self.d:
            return self.prototype.next_ver(name)
        self.d[name] = self.root[name].new_child(name)
        return self.build_name(name)

    def curr_ver(self, name):
        assert isinstance(name, str) or name == 0
        if name not in self.d:
            return self.prototype.curr_ver(name)
        return self.build_name(name)

    def __str__(self):
        return "All: %s, modified: %s" % (self.d, self.modified)

class Type:
    def __init__(self, name):
        self.name = name
class Array(Type):
    def __init__(self, inner):
        self.inner = inner

class Decl:
    def __init__(self, t, vlist):
        self.vlist = vlist
        self.t = t

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
                return self.const_emit(varv, ir, 0)
            else :
                return self.const_result(varv, ir)
        self.noconst_emit(varv, ir, 0)
        return varv.curr_ver(0)
    def get_modified(self, _=False):
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
    def wellformed(self, st, dfn):
        return self.lval.wellformed(st, dfn)
    def get_modified(self, either=False):
        return {self.lval.name}

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
        if not self.res:
            self.rhs.emit(varv, ir, self.lhs.name)
            self.res = varv.curr_ver(self.lhs.name)
        if dst:
            dst = varv.next_ver(dst)
            bb = ir.last_bb
            if self.is_constant:
                bb += [Load(dst, self.rhs.const_result(varv, ir))]
            else :
                bb += [Arithm('+', dst, self.res, 0)]
    def get_result(self, varv, ir, noconst=False):
        if self.is_constant and not noconst:
            return self.const_result(varv, ir)
        self.emit(varv, ir)
        return self.res
    def wellformed(self, st, defined):
        if self.lhs.name not in st:
            logging.error("Undeclared variable '%s' used at line %d" % (self.lhs.name, self.linenum))
            logging.error(self)
            return False
        return self.rhs.wellformed(st, defined)
    def get_modified(self, either=False):
        return {self.lhs.name}|self.rhs.get_modified(either)

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
    def wellformed(self, st, defined):
        return self.opr.wellformed(st, defined)
    def get_modified(self, either=False):
        return self.opr.get_modified(either)

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
    def wellformed(self, st, defined):
        return self.lopr.wellformed(st, defined) and self.ropr.wellformed(st, defined)
    def get_modified(self, either=False):
        ldfn = self.lopr.get_modified(either)
        rdfn = self.ropr.get_modified(either)
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
    def wellformed(self, st, defined):
        if self.name not in st:
            logging.error("Undeclared variable '%s' used at line %d" % (self.name, self.linenum))
            return False
        if self.name not in defined:
            logging.error("Variable '{0}' used before initialization, at line {1}".format(self.name, self.linenum))
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
    def wellformed(self, _, __):
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
        self.emit(varv, ir, 0)
        return varv.curr_ver(0)
    def wellformed(self, _, __):
        return True
    def get_modified(self, _=False):
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
    def get_modified(self, either=False):
        return self.expr.get_modified(either)
    def wellformed(self, st, defined):
        return self.expr.wellformed(st, defined)

class If:
    def __init__(self, cond, then, e, linenum=0):
        self.cond = cond
        self.then = then
        if not isinstance(then, Block):
            self.then = Block([then], None, then.linenum)
        self.else_ = e
        if not isinstance(e, Block) and e:
            self.else_ = Block([e], None, e.linenum)
        self.linenum = linenum
    def __str__(self):
        res = 'If('+str(self.cond)+')->{'+str(self.then)
        if self.else_:
            res += ',Else->'+str(self.else_)+'}'
        else :
            res += '}'
        return res
    def emit(self, st, ir):
        res = self.cond.get_result(st, ir)

        st.cp_push()
        tbbname = ir.next_name()
        epname = ir.next_name()
        ebbname = ir.next_name()
        prologue = ir.last_bb
        if self.else_ :
            prologue += [Br(1, res, ebbname, tbbname)]
        else :
            prologue += [Br(1, res, epname, tbbname)]

        thenb = ir.append_bb(tbbname)
        self.then.emit(st, ir)
        thenb = ir.last_bb
        thenb += [Br(0, None, epname, None)]
        tgt2b = prologue.name

        st.cp_push()
        if self.else_ :
            elseb = ir.append_bb(ebbname)
            self.else_.emit(st, ir)
            elseb = ir.last_bb
            elseb += [Br(0, None, epname, None)]
            tgt2b = elseb.name

        mod_else = st.cp_pop()
        mod = st.cp_pop()
        tsym = self.then.symtable
        if self.else_:
            esym = self.else_.symtable
        else :
            esym = SymTable()
        ep = ir.append_bb(epname)
        #Add phi nodes here
        #Unused phis will be removed later
        for v in mod: #modified in both branch
            if v in tsym.modified and v not in tsym.d:
                if v in mod_else:
                    tgt1 = mod_else[v] #the variable name before else modify it
                    tgt2 = esym.curr_ver(v)
                else :
                    tgt1 = st.curr_ver(v) #variable not modified in else, just get its name
                    tgt2 = mod[v]
            else :
                assert v in mod_else
                tgt1 = mod[v]
                tgt2 = esym.curr_ver(v)
            nv = st.next_ver(v)
            ep += [Phi(nv, tgt2b, tgt2, thenb.name, tgt1)]

    def wellformed(self, st, defined):
        try :
            assert self.cond.wellformed(st, defined)
            defined = defined|self.cond.get_modified()
            assert self.then.wellformed(st, defined)
            if self.else_ :
                assert self.else_.wellformed(st, defined)
        except AssertionError as e:
            print(e)
            return False
        return True
    def get_modified(self, either=False):
        cond_dfn = self.cond.get_modified(either)
        if not self.else_ :
            #in case the then branch is not run
            if either :
                return cond_dfn|self.then.get_modified(either)
            return cond_dfn
        #variables must be in both branch to be defined
        td = self.then.get_modified(either)
        te = self.else_.get_modified(either)
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
        if not isinstance(self.do, Block):
            self.do = Block([do], None, linenum=linenum)
        self.linenum = linenum
    def __str__(self):
        cp = ['Pre', 'Post']
        return 'For(%s;%s<%s>;%s){%s}' % (self.pre, self.cond, cp[self.cond_pos], self.post, self.do)
    def emit(self, st, ir):
        #emit pre
        if self.pre:
            self.pre.emit(st, ir)
        print(st)

        mod = self.do.get_modified(True)
        print("XX %s" % mod)
        mod |= self.cond.get_modified(True)
        print("XX2 %s" % mod)
        if self.post:
            mod |= self.post.get_modified(True)
        print("XX3 %s" % mod)

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

        st.cp_push() #create a checkpoint
        var_phi = {}
        pdfn = st.get_dfn()
        print("SAD %s %s" % (pdfn, self))
        for v in mod&pdfn:
            var_phi[v] = st.next_ver(v)

        def emit_prologue():
            nonlocal prname, ir, prologue, st
            prologue = ir.append_bb(prname)
            res = self.cond.get_result(st, ir)
            prologue_end = ir.last_bb
            prologue_end += [Br(1, res, epname, bname)]

        def emit_body():
            nonlocal bname, ir, body, st
            body = ir.append_bb(bname)
            bname = body.name
            self.do.emit(st, ir)
            if self.post:
                self.post.emit(st, ir)
            body_end = ir.last_bb
            body_end += [Br(0, None, prname, None)]

        prvar = {}
        if self.cond_pos == 0: #pre
            emit_prologue()
            for v in var_phi:
                prvar[v] = st.curr_ver(v)
            outbname = ir.last_bb.name
            emit_body()
        else :
            emit_body()
            emit_prologue()
            for v in var_phi:
                prvar[v] = st.curr_ver(v)
            outbname = ir.last_bb.name
        lbname = ir.last_bb.name

        phis = []
        pmod = st.cp_pop()
        assert set(pmod) == mod, "%s %s" % (pmod, mod)
        print("VAR %s %s" % (var_phi, self))
        print("PMOD %s %s" % (pmod, self))
        for v in pmod:
            if v not in var_phi:
                continue
            i = Phi(var_phi[v], before.name, pmod[v], lbname, st.curr_ver(v))
            phis.append(i)

        if self.cond_pos == 0:
            prologue.phis = phis
        else :
            body.phis = phis

        epilogue = ir.append_bb(epname)
        for v in var_phi:
            dst = st.next_ver(v)

            #use the last version from prologue block
            epilogue += [Arithm('+', dst, prvar[v], 0)]

    def wellformed(self, st, defined):
        try :
            if self.pre:
                assert self.pre.wellformed(st, defined)
                defined = defined|self.pre.get_modified()
            if self.cond_pos == 0:
                assert self.cond.wellformed(st, defined)
                defined = defined|self.cond.get_modified()
            assert self.do.wellformed(st, defined)
            defined = defined|self.do.get_modified()
            if self.post:
                assert self.post.wellformed(st, defined)
                defined = defined|self.post.get_modified()
            if self.cond_pos == 1:
                assert self.cond.wellformed(st, defined)
        except AssertionError as e:
            print(e)
            return False
        return True
    def get_modified(self, either=False):
        #if a loop is not run, nothing is defined
        #so defined is only what defined in the condition
        res = self.cond.get_modified(either)
        if self.cond_pos == 1 or either: #post
            #loop well run at least once
            res = res|self.do.get_modified(either)
            if self.post:
                res = res|self.post.get_modified(either)
        if self.pre :
            res = res|self.pre.get_modified(either)
        print("%s %s %s" % (res, self, either))
        return res

class Block:
    def emit(self, st, ir):
        assert st == self.symtable.prototype, "%s %s" % (st, self.symtable.prototype)
        for w in self.slist:
            w.emit(self.symtable, ir)
        if self.is_top:
            bb = ir.last_bb
            if bb.br:
                bb = ir.append_bb("Lend")
            bb += [Ret()]

    def wellformed(self, st, defined):
        if not self.symtable:
            self.symtable = SymTable(self.dlist, st)
        else :
            assert self.symtable.prototype == st
        dfn = copy.copy(defined)
        #clear everything that is re-declared in this block
        dfn -= set(self.symtable.d)
        for w in self.slist:
            if not w.wellformed(self.symtable, dfn):
                return False
            dfn |= w.get_modified()
        return True
    def get_modified(self, either=False):
        mod = set()
        for w in self.slist:
            mod |= w.get_modified(either)
        return mod-set(self.symtable.d)
    def __init__(self, slist, dlist, linenum=0):
        self.slist = slist
        self.dlist = dlist
        self.symtable = None
        self.parent = None
        self.is_top = False
        self.linenum = linenum
    def gencode(self):
        res = IR()
        for e, _ in self.slist:
            res += e.emit(self.symtable)
        return res
    def __iadd__(self, obj):
        self.slist += [obj]
        return self
    def __str__(self):
        res = "["
        for w in self.slist:
            res += str(w)
            res += ", "
        res += "]"
        return res

