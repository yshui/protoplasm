from IR import IR, Phi, BB, Arithm, Br, IInpt, IPrnt, Cmp, Load, Ret, Malloc, Store, Cell, ROStr
import copy
import logging

class Allocator:
    def __init__(self):
        self.ver = {}
        self.ver[0] = -1
    def next_name(self, prefix=None):
        if prefix is None :
            self.ver[0] += 1
            return "%%%d" % self.ver[0]
        prefix = str(prefix)
        if prefix not in self.ver:
            self.ver[prefix] = 0
        else :
            self.ver[prefix] += 1
        return "%%%s.%d" % (prefix, self.ver[prefix])

class SymTable:
    #this class is used to keep track of variable version
    #since we are using SSA here
    def __init__(self, dlist=None, prototype=None):
        self.t = {}
        self.d = {}
        self.prototype = prototype
        self.modified = {}
        self.mstack = []
        if prototype:
            self.allocator = prototype.allocator
        else :
            self.allocator = Allocator()
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
        else :
            self.modified = {}
        return m

    def get_dclr(self):
        res = set(self.d.keys())
        if self.prototype:
            res |= self.prototype.get_dclr()
        return res

    def get_dfn(self): #get all possibly initialized variable
        res = set([x for x in self.d if self.d[x] is not None])
        if self.prototype:
            res |= self.prototype.get_dfn()
        return res

    def new_var(self, name, t=None):
        self.d[name] = None
        self.t[name] = t

    def is_initialized(self, name):
        if name in self.d:
            return self.d[name] is not None
        assert self.prototype
        return self.prototype.is_initialized(name)

    def assign(self, name, var):
        assert isinstance(name, str)
        if name not in self.modified:
            if self.is_initialized(name):
                self.modified[name] = self.curr_ver(name)
            else :
                self.modified[name] = None
        if name not in self.d:
            return self.prototype.assign(name, var)
        self.d[name] = str(var)

    def unassign(self, name):
        if name in self.modified:
            assert self.modified[name] is None
            del self.modified[name]
        if name not in self.d:
            return self.prototype.unassign(name)
        self.d[name] = None

    def curr_ver(self, name):
        assert isinstance(name, str)
        if name not in self.d:
            assert self.prototype, name
            return self.prototype.curr_ver(name)
        return str(self.d[name])

    def __str__(self):
        return "All: %s, modified: %s" % (self.d, self.modified)

class Type:
    def __init__(self, name):
        self.name = name
    def __str__(self):
        return self.name
class Array(Type):
    def __init__(self, inner):
        self.inner = inner

class Decl:
    def __init__(self, t, vlist):
        self.vlist = vlist
        self.t = t

class Dim:
    def __init__(self, size, star):
        self.size = size
        assert isinstance(star, int)
        self.star = star
    def __str__(self):
        return "[%s], []*%s" % (self.size, self.star)

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
                bb += [Load(n, res, c=str(self))]
                return n
            return res
        return self.get_result_noconst(st, ir)
    def get_modified(self, _=False):
        return set()

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
        bb += [Arithm('+', szp1, res, 1), Arithm('*', szp1m4, szp1, 4)]
        bb += [Malloc(ndst, szp1m4, c=str(self))]
        #store the size of the array
        bb += [Store(Cell(0, base=ndst), res)]
        ndst2 = st.allocator.next_name()
        bb += [Arithm('+', ndst2, ndst, 4)]
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
            bb += [Arithm(opn[self.op], cdst, opr, 1, c=str(self))]
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
            bb += [Cmp('==', cdst, copr, 0, c=str(self))]
        elif self.op == '-':
            bb += [Arithm('-', cdst, copr, 0, c=str(self))]
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
                bb += [Arithm(self.op, dst, lres, rres, c=str(self))]
            else :
                bb += [Cmp(self.op, dst, lres, rres, c=str(self))]
            return dst
        if self.op in {'&&', '||'}:
            #emit IR for left operand first
            #left, right might include assignment, so we need additional
            #phi nodes
            lres = self.lopr.get_result(st, ir)
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
            bb += [Br(brop, lres, epname, roprbb.name, c=str(self.lopr))]

            #emit IR for right operand
            #keep track of what's changed in right
            st.cp_push()
            rres = self.ropr.get_result(st, ir)
            bb = ir.last_bb
            bb += [Br(0, None, epname, None)]
            m = st.cp_pop()

            bb = ir.append_bb(epname)
            for v in m:
                nv = st.allocator.next_name(v)
                bb += [Phi(nv, prologue_name, m[v], roprbb.name, st.curr_ver(v))]
                st.assign(v, nv)

            dst = st.allocator.next_name()
            #generate result
            #for &&, if we jump from prologue, result = 0, otherwise = right operand
            #for ||, if we jump from prologue result = left, otherwise = right
            if self.op == '&&':
                lres = 0
            bb += [Phi(dst, prologue_name, lres, roprbb.name, rres)]
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
        return self.lopr.wellformed(st, defined) and self.ropr.wellformed(st, defined)
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
    def get_offset(self, st, ir):
        base = self.lhs.get_result(st, ir, True)
        idx = self.index.get_result(st, ir)
        bb = ir.last_bb

        #load -4(base) for the size of array
        sz = st.allocator.next_name()
        bb += [Load(sz, Cell(-4, base=base), c="Get the size of "+str(self.lhs))]

        cmpres = st.allocator.next_name()
        bb += [Cmp('<', cmpres, idx, sz)]

        nextbb = ir.next_name()
        bb += [Br(1, cmpres, "Lbound",nextbb )]

        bb = ir.append_bb(nextbb)
        if isinstance(idx, int):
            idx *= 4
        else :
            idx2 = st.allocator.next_name()
            bb += [Arithm('*', idx2, idx, 4)]
            idx = idx2
        offset = st.allocator.next_name()
        bb += [Arithm('+', offset, idx, base, c="Address of "+str(self))]
        return offset
    def get_result_noconst(self, st, ir):
        offset = self.get_offset(st, ir)
        result = st.allocator.next_name()
        bb = ir.last_bb
        bb += [Load(result, Cell(0, base=offset))]
        return result
    @property
    def is_constant(self):
        return False
    def wellformed(self, st, dfn, _=False):
        return self.lhs.wellformed(st, dfn, False) and self.index.wellformed(st, dfn)
    def get_modified(self, either=False, is_dst=False):
        return self.lhs.get_modified(either, False)|self.index.get_modified(either)
    def assign(self, st, ir, v):
        offset = self.get_offset(st, ir)
        bb = ir.last_bb
        bb += [Store(Cell(0, base=offset), v)]

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
    def wellformed(self, _, __):
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
    def get_result_noconst(self, st, ir):
        dst = st.allocator.next_name()
        bb = ir.last_bb
        bb += [IInpt(dst, c=str(self))]
        return dst
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
    def emit(self, st, ir):
        res = self.expr.get_result(st, ir)
        bb = ir.last_bb
        bb += [IPrnt(res, c=str(self)), IPrnt(ROStr("\\n"), c="New line")]
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
            prologue += [Br(1, res, ebbname, tbbname, c=str(self.cond))]
        else :
            prologue += [Br(1, res, epname, tbbname, c=str(self.cond))]

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
        for v in mod: #modified in either branch
            if v in tsym.modified and v not in tsym.d:
                if v in mod_else:
                    tgt1 = mod_else[v] #the variable name before else modify it
                    tgt2 = esym.curr_ver(v)
                elif mod[v] is not None :
                    tgt1 = st.curr_ver(v) #variable not modified in else, just get its name
                    tgt2 = mod[v]
                else :
                    #mod[v] is None, this variable is only assigned in then and not before
                    #No phi for this v, also we have to remove it from symbol table
                    logging.debug("Unassign (if) %s" % v)
                    st.unassign(v)
                    continue
            else :
                assert v in mod_else
                if mod[v] is not None :
                    tgt1 = mod[v]
                    tgt2 = esym.curr_ver(v)
                else :
                    #same as before
                    logging.debug("Unassign (if) %s" % v)
                    st.unassign(v)
                    continue
            nv = st.allocator.next_name(v)
            ep += [Phi(nv, tgt2b, tgt2, thenb.name, tgt1)]
            st.assign(v, nv)

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

        mod = self.do.get_modified(True)
        mod |= self.cond.get_modified(True)
        if self.post:
            mod |= self.post.get_modified(True)

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
        for v in mod&pdfn:
            var_phi[v] = st.allocator.next_name(v)
            st.assign(v, var_phi[v])

        def emit_prologue():
            nonlocal prname, ir, prologue, st
            prologue = ir.append_bb(prname)
            res = self.cond.get_result(st, ir)
            prologue_end = ir.last_bb
            prologue_end += [Br(1, res, epname, bname, c=str(self.cond))]

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
        to_unassign = {}
        if self.cond_pos == 0: #pre
            emit_prologue()
            for v in var_phi:
                prvar[v] = st.curr_ver(v)
            outbname = ir.last_bb.name
            st.cp_push()
            emit_body()
            to_unassign = st.cp_pop()
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
        for v in pmod:
            if v not in var_phi:
                continue
            i = Phi(var_phi[v], before.name, pmod[v], lbname, st.curr_ver(v))
            phis.append(i)

        if self.cond_pos == 0:
            prologue.phis = phis
        else :
            body.phis = phis

        for v in var_phi:
            #use the last version from prologue block
            st.assign(v, prvar[v])
        for v in to_unassign:
            if to_unassign[v] is None:
                logging.info("Unassign %s" % v)
                st.unassign(v)
        epilogue = ir.append_bb(epname)

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
            logging.error(e)
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
            bb = ir.append_bb("Lbound")
            bb += [IPrnt(ROStr("Out-of-bound error, abort\\n")), Ret()]

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

