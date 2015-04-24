import copy
import logging
import builtin
import IR.mod as mod
import IR.instruction as IRI
import IR.operand as opr
from .symbol import SymTable, DupErr, FnTy

class Dim:
    def __init__(self, size, star):
        self.size = size
        assert isinstance(star, int)
        self.star = star
    def __str__(self):
        return "[%s], []*%s" % (self.size, self.star)

class Prnt:
    def __str__(self):
        return "Print({0})".format(self.expr)
    def __init__(self, expr, linenum=0):
        self.linenum = linenum
        self.expr = expr
    def emit(self, st, fn):
        res = self.expr.get_result(st, fn)
        bb = fn.last_bb
        strg = fn.glob_for_str("\\n")
        strv = st.allocator.next_name()
        bb += [IRI.Invoke("print_int", [res], None, c=str(self))]
        bb += [IRI.GetAddrOf(strv, strg)]
        bb += [IRI.Invoke("print_str", [strv], None, c="New line")]
    def get_modified(self, either=False):
        return self.expr.get_modified(either)
    def wellformed(self, st, defined):
        return self.expr.wellformed(st, defined)

class Return:
    def __str__(self):
        return "Return(%s)" % self.expr
    def __init__(self, expr, linenum=0):
        self.linenum = linenum
        self.expr = expr
    def emit(self, st, fn):
        if self.expr is not None:
            res = self.expr.get_result(st, fn)
        else :
            res = None
        bb = fn.last_bb
        bb += [IRI.Ret(res)]
    def get_modified(self, either=False):
        if self.expr is None:
            return set()
        return self.expr.get_modified(either)
    def wellformed(self, st, defined):
        if self.expr is None:
            return True
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
    def emit(self, st, fn):
        res = self.cond.get_result(st, fn)

        st.cp_push()
        tbbname = fn.next_name()
        epname = fn.next_name()
        ebbname = fn.next_name()
        prologue = fn.last_bb
        if self.else_ :
            prologue += [IRI.Br(1, res, ebbname, tbbname, c=str(self.cond))]
        else :
            prologue += [IRI.Br(1, res, epname, tbbname, c=str(self.cond))]

        thenb = fn.append_bb(tbbname)
        self.then.emit(st, fn)
        thenb = fn.last_bb
        thenb += [IRI.Br(0, None, epname, None)]
        tgt2b = prologue.name
        mod_then = st.cp_revert()

        st.cp_push()
        if self.else_ :
            elseb = fn.append_bb(ebbname)
            self.else_.emit(st, fn)
            elseb = fn.last_bb
            elseb += [IRI.Br(0, None, epname, None)]
            tgt2b = elseb.name

        mod_else = st.cp_revert()
        ep = fn.append_bb(epname)

        #Add phi nodes here
        #Unused phis will be removed later
        tmp = set(mod_then)|set(mod_else)
        for v in tmp: #modified in either branch
            if v in mod_then:
                if v in mod_else:
                    tgt1 = mod_then[v][0]
                    tgt2 = mod_else[v][0]
                else :
                    tgt1, tgt2 = mod_then[v]
                    if tgt2 is None :
                        #no need to unassign
                        #v is already unassigned in cp_revert
                        continue
            else :
                assert v in mod_else
                tgt2, tgt1 = mod_else[v]
                if tgt1 is None :
                    continue
            nv = st.allocator.next_name(v)
            ep += [IRI.Phi(nv, tgt2b, tgt2, thenb.name, tgt1)]
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
    def emit(self, st, fn):
        #emit pre
        if self.pre:
            self.pre.emit(st, fn)

        mod = self.do.get_modified(True)
        mod |= self.cond.get_modified(True)
        if self.post:
            mod |= self.post.get_modified(True)

        before = fn.last_bb
        prname = fn.next_name()
        epname = fn.next_name()
        bname = fn.next_name()
        prologue = None
        body = None
        lbname = None #loopback name

        if self.cond_pos == 0:
            before += [IRI.Br(0, None, prname, None)]
        else :
            before += [IRI.Br(0, None, bname, None)]

        st.cp_push() #create a checkpoint
        var_phi = {}
        pdfn = st.get_dfn()
        for v in mod&pdfn:
            var_phi[v] = st.allocator.next_name(v)
            st.assign(v, var_phi[v])

        def emit_prologue():
            nonlocal prname, fn, prologue, st
            prologue = fn.append_bb(prname)
            res = self.cond.get_result(st, fn)
            prologue_end = fn.last_bb
            prologue_end += [IRI.Br(1, res, epname, bname, c=str(self.cond))]

        def emit_body():
            nonlocal bname, fn, body, st
            body = fn.append_bb(bname)
            bname = body.name
            self.do.emit(st, fn)
            if self.post:
                self.post.emit(st, fn)
            body_end = fn.last_bb
            body_end += [IRI.Br(0, None, prname, None)]

        mod_body = {}
        if self.cond_pos == 0: #pre
            emit_prologue()
            st.cp_push()
            emit_body()
            mod_body = st.cp_revert()
        else :
            emit_body()
            emit_prologue()
        lbname = fn.last_bb.name

        mod_prologue = st.cp_pop()
        tmp = set(mod_prologue)|set(mod_body)
        assert tmp == mod, "body: %s prologue: %s %s" % (mod_body, mod_prologue, mod)

        if self.cond_pos == 0:
            phis = prologue.phis
        else :
            phis = body.phis
        for v in tmp:
            if v not in var_phi:
                continue
            newv, oldv = mod_prologue[v]
            if v in mod_body:
                newv = mod_body[v][0]
            if oldv is not None :
                i = IRI.Phi(var_phi[v], before.name, oldv, lbname, newv)
                phis.append(i)

        fn.append_bb(epname)

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

class Fn:
    def __init__(self, name, params, rety, body, linenum=0):
        self.name = name
        self.params = params
        self.linenum = linenum
        self.rety = rety
        self.body = body
        self.symtable = None
        self.ty = FnTy()
    def __hash__(self):
        return str.__hash__("Fn(%s)" % self.name)
    def __eq__(self, o):
        if not isinstance(o, Fn):
            return False
        return self.name == o.name
    def __str__(self):
        res = "%s %s (" % (self.rety, self.name)
        for p in self.params:
            res += "%s, " %p
        res = res[:-2]+") {"
        res += str(self.body)+"}"
        return res
    def wellformed(self, globs):
        try :
            self.symtable = SymTable(None, self.params, None)
        except DupErr as e:
            logging.error("Duplicate variable %s in parameter list, at line %d", e.name, self.linenum)
            return False
        self.symtable.globs = {}
        for v in globs:
            if v not in self.symtable.d:
                self.symtable.globs[v] = globs[v]

        defined = set()
        for p in self.params:
            defined |= {p.name}
        return self.body.wellformed(self.symtable, defined)
    def emit(self, ir):
        iparams = []
        for p in self.params:
            v = self.symtable.allocator.next_name(p.name)
            self.symtable.assign(p.name, v)
            iparams.append(v)
        func = mod.Func(self.name, iparams, self.rety.itype)
        func.append_bb()
        func.ir = ir
        self.body.emit(self.symtable, func)
        ir += [func]

class Program:
    def __init__(self, decl_list):
        self.decl = decl_list

    def wellformed(self):
        globs = {}
        for d in self.decl:
            if isinstance(d, Fn):
                if d.name in globs:
                    logging.error("Function %s at line %d has duplicated name", d.name, d.linenum)
                    return False
                if not d.wellformed(globs):
                    return False
                globs[d.name] = d
            else :
                for v in d:
                    if v in globs:
                        logging.error("Global variable %s defined again at line %d", v, d.linenum)
                        return False
                    globs[v.name] = v
        return True

    def emit(self):
        ir = mod.IR()
        for fn in self.decl:
            if isinstance(fn, Fn):
                fn.emit(ir)
        ir += builtin.builtins
        return ir

class Block:
    def emit(self, st, fn):
        assert st == self.symtable.prototype, "%s %s" % (st, self.symtable.prototype)
        for w in self.slist:
            w.emit(self.symtable, fn)
        if self.is_top:
            bb = fn.append_bb("Lbound")
            strg = fn.glob_for_str("Out-of-bound error, abort\\n")
            strv = st.allocator.next_name()
            bb += [IRI.GetAddrOf(strv, strg)]
            bb += [IRI.Invoke("print_str", [strv], None), IRI.Invoke("exit", [], None)]
            bb += [IRI.Br(0, None, "Lbound", None)]

    def wellformed(self, st, defined):
        if not self.symtable:
            try :
                self.symtable = SymTable(dlist=self.dlist, prototype=st)
            except DupErr as e:
                logging.error("Variable %s defined again\n" % e.name)
                return False
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
        assert isinstance(dlist, list)
        assert not dlist or not isinstance(dlist[0], list), dlist
        self.dlist = dlist
        self.symtable = None
        self.parent = None
        self.is_top = False
        self.linenum = linenum
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
