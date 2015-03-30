from IR import IR, Phi, BB, Arithm, Br, IInpt, IPrnt, Cmp, Load, Ret, parse_bbname, build_bbname
import copy
def error(st):
        raise Exception("Unexpected {0}({1}) at {2}, {3}".
                        format(st[1], st[0], st[2][0], st[2][1]))
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
        assert name in self.d
        return "%"+name+"."+str(self.d[name])

#methods of AST classes:
# reduce: used to create AST class from symbols
# emit: emit the intermediate code

class Asgn:
    def __str__(self):
        return "Asgn({0} = {1})".format(self.lhs, self.rhs)
    def __init__(self, lhs, rhs, linenum=0):
        assert isinstance(lhs, Var)
        self.lhs = lhs
        self.rhs = rhs
        self.linenum = linenum
    def emit(self, varv, ir):
        self.rhs.emit(varv, ir, self.lhs.name)
    def wellformed(self, defined):
        return self.rhs.wellformed(defined)
    def get_defined(self):
        return {self.lhs.name}

class Expr:
    @property
    def is_constant(self):
        return False
    def get_result(self, varv, ir):
        return None
    def const_emit(self, varv, ir, dst):
        assert self.is_constant
        cdst = varv.next_ver(dst)
        res = self.get_result(varv, ir)

        bb = ir.last_bb
        bb += [Load(cdst, res)]

class UOP(Expr):
    def emit(self, varv, ir, dst):
        if self.is_constant:
            self.const_emit(varv, ir, dst)
            return
        bb = ir.last_bb
        copr = self.opr.get_result(varv, ir)
        cdst = varv.next_ver(dst)
        if self.op == '!':
            bb += [Cmp(0, copr, 0, cdst)]
        elif self.op == '-':
            bb += [Arithm('-', cdst, copr, 0)]
        else :
            assert False
    @property
    def is_constant(self):
        return self.opr.is_constant
    def get_result(self, varv, ir):
        if self.is_constant:
            oo = self.opr.get_result(varv, ir)
            if self.op == '!' :
                return not oo
            elif self.op == '-' :
                return -oo
            else :
                assert False
        self.emit(varv, ir, 'tmp')
        return varv.curr_ver('tmp')
    def __str__(self):
        return "UOP({0},{1})".format(self.op, self.opr)
    def __init__(self, op, opr, linenum=0):
        self.op = op
        self.opr = opr
        self.linenum = linenum
    def wellformed(self, defined):
        return self.opr.wellformed(defined)

class BinOP(Expr):
    def emit(self, varv, ir, dst):
        if self.is_constant:
            self.const_emit(varv, ir, dst)
            return
        bb = ir.last_bb
        arithm = {'+', '-', '*', '//', '%', '&', '|'}
        if self.op not in {'&&', '||'}:
            lres = self.lopr.get_result(varv, ir)
            rres = self.ropr.get_result(varv, ir)
            dst = varv.next_ver(dst)
            if self.op in arithm:
                bb += [Arithm(self.op, dst, lres, rres)]
            else :
                bb += [Cmp(self.op, lres, rres, dst)]
        elif self.op == '&&':
            lres = self.lopr.get_result(varv, ir)
            pbb = ir.append_bb(None)
            pbbname = parse_bbname(pbb.name)
            epname = build_bbname(pbbname, 0, 0, 1)
            bb += [Br(1, lres, epname)]
            rres = self.ropr.get_result(varv, ir)
            bb2 = ir.last_bb
            bb3 = ir.append_bb(epname)
            dst = varv.next_ver(dst)
            bb3 += [Phi(dst, bb.name, 0, bb2.name, rres)]
        elif self.op == '||':
            lres = self.lopr.get_result(varv, ir)
            pbb = ir.append_bb(None)
            pbbname = parse_bbname(pbb.name)
            epname = build_bbname(pbbname, 0, 0, 1)
            bb += [Br(2, lres, epname)]
            rres = self.ropr.get_result(varv, ir)
            bb2 = ir.last_bb
            bb3 = ir.append_bb(epname)
            dst = varv.next_ver(dst)
            bb3 += [Phi(dst, bb.name, lres, bb2.name, rres)]
        else :
            assert False

    @property
    def is_constant(self):
        return self.lopr.is_constant and self.ropr.is_constant
    def get_result(self, varv, ir):
        if self.is_constant:
            ll = self.lopr.get_result(ir, varv, ir)
            rr = self.ropr.get_result(ir, varv, ir)
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
        self.emit(varv, ir, 'tmp')
        return varv.curr_ver('tmp')
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

class Var(Expr):
    def emit(self, varv, ir, dst):
        src = varv.curr_ver(self.name)
        dst = varv.next_ver(dst)
        bb = ir.last_bb
        bb += [Arithm('+', dst, src, 0)]
    @property
    def is_constant(self):
        return False
    def get_result(self, varv, ir):
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
            print("Variable {0} used at line {1}, but not defined".format(self.name, self.linenum))
            return False
        return True

class Num(Expr):
    @property
    def is_constant(self):
        return True
    def emit(self, varv, ir, dst):
        self.const_emit(varv, ir, dst)
    def get_result(self, varv, ir):
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
    def get_defined(self):
        return set()
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
        num = str(ir.bbcnt)
        tdfn = self.then.get_defined()
        pdfn = varv.get_dfn()
        edfn = set()
        if self.e:
            edfn = self.e.get_defined()

        prologue = ir.last_bb
        pbbname = parse_bbname(prologue.name)
        res = self.cond.get_result(varv, ir)
        if self.e :
            prologue += [Br(1, res, build_bbname(pbbname, 1, 0, 0))]
        else :
            prologue += [Br(1, res, build_bbname(pbbname, 0, 0, 1))]
        pmap = {}
        for v in (tdfn|edfn)&pdfn:
            pmap[v] = varv.curr_ver(v)

        thenb = ir.append_bb(build_bbname(pbbname, 0, 1, 0))
        self.then.emit(varv, ir)
        thenb = ir.last_bb
        thenb += [Br(0, None, build_bbname(pbbname, 0, 0, 1))]
        #get last version
        thenmap = {}
        for v in tdfn:
            thenmap[v] = varv.curr_ver(v)

        elsemap = {}
        if self.e :
            elseb = ir.append_bb(build_bbname(pbbname, 1, 0, 0))
            self.e.emit(varv, ir)
            elseb = ir.last_bb
            for v in edfn:
                elsemap[v] = varv.curr_ver(v)

        ep = ir.append_bb(build_bbname(pbbname, 0, 0, 1))
        tgt1b = ""
        tgt2b = ""
        #Add phi nodes here
        #Unused phis will be removed later
        for v in tdfn|edfn:
            if v in tdfn :
                tgt1 = thenmap[v]
                tgt1b = thenb.name
                if v in edfn :
                    tgt2 = elsemap[v]
                    tgt2b = elseb.name
                elif v in pdfn:
                    tgt2 = pmap[v]
                    tgt2b = prologue.name
                else :
                    continue
            elif v in edfn :
                tgt2 = elsemap[v]
                tgt2b = elseb.name
                if v in pdfn :
                    tgt1 = pmap[v]
                    tgt1b = prologue.name
                else :
                    continue
            nv = varv.next_ver(v)
            ep += [Phi(nv, tgt2b, tgt2, tgt1b, tgt1)]

    def wellformed(self, defined):
        res = self.then.wellformed(defined)
        if self.e :
            res = res and self.e.wellformed(defined)
        return res
    def get_defined(self):
        if not self.e :
            #in case the then branch is not run
            return set()
        #variables must be in both branch to be defined
        td = self.then.get_defined()
        te = self.e.get_defined()
        return td&te

class While:
    def __init__(self, cond, do, linenum=0):
        self.cond = cond
        self.do = do
        self.linenum = linenum
    def __str__(self):
        return 'While('+str(self.cond)+')->'+str(self.do)
    def emit(self, varv, ir):
        prologue = ir.last_bb
        pbbname = parse_bbname(prologue.name)
        res = self.cond.get_result(varv, ir)
        prologue += [Br(1, res, build_bbname(pbbname, 0, 0, 1))]
        dfn = self.do.get_defined()
        pdfn = varv.get_dfn()
        old_var = {}
        for v in dfn&pdfn:
            old_var[v] = varv.curr_ver(v)

        body = ir.append_bb(None)
        #emit placeholder phi nodes
        #since we don't know the final
        #variable name at the end of the loop
        phis = []
        for v in dfn&pdfn:
            nv = varv.next_ver(v)
            phis.append(Phi(nv, prologue.name, old_var[v], body.name, "%"+v))
        body += phis
        bname = body.name
        self.do.emit(varv, ir)

        #replace the names in phi nodes
        body = ir.last_bb
        res2 = self.cond.get_result(varv, ir)
        body += [Br(2, res2, bname)]
        for phi in phis:
            v = phi.srcs[bname].val
            phi.del_source(bname)
            phi.set_source(body.name, varv.curr_ver(v))

        epilogue = ir.append_bb(build_bbname(pbbname, 0, 0, 1))
        #add phi nodes
        for v in dfn&pdfn:
            lv = varv.curr_ver(v)
            nv = varv.next_ver(v)
            epilogue += [Phi(nv, prologue.name, old_var[v], body.name, lv)]

    def wellformed(self, defined):
        return self.do.wellformed(defined)
    def get_defined(self):
        #if a loop is not run, nothing is defined
        #so defined is ()
        return set()

class Block:
    def emit(self, varv, ir):
        for w in self.expr_list:
            w.emit(varv, ir)
        if self.is_top:
            bb = ir.append_bb("Lend")
            bb += [Ret()]

    def wellformed(self, _def):
        defined = copy.copy(_def)
        for w in self.expr_list:
            if not w.wellformed(defined):
                return False
            defined |= w.get_defined()
        return True
    def get_defined(self):
        defined = set()
        for w in self.expr_list:
            defined |= w.get_defined()
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

