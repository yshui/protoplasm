import copy
from instruction import usable_reg
class Cell:
    def __init__(self, val):
        self.val = val
        self.is_reg = False
        self.is_imm = False
    def __eq__(self, other):
        assert isinstance(other, Cell)
        return self.val == other.val
    def validate(self, dfn):
        return True
    def get_dfn(self):
        assert False
    def __str__(self):
        return "("+self.val+")"
    def get_used(self):
        return set()
    def get_offset(self):
        return str(self.val*4)
    def allocate(self):
        assert False, "Cannot allocate register for a cell"

class Register:
    def __eq__(self, other):
        return other.val == self.val
    def __hash__(self):
        return str(self).__hash__()
    def __init__(self, val):
        self.val = val
        self.is_reg = True
        self.is_imm = False
    def validate(self, dfn):
        return True
    def get_dfn(self):
        assert False
    def __str__(self):
        return "$"+self.val
    def get_used(self):
        return set()
    def allocate(self):
        assert False, "Cannot allocate register for a register"

class Imm:
    def __init__(self, number):
        assert isinstance(number, int)
        self.val = number
        self.is_var = False
        self.is_imm = True
    def validate(self, dfn):
        return True
    def get_dfn(self):
        assert False
    def __str__(self):
        return str(self.val)
    def get_used(self):
        return set()
    def allocate(self, _):
        return self


class Var:
    def __init__(self, var, dst=0):
        self.val = var
        self.dst = dst
        self.used = False
        self.is_var = True
        self.is_imm = False
    def validate(self, dfn):
        if not self.dst:
            assert self.val in dfn, "%s not defined" % self.val
        else :
            assert self.val not in dfn
    def get_dfn(self):
        assert self.dst
        return {self.val}
    def __str__(self):
        return "%"+self.val
    def __hash__(self):
        return str(self).__hash__()
    def __eq__(self, other):
        if not isinstance(other, Var):
            return False
        return self.val == other.val
    def get_used(self):
        if self.dst:
            return set()
        return {self.val}
    def allocate(self, regmap):
        assert self.val in regmap
        return regmap[self.val]
    def mark_as_used(self):
        assert self.dst
        self.used = True

class Nil:
    def __init__(self, var=0, dst=0):
        pass
    def validate(self, dfn):
        return True
    def get_dfn(self):
        return set()
    @property
    def val(self):
        assert False
    def __str__(self):
        return ""
    def get_used(self):
        return set()
    def allocate(self, _):
        return self

def get_operand(val, dst=0):
    if dst :
        assert isinstance(val, str)
        assert val[0] == '%'
    if val is None :
        return Nil()
    if isinstance(val, int):
        return Imm(val)
    assert isinstance(val, str)
    if val[0] == '%':
        return Var(val[1:], dst)
    return Register(val)

class NIns:
    'Normal instructions, not end of basic block or phi'
    is_br = False
    is_phi = False
    def __init__(self):
        self.dst = None
    def mark_as_used(self):
        self.dst.mark_as_used()
    @property
    def used(self):
        return self.dst.used
    def get_dfn(self):
        return self.dst.get_dfn()

class Arithm(NIns):
    opc = {"+": 1, "-": 2, "*": 3, "//": 4, "%": 5, "&": 6, "|": 7}
    opname = {
            1 : 'add',
            2 : 'sub',
            3 : 'mul',
            4 : 'div',
            5 : 'rem',
            6 : 'and',
            7 : 'or',
    }
    def gencode(self):
        if self.opr1.is_imm and self.opr2.is_imm:
            assert False
        return "\t%s %s, %s, %s\n" % (self.opname[self.op], str(self.dst), str(self.opr1), str(self.opr2))

    def __init__(self, op, dst, opr1, opr2):
        assert op in self.opc
        self.op = self.opc[op]
        self.dst = get_operand(dst, 1)
        self.opr1 = get_operand(opr1)
        if self.opr1.is_imm:
            assert self.opr1.val == 0
            self.opr1 = Register("r0")
        self.opr2 = get_operand(opr2)
    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
        self.opr1 = self.opr1.allocate(regmap)
        self.opr2 = self.opr2.allocate(regmap)
    def validate(self, dfn):
        self.opr1.validate(dfn)
        self.opr2.validate(dfn)
        self.dst.validate(dfn)
    def __str__(self):
        return "%s %s, %s, %s" % (self.opname[self.op], str(self.dst), str(self.opr1), str(self.opr2))
    def get_used(self):
        return self.opr1.get_used()|self.opr2.get_used()

class IInpt(NIns):
    def __init__(self, dst):
        self.dst = get_operand(dst, 1)
    def validate(self, dfn):
        self.dst.validate(dfn)
    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
    def get_used(self):
        return set()
    def gencode(self):
      out = "\tli $v0, 5\n\tsyscall\n"
      out += "\tadd %s, $v0, 0\n" % str(self.dst)
      return out
    def __str__(self):
        return "INPUT "+str(self.dst)

class IPrnt(NIns):
    def __init__(self, var):
        self.var = get_operand(var)
    def validate(self, dfn):
        self.var.validate(dfn)
    def allocate(self, regmap):
        self.var = self.var.allocate(regmap)
    def get_dfn(self):
        return set()
    def __str__(self):
        return "PRINT "+str(self.var)
    def get_used(self):
        return self.var.get_used()
    def gencode(self):
        out = ""
        if self.var.is_reg:
            out += "\tadd $a0, %s, 0\n" % str(self.var)
        else :
            out += "\tli $a0, %s\n" % str(self.var)
        out += "\tli $v0, 1\n\tsyscall\n"
        out += "\tli $v0, 4\n\tla $a0, nl\n\tsyscall\n"
        return out

class Cmp:
    '0 : seq'
    opname = {
            0 : "SEQ"
    }
    opc = {"==" : 0}
    def __init__(self, op, src1, src2, dst):
        assert op in self.opc
        self.op = self.opc[op]
        self.src1 = get_operand(src1)
        self.src2 = get_operand(src2)
        self.dst = get_operand(dst, 1)
    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
        self.src1 = self.src1.allocate(regmap)
        self.src2 = self.src2.allocate(regmap)
    def get_dfn(self):
        return self.dst.get_dfn()
    def get_used(self):
        return self.src1.get_used()|self.src2.get_used()
    def validate(self, dfn):
        self.src1.validate(dfn)
        self.src2.validate(dfn)
        self.dst.validate(dfn)
    def __str__(self):
        return self.opname[self.op]+" "+str(self.dst)+", "+str(self.src1)+", "+str(self.src2)

class Br:
    '0 : j, 1 : beqz, 2 : bnez'
    brname = {
            0 : "j",
            1 : "beqz",
            2 : "bnez",
    }
    def __init__(self, op, src, target):
        self.src = get_operand(src)
        self.tgt = target
        self.op = op
        self.is_br = True
        self.is_phi = False
        self.is_cond = (op != 0)
    def validate(self, dfn):
        self.src.validate(dfn)
    def allocate(self, regmap):
        self.src = self.src.allocate(regmap)
    def get_dfn(self):
        return set()
    def get_used(self):
        if self.src:
            return self.src.get_used()
        return set()
    def gencode(self, curr):
        real_tgt = self.tgt+"_"+curr
        if self.op == 0:
            return "\tb "+real_tgt+"\n"
        assert self.src.is_reg
        return "\t"+self.brname[self.op]+" "+str(self.src)+", "+real_tgt+"\n"
    def __str__(self):
        if not isinstance(self.src, Nil) :
            return self.brname[self.op]+" "+str(self.src)+", "+self.tgt
        else :
            return self.brname[self.op]+" "+self.tgt

class Phi:
    def __init__(self, dst, *arg):
        if len(arg)%2 :
            raise Exception("Wrong number of arg for Phi")
        it = iter(arg)
        self.srcs = {}
        for x in it:
            self.srcs[x] = get_operand(next(it))
        self.is_phi = True
        self.is_br = False
        self.dst = get_operand(dst, 1)
    def set_source(self, bb, src):
        self.srcs[bb] = get_operand(src)
    def del_source(self, bb):
        del self.srcs[bb]
    def get_dfn(self):
        return self.dst.get_dfn()
    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
    def validate(self, bb, bbmap):
        for src, var in self.srcs.items():
            #does src point to us?
            assert src in bb.predecessors
            print("{0} does point to us".format(src))
            #are we referring to ourselves?
            assert not var == self.dst
            #is var defined in src?
            _dfn = bbmap[src].internal_dfn|bbmap[src].avail_dfn
            var.validate(_dfn)
            print("{0} is defined in {1}".format(var, src))
        for pred in bb.predecessors:
            assert pred in self.srcs
    def __str__(self):
        res = "PHI "+str(self.dst)+", ["
        for x, y in self.srcs.items():
            res += x+" : "+str(y)+", "
        res += "]"
        return res

class Memory:
    def __init__(self):
        self.avail = set()
        self.top = 0
        self.mmap = {}
    def get(self, var):
        if var in self.mmap:
            return (True, self.mmap[var])
        if self.avail:
            self.mmap[var] = Cell(self.avail.pop())
        else :
            self.mmap[var] = Cell(self.top)
            self.top += 1
        return (False, self.mmap[var])
    def drop(self, var):
        assert var in self.mmap
        m = self.mmap[var]
        del self.mmap[var]
        if m.val == self.top:
            self.top -= 1
        else :
            self.avail |= {m.val}

def load_or_move(src, dst):
    assert dst.is_reg
    if src.is_imm:
        return "\tli "+str(dst)+", "+str(src)+"\n"
    elif src.is_reg:
        return "\tadd %s, %s, 0\n" % (str(dst), str(src))
    else :
        return "\tlw "+str(dst)+src.get_offset()+"($sp)\n"

def move_or_store(src, dst):
    assert src.is_reg
    if dst.is_reg:
        return "\tadd %s, %s, 0\n" % (str(dst), str(src))
    else :
        return "\tsw "+str(src)+dst.get_offset()+"($sp)\n"

class Load:
    def __init__(self, dst, m):
        assert isinstance(m, Cell) or isinstance(m, int)
        if isinstance(dst, str):
            dst = get_operand(dst, 1)
        assert isinstance(dst, Register) or isinstance(dst, Var)
        self.dst = dst
        if isinstance(m, int):
            self.m = Imm(m)
        else :
            self.m = m
        self.is_phi = False
        self.is_br = False
    def __str__(self):
        return "load %s, %s" % (str(self.dst), str(self.m))
    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
    def get_dfn(self):
        return self.dst.get_dfn()
    def get_used(self):
        return set()
    def gencode(self):
        return load_or_move(self.m, self.dst)
    def validate(self, dfn):
        self.dst.validate(dfn)

class Store:
    def __init__(self, dst, r):
        assert isinstance(r, Register)
        assert isinstance(dst, Cell)
        self.dst = dst
        self.r = r
    def gencode(self):
        return move_or_store(self.r, self.dst)

def promote(regmap, rreg, reg, mem, var, rlock):
    """
    promote var to register, don't spill variables in
    rlock
    """
    if var in regmap and regmap[var].is_reg:
        return ([], [])
    if reg:
        pre = []
        nreg = reg.pop()
        if var in regmap:
            pre = [Load(regmap[var], nreg)]
        regmap[var] = nreg
        rreg[regmap[var]] = var
        return (pre, [])

    for v in regmap:
        if v not in rlock and regmap[v].is_reg:
            break

    inmem, mc = mem.get(v)
    if not inmem:
        pre = [Store(regmap[v], mc)]
    if var in regmap:
        pre.append(Load(regmap[var], regmap[v]))
    regmap[var] = regmap[v]
    rreg[regmap[v]] = var
    regmap[v] = mem.get()
    return (pre, [])

class BB:
    '''
    Last and only the last instruction can be Br
    Phi instructions must be at the beginning of a bb
    '''
    def __str__(self):
        res = self.name+":\n"
        res += "#availbb: "+str(self.availbb)+"\n"
        res += "#pred: "+str(self.predecessors)+"\n"
        res += "#fall through: "+str(self.fall_through)+"\n"
        res += "#In: "+str(self.In)+"\n"
        if self.required:
            res += "#Required: "+str(self.required)+"\n"
        for n, i in enumerate(self.ins):
            if i is self.end:
                break
            res += "\t"+str(i)
            if n in self.prune:
                res += "  #Pruned\n"
            else :
                res += "\n"
        if self.epilogue:
            res += "#Epilogue: \n"
        for i in self.epilogue:
            res += "\t"+str(i)+"\n"
        if self.end:
            res += "\t"+str(self.end)+"  #end\n"
        res += "#Out: "+str(self.out)+"\n"
        if self.out_reg:
            res += "#Out_reg: \n"
            for k, v in self.out_reg.items():
                res += k+": "+str(v)+", "
            res += "\n"
        return res
    def __hash__(self):
        return self.name.__hash__()
    def __eq__(self, other):
        return self is other
    @property
    def allocatable(self):
        assert(self.avail_done)
        assert(self.inout_done)
        return not self.required
    def gencode(self, bbmap):
        out = ""
        #First, generate code for phi nodes
        for pred in self.predecessors:
            srcb = bbmap[pred]
            out += self.name+"_"+pred+":\n"
            print(self.name+"_"+pred+":")
            has_reg = {}
            dsts = {}
            tmpreg = None
            need_pop = False
            imm2mem = []
            nphi = 0
            for n, i in enumerate(self.ins):
                if not i.is_phi:
                    break
                if n in self.prune:
                    continue
                if not i.srcs[pred].is_var:
                    if i.dst.is_reg:
                        out += load_or_move(i.srcs[pred], i.dst)
                    else :
                        imm2mem.append(i)
                        nphi += 1
                    continue
                nphi += 1
                if i.srcs[pred] not in has_reg:
                    dsts[i.srcs[pred]] = []
                    has_reg[i.srcs[pred]] = False
                dsts[i.srcs[pred]].append(i)
                if i.dst.is_reg:
                    tmpreg = str(i.dst)
                    has_reg[i.srcs[pred]] = True
            if nphi == 0:
                continue
            if not tmpreg:
                #then we must borrow a reg from someone
                #we don't care who we borrow it from
                #we are going to put it back anyway
                out += "\tsw $t0, -4($sp)\n"
                #now we can use t0
                tmpreg = "$t0"
                need_pop = True
            #handle all imm to memory
            while imm2mem:
                i = imm2mem.pop()
                out += "\tli %s, %s\n" % (tmpreg, str(i.srcs[pred]))
                out += "\tsw "+tmpreg+", "+i.dst.get_offset()+"($sp)\n"
            #handle all the in memory phi nodes
            for i in has_reg:
                if has_reg[i]:
                    continue
                if i.is_var:
                    src = srcb.out_reg[i.val]
                else :
                    src = i
                load_or_move(src, tmpreg)
                while dsts[i]:
                    ii = dsts[i].pop()
                    out += "\tsw "+tmpreg+ii.dst.get_offset()+"($sp)\n"
            #recover tmpreg
            if need_pop:
                out += "\tlw $t0, -4($sp)\n"
            for i in has_reg:
                if not has_reg[i]:
                    continue
                for ii in dsts[i]:
                    if ii.dst.is_reg:
                        break
                if i.is_var:
                    load_or_move(srcb.out_reg[i.val], ii.dst)
                else :
                    load_or_move(i, ii.dst)
                tmpreg = ii.dst
                while dsts[i]:
                    ii = dsts[i].pop()
                    if ii.dst == tmpreg:
                        continue
                    move_or_store(tmpreg, ii.dst)
            out += '\tb '+self.name+"\n"
        out += self.name+":\n"
        endn = 0
        for n, i in enumerate(self.ins):
            if i is self.end:
                endn = n
                break
            if i.is_phi:
                continue
            if n in self.prune:
                continue
            for pi in self.pre[n]:
                out += pi.gencode()
            out += i.gencode()
            for pi in self.post[n]:
                out += pi.gencode()

        if self.epilogue:
            for i in self.epilogue:
                out += i.gencode()
        if self.end:
            for pi in self.pre[endn]:
                out += pi.gencode()
            out += self.end.gencode(self.name)
            for pi in self.post[endn]:
                out += pi.gencode()
        return out

    def allocate(self, in_reg, mem):
        last_use = {}
        term_ins = {}
        avail_reg = set(all_reg)
        regmap = {}
        rregmap = {}
        for v in self.In:
            assert v in in_reg, "BB(%s): in variable %s not defined in in_reg, pred %s" % (self.name, v, str(self.predecessors))
            if in_reg[v].is_reg:
                avail_reg -= {in_reg[v]}
            regmap[v] = in_reg[v]
            rregmap[regmap[v]] = v
        for v in self.out:
            last_use[v] = -1
        for n, i in reversed(list(enumerate(self.ins))):
            if i.is_phi:
                break
            uu = i.get_used()
            term_ins[n] = set()
            for k in uu:
                if k not in last_use:
                    last_use[k] = n
                    term_ins[n] |= {k}
        for n, i in enumerate(self.ins):
            d = i.get_dfn()
            assert len(d) <= 1, "More than one defined variable???"
            if d:
                d = d.pop()
            #new variable?
            if d and d not in last_use:
                #unused variable
                self.prune[n] = True
                continue
            assert n not in self.pre
            assert n not in self.post
            self.pre[n] = []
            self.post[n] = []

            if i.is_phi:
                #we will deal with phi nodes later
                if avail_reg:
                    r = avail_reg.pop()
                    regmap[d] = r
                    rregmap[r] = d
                else :
                    regmap[d] = mem.get(d)
                i.allocate(regmap)
                continue

            u = i.get_used()
            #promote arguments into registers
            for v in u:
                pre, post = promote(regmap, rregmap, avail_reg, mem, v, u)
                self.pre[n] += pre
                self.post[n] += post
            #add regs that are used the last time back to avail_reg
            for v in term_ins[n]:
                if regmap[v].is_reg:
                    avail_reg |= {regmap[v]}
                    del rregmap[regmap[v]]
                else :
                    mem.drop(v)
            if d:
                pre, post = promote(regmap, rregmap, avail_reg, mem, d, u)
                self.pre[n] += pre
                self.post[n] += post
            i.allocate(regmap)
            for v in term_ins[n]:
                del regmap[v]
        for v in self.out:
            if v in self.In:
                if regmap[v] != in_reg[v]:
                    if in_reg[v].is_reg:
                        #since the register changed, its value must still be in memory
                        #so move whoever is using in_reg[v] into regmap[v]
                        #and then load the memory into in_reg[v]
                        if in_reg[v] in rregmap:
                            inmem, mc = mem.get(v)
                            inv = rregmap[in_reg[v]]
                            assert inmem
                            self.epilogue.append(Arithm('+', regmap[v], in_reg[v], 0))
                            self.epilogue.append(Load(in_reg[v], mc))
                            regmap[inv] = regmap[v]
                            rregmap[regmap[inv]] = inv
                            regmap[v] = in_reg[v]
                            rregmap[regmap[v]] = v
                        else :
                            #in_reg[v] is not used, simply move
                            self.epilogue.append(Arithm('+', in_reg[v], regmap[v], 0))
                            del rregmap[regmap[v]]
                            regmap[v] = in_reg[v]
                            rregmap[regmap[v]] = v
                    else :
                        assert mem.get(v) == in_reg[v]
                        regmap[v] = in_reg[v]
            self.out_reg[v] = regmap[v]
        self.allocated = True

    def __init__(self, name, ins=[]):
        #dfn is variable defined in all paths lead to this bb
        self.ins = copy.copy(ins)
        self.name = name
        self.allocated = False #is register allocation done
        self.avail_done = False
        self.inout_done = False
        self.end = None
        self.nxt = None
        self.phi = True
        self.in_dfn = set() #in_dfn = definitions in this bb
        self.a_dfn = set() #available definitions
        self.in_used = set()
        self.predecessors = set()
        self.successors = set()
        self.validated = False
        self.availbb = set()
        self.availbb_next = set()
        self.fall_through = True
        self.out = set()
        self.In = set()
        self.pre = {}
        self.post = {}
        self.out_reg = {}
        self.epilogue = []
        self.required = set()
        self.dombb = set()
        self.prune = {}

    def avail_next(self, bbmap, queue):
        availbb_next = set()
        for pbb in self.predecessors:
            if not availbb_next:
                availbb_next = bbmap[pbb].availbb|{pbb}
            else :
                availbb_next &= (bbmap[pbb].availbb|{pbb})
        if availbb_next != self.availbb:
            for nbb in self.successors:
                queue |= {nbb}
            self.availbb = availbb_next

    def avail_finish(self, bbmap):
        self.avail_done = True
        for prevbb in self.availbb:
            pbb = bbmap[prevbb]
            self.a_dfn |= pbb.internal_dfn
            pbb.dombb |= {self.name}

    @property
    def internal_used(self):
        if self.in_used:
            return self.in_used
        for i in self.ins:
            if not i.is_phi:
                self.in_used |= i.get_used()
        return self.in_used

    def inout_next(self, bbmap, queue):
        in_next = (self.out|self.internal_used)-self.internal_dfn
        if in_next == self.In:
            return
        self.In = in_next
        visited = set()
        for i in self.ins:
            if not i.is_phi:
                break
            for srcbb, src in i.srcs.items():
                srcu = src.get_used()
                sbb = bbmap[srcbb]
                new_out = sbb.out
                visited |= {sbb.name}
                if new_out|self.In|srcu != sbb.out:
                    sbb.out |= (self.In|srcu)
                    queue |= {srcbb}

        for prevbb in self.predecessors-visited:
            pbb = bbmap[prevbb]
            if pbb.out|self.In != pbb.out:
                pbb.out |= self.In
                queue |= {prevbb}

    def inout_finish(self, bbmap):
        self.inout_done = True
        for abb in self.availbb:
            aabb = bbmap[abb]
            if aabb.out&self.In:
                self.required |= {abb}

    def __iadd__(self, _ins):
        if self.end :
            raise Exception("Appending instruction after end of BB")
        if self.availbb :
            raise Exception("Appending instruction after calc availbb")
        ins = copy.copy(_ins)
        while ins:
            i = ins.pop(0)
            if i.is_phi and not self.phi:
                raise Exception("Phi instructions in the middle of a BB")
            if not i.is_phi:
                self.phi = False
            if i.is_br:
                if ins:
                    raise Exception("Branch not at end of BB.")
                self.end = i
                self.nxt = i.tgt
                self.fall_through = i.is_cond
            self.ins.append(i)
        return self
    @property
    def avail_dfn(self):
        if not self.avail_done:
            raise Exception("Call calc_avail before get avail_dfn")
        return self.a_dfn
    @property
    def internal_dfn(self):
        if self.in_dfn:
            return self.in_dfn
        for i in self.ins:
            self.in_dfn |= i.get_dfn()
        return self.in_dfn
    def validate(self, bbmap):
        #with the help of available dfn
        #we can make sure all of the variables used in this bb
        #is always defined on all the paths leading to this bb
        self.validated = True
        _dfn = copy.copy(self.a_dfn)
        #skip phi instructions, only get their defines
        #because phi instruction can grab a variable defined later in this bb
        for i in self.ins:
            if i.is_phi:
                _dfn |= i.get_dfn()
            else :
                break
        #validate other instructions
        for i in self.ins:
            if not i.is_phi:
                i.validate(_dfn)
                _dfn |= i.get_dfn()
        #now validate phi instructions
        for i in self.ins:
            if i.is_phi:
                i.validate(self, bbmap)

class IR:
    def __str__(self):
        res = "\n\n==========================IR============================\n"
        for bb in self.bb:
            res += str(bb)
        return res
    def allocate(self):
        queue = set([bb for bb in self.bb if bb.allocatable])
        mem = Memory()
        while queue:
            h = queue.pop()
            print(h.required)
            in_reg = {}
            for availbb in h.availbb:
                abb = self.bbmap[availbb]
                for k, v in abb.out_reg.items():
                    if k not in in_reg:
                        in_reg[k] = v
                    else :
                        assert in_reg[k] == abb.out_reg[k]
            h.allocate(in_reg, mem)
            #print(self)
            for dombb in h.dombb:
                dbb = self.bbmap[dombb]
                dbb.required -= {h.name}
                if dbb.allocatable:
                    queue |= {dbb}

    def __init__(self, bb=[]):
        self.bb = copy.copy(bb)
        self.bbmap = {}
        self.bbcnt = 0

    def __iadd__(self, o):
        self.bb += o
        for i in o:
            if i.name in self.bbmap:
                raise Exception("Basic blocks with duplicated name")
            self.bbmap[i.name] = i
        self.bbcnt += len(o)
        return self

    def append_bb(self, name=None):
        if not name:
            name = 'L'+str(self.bbcnt)
        r = BB(name)
        self += [r]
        return r

    def calc_connections(self):
        prev = None
        for i in self.bb:
            if prev and prev.fall_through:
                i.predecessors |= {prev.name}
                prev.successors |= {i.name}
            if i.nxt :
                assert i.nxt in self.bbmap, "Jumping to a non-existent block %s" % i.nxt
                i.successors |= {i.nxt}
                self.bbmap[i.nxt].predecessors |= {i.name}
            prev = i

    def calc_avail(self):
        #calculate blocks that are 'available' to this bb
        #the definition of 'available' is the same as in the slides
        #the 'available' variable would than be all variable defined in available blocks
        init = set(self.bbmap.keys())
        for bb in self.bb:
            bb.availbb = init
        queue = {self.bb[0].name}
        while queue :
            print(queue)
            h = queue.pop()
            print(self)
            self.bbmap[h].avail_next(self.bbmap, queue)
        for bb in self.bb:
            bb.avail_finish(self.bbmap)

    def calc_inout(self):
        queue = set()
        for bb in self.bb:
            bb.In = set()
            bb.out = set()
            queue |= {bb.name}
        while queue:
            h = queue.pop()
            self.bbmap[h].inout_next(self.bbmap, queue)
        for bb in self.bb:
            bb.inout_finish(self.bbmap)

    def gencode(self, fname):
        f = open(fname, 'w')
        f.write(".data\nnl: .asciiz \"\\n\"\n")
        f.write(".text\nmain:\n")
        for bb in self.bb:
            f.write(bb.gencode(self.bbmap))
        f.close()

    @property
    def last_bb(self):
        return self.bb[-1]
    def validate(self):
        for i in self.bb:
            i.validate(self.bbmap)

all_reg = [Register(x) for x in usable_reg]
