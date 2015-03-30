import copy
import re
from utils import _str_set, _dict_print

usable_reg = []
for __i in range(0, 2):
    usable_reg += ["t{0}".format(__i)]

def parse_bbname(name):
    ret = [0, 0, 0, 0]
    ep = name.find('EP')
    if ep >= 0:
        ret[3] = int(name[ep+2:])
        name = name[:ep]
    ep = name.find('T')
    if ep >= 0:
        ret[2] = int(name[ep+1:])
        name = name[:ep]
    ep = name.find('O')
    if ep >= 0:
        ret[1] = int(name[ep+1:])
        name = name[:ep]
    ret[0] = int(name[1:])
    return ret

def build_bbname(no, o, t, ep):
    name = "L"+str(no[0])
    if no[1]+o:
        name += "O"+str(no[1]+o)
    if no[2]+t:
        name += "T"+str(no[2]+t)
    if no[3]+ep:
        name += "EP"+str(no[3]+ep)
    return name

def gen_rvmap(*arg):
    #res = ""
    #for v in arg:
        #if not v or v.is_nil:
            #continue
        #if not v.is_reg and not v.is_mem:
            #continue
        #if v.xvar:
            #res += "%s->%s, " % (v.xvar, v)
    #if res:
        #return "  #"+res
    return ""

class BassOpr:
    @property
    def is_reg(self):
        return isinstance(self, Register)
    @property
    def is_var(self):
        return isinstance(self, Var)
    @property
    def is_imm(self):
        return isinstance(self, Imm)
    @property
    def is_mem(self):
        return isinstance(self, Cell)
    @property
    def is_nil(self):
        return False

class Cell(BassOpr):
    def __init__(self, val, var=None):
        self.val = val
        self.xvar = var
    def __eq__(self, other):
        if not isinstance(other, Cell):
            return False
        return self.val == other.val
    def validate(self, dfn):
        return True
    def get_dfn(self):
        return set()
    def __str__(self):
        return "("+str(self.val)+")"
    def get_used(self):
        return set()
    def get_offset(self):
        return str(self.val*4)
    def allocate(self):
        assert False, "Cannot allocate register for a cell"

class Register(BassOpr):
    def __eq__(self, other):
        return other.val == self.val
    def __hash__(self):
        return str(self).__hash__()
    def __init__(self, val, var=None):
        self.val = val
        self.used = True
        self.xvar = var
    def validate(self, dfn):
        return True
    def get_dfn(self):
        return set()
    def __str__(self):
        return "$"+self.val
    def get_used(self):
        return set()
    def allocate(self):
        assert False, "Cannot allocate register for a register"

class Imm(BassOpr):
    def __init__(self, number):
        assert isinstance(number, int)
        self.val = number
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


class Var(BassOpr):
    def __init__(self, var, dst=False):
        self.val = var
        self.dst = dst
        self.used = False
    def validate(self, dfn):
        if not self.dst:
            assert self in dfn, "%s not defined" % self
        else :
            assert self not in dfn
    def get_dfn(self):
        assert self.dst
        return {self}
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
        return {self}
    def allocate(self, regmap):
        #assert self.val in regmap
        if self in regmap:
            regmap[self].xvar = self
            return regmap[self]
        return self
    def mark_as_used(self):
        assert self.dst
        self.used = True
    def mark_as_unused(self):
        assert self.dst
        self.used = False

class Nil:
    def __init__(self, var=0, dst=0):
        self.is_nil = True
    def validate(self, dfn):
        return True
    def get_dfn(self):
        return set()
    @property
    def val(self):
        assert False
    def __str__(self):
        return "Nil()"
    def get_used(self):
        return set()
    def allocate(self, _):
        return self

def get_operand(val, dst=False):
    if isinstance(val, Nil) or isinstance(val, Var) or isinstance(val, Register) or isinstance(val, Cell):
        if dst :
            assert (val.is_var and val.dst) or val.is_reg
        return val
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

class BaseIns:
    last_use = None #Which variable is used the last time in this instructions
    def get_used(self):
        assert False, self

class NIns(BaseIns):
    'Normal instructions, not end of basic block or phi'
    is_br = False
    is_phi = False
    def __init__(self):
        self.dst = None
    def mark_as_used(self):
        self.dst.mark_as_used()
    def mark_as_unused(self):
        self.dst.mark_as_unused()
    @property
    def used(self):
        if self.dst.is_var:
            return self.dst.used
        return True
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
        if self.opr2.is_imm:
            if self.opr2.val == 0 and self.opr1 == self.dst:
                print("%s is NOP" % self)
                return ""
        assert self.opr1.is_reg
        assert self.opr2.is_reg or self.opr2.is_imm
        return "\t%s %s, %s, %s\n" % (self.opname[self.op], str(self.dst), str(self.opr1), str(self.opr2))

    def __init__(self, op, dst, opr1, opr2):
        assert op in self.opc
        self.op = self.opc[op]
        self.dst = get_operand(dst, True)
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
        res = "%s %s, %s, %s" % (self.opname[self.op], str(self.dst), str(self.opr1), str(self.opr2))
        res += gen_rvmap(self.dst, self.opr1, self.opr2)
        return res
    def get_used(self):
        return self.opr1.get_used()|self.opr2.get_used()

class IInpt(NIns):
    def __init__(self, dst):
        if dst is None:
            self.dst = Nil()
        else :
            self.dst = get_operand(dst, True)
    def validate(self, dfn):
        self.dst.validate(dfn)
    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
    def get_used(self):
        return set()
    def gencode(self):
      out = "\tli $v0, 5\n\tsyscall\n"
      if not self.dst.is_nil:
          assert self.dst.is_reg
          out += "\tadd %s, $v0, 0\n" % str(self.dst)
      return out
    def mark_as_used(self):
        if not self.dst.is_nil:
            self.dst.mark_as_used()
    def mark_as_unused(self):
        if not self.dst.is_nil:
            self.dst.mark_as_unused()
    @property
    def used(self):
        if not self.dst.is_nil:
            return self.dst.used
        return True
    def __str__(self):
        return "input "+str(self.dst)+gen_rvmap(self.dst)

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
        return "print "+str(self.var)+gen_rvmap(self.var)
    def get_used(self):
        return self.var.get_used()
    def mark_as_used(self):
        pass
    @property
    def used(self):
        return True
    def gencode(self):
        out = ""
        if self.var.is_reg:
            out += "\tadd $a0, %s, 0\n" % str(self.var)
        else :
            assert self.var.is_imm
            out += "\tli $a0, %s\n" % str(self.var)
        out += "\tli $v0, 1\n\tsyscall\n"
        out += "\tli $v0, 4\n\tla $a0, nl\n\tsyscall\n"
        return out

class Cmp(NIns):
    '0 : seq'
    opname = {
            0 : "seq",
            1 : "sle",
            2 : "slt",
            3 : "sge",
            4 : "sgt",
            5 : "sne"
    }
    opc = {'==': 0, '<=': 1, '<' : 2, '>=': 3, '>' : 4, '!=': 5}
    iopc = {0: 0, 1: 4, 2: 3, 3: 2, 4: 1, 5: 5}
    def gencode(self):
        assert self.dst.is_reg
        if self.src1.is_imm and self.src2.is_imm:
            assert False
        if self.src1.is_imm:
            assert self.src2.is_reg
            return "\t%s %s, %s, %s\n" % (self.opname[self.iopc[self.op]], str(self.dst), str(self.src2), str(self.src1))
        else :
            assert self.src1.is_reg, self.src1
            assert self.src2.is_reg or self.src2.is_imm
            return "\t%s %s, %s, %s\n" % (self.opname[self.op], str(self.dst), str(self.src1), str(self.src2))
    def __init__(self, op, src1, src2, dst):
        assert op in self.opc
        self.op = self.opc[op]
        self.src1 = get_operand(src1)
        self.src2 = get_operand(src2)
        self.dst = get_operand(dst, True)
        self.is_phi = False
        self.is_br = False
    def allocate(self, regmap):
        _dict_print(regmap)
        self.dst = self.dst.allocate(regmap)
        self.src1 = self.src1.allocate(regmap)
        self.src2 = self.src2.allocate(regmap)
    def get_used(self):
        return self.src1.get_used()|self.src2.get_used()
    def validate(self, dfn):
        self.src1.validate(dfn)
        self.src2.validate(dfn)
        self.dst.validate(dfn)
    def __str__(self):
        res = self.opname[self.op]+" "+str(self.dst)+", "+str(self.src1)+", "+str(self.src2)
        res += gen_rvmap(self.dst, self.src1, self.src2)
        return res

class Br(BaseIns):
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
        self.used = True
    def validate(self, dfn):
        self.src.validate(dfn)
    def allocate(self, regmap):
        print(regmap)
        self.src = self.src.allocate(regmap)
    def get_dfn(self):
        return set()
    def get_used(self):
        if self.src:
            return self.src.get_used()
        return set()
    def gencode(self):
        real_tgt = self.tgt
        if self.op == 0:
            return "\tb "+real_tgt+"\n"
        assert self.src.is_reg
        return "\t"+self.brname[self.op]+" "+str(self.src)+", "+real_tgt+"\n"
    def __str__(self):
        if not self.src.is_nil :
            res = self.brname[self.op]+" "+str(self.src)+", "+self.tgt
        else :
            res = self.brname[self.op]+" "+self.tgt
        res += gen_rvmap(self.src)
        return res

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
        self.dst = get_operand(dst, True)
    def mark_as_used(self):
        self.dst.mark_as_used()
    def mark_as_unused(self):
        self.dst.mark_as_unused()
    @property
    def used(self):
        return self.dst.used
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
            #assert not var == self.dst, "Phi %s -> %s" % (var, self.dst)
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

def load_or_move(src, dst):
    assert dst.is_reg
    if src.is_imm:
        return "\tli "+str(dst)+", "+str(src)+"\n"
    elif src.is_reg:
        return "\tadd %s, %s, 0\n" % (str(dst), str(src))
    else :
        return "\tlw %s, %s($sp)\n" % (str(dst), src.get_offset())

def move_or_store(src, dst):
    assert src.is_reg
    if dst.is_reg:
        return "\tadd %s, %s, 0\n" % (str(dst), str(src))
    else :
        return "\tsw "+str(src)+", "+dst.get_offset()+"($sp)\n"

class Load(NIns):
    def __init__(self, dst, m):
        if isinstance(m, int):
            m = Imm(m)
        assert isinstance(m, Cell) or isinstance(m, Imm), str(m)
        if isinstance(dst, str):
            dst = get_operand(dst, True)
        assert isinstance(dst, Register) or isinstance(dst, Var)
        self.dst = dst
        self.m = m
        self.is_phi = False
        self.is_br = False
    def __str__(self):
        return "load %s, %s" % (str(self.dst), str(self.m))
    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
    def get_used(self):
        return set()
    def gencode(self):
        return load_or_move(self.m, self.dst)
    def validate(self, dfn):
        self.dst.validate(dfn)

class Store(NIns):
    def __init__(self, dst, r):
        assert isinstance(r, Register)
        assert isinstance(dst, Cell)
        self.dst = dst
        self.r = r
    def gencode(self):
        return move_or_store(self.r, self.dst)
    def validate(self, dfn):
        self.r.validate(dfn)
    def get_used(self):
        return self.r.get_used()
    def __str__(self):
        return "store %s, %s" % (str(self.dst), str(self.r))

class BB:
    '''
    Last and only the last instruction can be Br
    Phi instructions must be at the beginning of a bb
    '''
    def __str__(self):
        res = self.name+":\n"
        res += "#availbb: "+str(self.availbb)+"\n"
        res += "#pred: "+str(self.predecessors)+"\n"
        res += "#succ: "+str(self.successors)+"\n"
        res += "#fall through: "+str(self.fall_through)+"\n"
        res += "#In: "+_str_set(self.In)+"\n"
        if self.required:
            res += "#Required: "+str(self.required)+"\n"
        for n, i in enumerate(self.ins):
            if i is self.br:
                break
            res += "\t"+str(i)
            if not i.used:
                res += "  #unused"
            res += "\n"
        if self.br:
            res += "\t"+str(self.br)+"  #end\n"
        res += "#Out: "+_str_set(self.out)+"\n"
        if self.out_reg:
            res += "#Out_reg: \n"
            for k, v in self.out_reg.items():
                res += str(k)+": "+str(v)+", "
            res += "\n"
        return res
    def gencode(self):
        res = self.name+":\n"
        for i in self.ins:
            res += i.gencode()
        return res
    def __hash__(self):
        return self.name.__hash__()
    def __eq__(self, other):
        return self is other
    def __init__(self, name, ins=[]):
        #dfn is variable defined in all paths lead to this bb
        self.ins = []
        self.name = name
        self.allocated = False #is register allocation done
        self.avail_done = False
        self.inout_done = False
        self.end = False
        self.br = None
        self.nxt = None
        self.phi = []
        self._phi = True
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
        self.out_reg = {}
        self.required = set()
        self.dombb = set()
        if ins:
            self += ins

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
        self.In = (self.out|self.internal_used)-self.internal_dfn
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
            #print(self)
            raise Exception("Appending instruction after end of BB")
        if self.availbb :
            raise Exception("Appending instruction after calc availbb")
        ins = copy.copy(_ins)
        while ins:
            i = ins.pop(0)
            if i.is_phi and not self._phi:
                raise Exception("Phi instructions in the middle of a BB")
            if not i.is_phi and self._phi:
                self._phi = False
                self.phi = self.ins[0:]
            if i.is_br:
                if ins:
                    raise Exception("Branch not at end of BB.")
                self.end = True
                self.br = i
                self.nxt = i.tgt
                self.fall_through = i.is_cond
            self.ins.append(i)
        return self
    @property
    def nonbr_ins(self):
        if not self.ins:
            return []
        if self.ins[-1].is_br:
            return self.ins[0:-1]
        return self.ins
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
    def finish(self):
        if self._phi:
            self.phi = self.ins[0:]
        self.end = True
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
    def liveness(self):
        alive = set(self.out)
        for i in reversed(self.ins):
            if i.is_phi:
                break
            u = i.get_used()
            i.last_use = set()
            for v in u:
                if v not in alive:
                    i.last_use |= {v}
                    alive |= {v}
            ds = i.get_dfn()
            if ds:
                d, = ds
                if d in alive:
                    i.mark_as_used()
                    alive -= {d}
        for i in self.ins:
            if not i.is_phi:
                continue
            d, = i.get_dfn()
            if d in alive:
                i.mark_as_used()

    def assign_out_reg(self, vrmap):
        for v in self.out:
            assert v in vrmap, "%s not allocated" % v
            self.out_reg[v] = vrmap[v]

class IR:
    def __str__(self):
        res = "\n\n==========================IR============================\n"
        for bb in self.bb:
            res += str(bb)
        return res

    def __init__(self, bb=[]):
        self.bb = copy.copy(bb)
        self.bbmap = {}
        self.bbcnt = 0

    def __iadd__(self, o):
        for i in o:
            if i.name in self.bbmap:
                raise Exception("Basic blocks with duplicated name")
            self.bbmap[i.name] = i
            self.bb.append(i)
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
            h = queue.pop()
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
            #print("%s: new In %s, new out %s" % (h, self.bbmap[h].In, self.bbmap[h].out))
        for bb in self.bb:
            bb.inout_finish(self.bbmap)

    def gencode(self, fname):
        f = open(fname, 'w')
        f.write(".data\nnl: .asciiz \"\\n\"\n")
        f.write(".text\nmain:\n")
        for bb in self.bb:
            f.write(bb.gencode())
        f.write("\tli $v0, 10\n\tsyscall\n")
        f.close()
    def finish(self):
        print(self)
        for bb in self.bb:
            bb.finish()
        self.calc_connections()
        self.calc_avail()
        print(self)
        self.validate()
        self.calc_inout()
        for bb in self.bb:
            bb.liveness()

    @property
    def last_bb(self):
        return self.bb[-1]
    def validate(self):
        for i in self.bb:
            i.validate(self.bbmap)

all_reg = [Register(x) for x in usable_reg]
