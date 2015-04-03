import copy
from utils import _str_set, _dict_print, _set_print
from functools import reduce
import logging

usable_reg = []
for __i in range(0, 2):
    usable_reg += ["t{0}".format(__i)]
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
                logging.info("%s is NOP" % self)
                return ""
        assert self.opr1.is_reg
        assert self.opr2.is_reg or self.opr2.is_imm
        return "\t%s %s, %s, %s\n" % (self.opname[self.op], str(self.dst), str(self.opr1), str(self.opr2))

    def __init__(self, op, dst, opr1, opr2):
        assert op in self.opc
        self.op = self.opc[op]
        self.dst = get_operand(dst, True)
        self.opr1 = get_operand(opr1)
        self.opr2 = get_operand(opr2)
        if self.opr1.is_imm:
            if self.opr1.val == 0:
                #use the 0 register
                self.opr1 = Register("r0")
            elif self.op in {1, 3, 6, 7}:
                #swap opr1 and opr2 for +, *, &, |
                self.opr1, self.opr2 = self.opr2, self.opr1
            else :
                #otherwise fail
                assert False

    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
        self.opr1 = self.opr1.allocate(regmap)
        self.opr2 = self.opr2.allocate(regmap)
    def validate(self, dfn):
        self.opr1.validate(dfn)
        self.opr2.validate(dfn)
        self.dst.validate(dfn)
    def __str__(self):
        res = "%s = %s, %s, %s" % (self.dst, self.opname[self.op], str(self.opr1), str(self.opr2))
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
    @property
    def used(self):
        if not self.dst.is_nil:
            return self.dst.used
        return True
    def __str__(self):
        return "%s = input " % self.dst

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
        return "print %s" % self.var
    def get_used(self):
        return self.var.get_used()
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
        res = "%s = cmp %s %s, %s" % (self.dst, self.opname[self.op], self.src1, self.src2)
        return res

class Br(BaseIns):
    '0 : j, 1 : beqz, 2 : bnez'
    brname = {
            0 : "j",
            1 : "beqz",
            2 : "bnez",
    }
    def __init__(self, op, src, target, target2):
        self.src = get_operand(src)
        self.tgt = [target, target2]
        self.op = op
        self.is_br = True
        self.is_phi = False
        self.used = True
    def validate(self, dfn):
        self.src.validate(dfn)
    def allocate(self, regmap):
        logging.debug(regmap)
        self.src = self.src.allocate(regmap)
    def get_dfn(self):
        return set()
    def get_used(self):
        if self.src:
            return self.src.get_used()
        return set()
    def gencode(self, nextbb):
        if self.op == 0:
            if self.tgt[0] != nextbb:
                return "\tb "+self.tgt[0]+"\n"
            else :
                return ""
        assert self.src.is_reg
        res = "\t%s %s, %s\n" % (self.brname[self.op], self.src, self.tgt[0])
        if self.tgt[1] != nextbb:
            res += ("\tb %s\n" % self.tgt[1])
        return res
    def __str__(self):
        if not self.src.is_nil :
            res = "br %s %s, [ %s, %s ]" % (self.brname[self.op], self.src, self.tgt[0], self.tgt[1])
        else :
            res = "br %s [ %s ]" % (self.brname[self.op], self.tgt[0])
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
            logging.debug("{0} does point to us".format(src))
            #are we referring to ourselves?
            #assert not var == self.dst, "Phi %s -> %s" % (var, self.dst)
            #is var defined in src?
            _dfn = bbmap[src].internal_dfn|bbmap[src].avail_dfn
            var.validate(_dfn)
            logging.debug("{0} is defined in {1}".format(var, src))
        for pred in bb.preds:
            assert pred in self.srcs
        assert len(bb.preds) == len(self.srcs), "%s %s" % (bb, self)
    def __str__(self):
        res = "%s = phi " % self.dst
        for x, y in self.srcs.items():
            res += "[ %s: %s ], " % (x, y)
        return res[:-2]

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
        return "%s = load %s" % (str(self.dst), str(self.m))
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
        assert isinstance(r, Register), r
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

class Ret:
    def __init__(self):
        self.used = True
        self.is_br = True
        self.is_phi = False
        self.tgt = [None, None]
    def allocate(self, _):
        return
    def gencode(self, nextbb):
        return "\tjr $ra\n"
    def validate(self, _):
        return True
    def get_used(self):
        return set()
    def get_dfn(self):
        return set()
    def __str__(self):
        return "ret"

class BB:
    '''
    Last and only the last instruction can be Br
    Phi instructions must be at the beginning of a bb
    '''
    def __str__(self):
        res = self.name+":\n"
        res += "#availbb: "+str(self.availbb)+"\n"
        res += "#pred: "+str(self.preds)+"\n"
        res += "#succ: "+str(self.succs)+"\n"
        res += "#In: "+_str_set(self.In)+"\n"
        if self.required:
            res += "#Required: "+str(self.required)+"\n"
        for i in self.phis:
            res += "\t"+str(i)+"\n"
        for i in self.ins:
            res += "\t"+str(i)+"\n"
        res += "\t"+str(self.br)+"  #end\n"
        res += "#Out: "+_str_set(self.out)+"\n"
        if self.out_reg:
            res += "#Out_reg: \n"
            for k, v in self.out_reg.items():
                res += str(k)+": "+str(v)+", "
            res += "\n"
        return res
    def gencode(self, nextbb):
        res = self.name+":\n"
        assert not self.phis
        for i in self.ins:
            res += i.gencode()
        res += self.br.gencode(nextbb)
        return res
    def __hash__(self):
        return self.name.__hash__()
    def __eq__(self, other):
        return self is other
    def __init__(self, name, bb=None):
        #dfn is variable defined in all paths lead to this bb
        self.ins = []
        self.phis = []
        self.name = name
        self.avail_done = False
        self.inout_done = False
        self.br = None
        self.in_dfn = set() #in_dfn = definitions in this bb
        self.a_dfn = set() #available definitions
        self.in_used = set()
        self.succs = [] #next[0] = branch taken, next[1] = otherwise
        self.preds = []
        self.validated = False
        self.availbb = set()
        self.out = set()
        self.In = set()
        self.out_reg = {}
        self.required = set()
        self.dombb = set()
        if bb:
            self += bb.phis
            self += bb.ins
            self += [bb.br]

    def avail_next(self, bbmap, queue):
        if not self.preds:
            availbb_next = set()
        else :
            pabb = [bbmap[pbb].availbb|{pbb} for pbb in self.preds]
            availbb_next = reduce(lambda x, y: x&y, pabb)
        if availbb_next != self.availbb:
            for nbb in self.succs:
                if nbb:
                    queue |= {nbb}
            self.availbb = set(availbb_next)

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
        for i in self.ins+[self.br]:
            self.in_used |= i.get_used()
        return self.in_used

    def inout_next(self, bbmap, queue):
        self.In = (self.out|self.internal_used)-self.internal_dfn
        visited = set()
        for prevbb in self.preds:
            sbb = bbmap[prevbb]
            new_out = sbb.out|self.In
            for i in self.phis:
                srcu = i.srcs[prevbb].get_used()
                new_out |= srcu
            if new_out != sbb.out:
                sbb.out = new_out
                queue |= {prevbb}

    def inout_finish(self, bbmap):
        self.inout_done = True
        for abb in self.availbb:
            aabb = bbmap[abb]
            if aabb.out&self.In:
                self.required |= {abb}

    def __iadd__(self, _ins):
        ins = copy.copy(_ins)
        while ins:
            assert not self.br, "Appending instruction after end of BB %s" % self
            i = ins.pop(0)
            if i.is_phi:
                if self.ins:
                    raise Exception("Phi instructions in the middle of a BB")
                self.phis.append(i)
            else :
                if i.is_br:
                    self.br = i
                    self.succs = i.tgt
                else :
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
        for i in self.phis+self.ins:
            self.in_dfn |= i.get_dfn()
        return self.in_dfn
    def finish(self):
        assert self.br
    def validate(self, bbmap):
        #with the help of available dfn
        #we can make sure all of the variables used in this bb
        #is always defined on all the paths leading to this bb
        self.validated = True
        _dfn = copy.copy(self.a_dfn)
        #skip phi instructions, only get their defines
        #because phi instruction can grab a variable defined later in this bb
        for i in self.phis:
            i.validate(self, bbmap)
            _dfn |= i.get_dfn()
        #validate other instructions
        for i in self.ins:
            i.validate(_dfn)
            _dfn |= i.get_dfn()
    def liveness(self):
        #we assume there're no unreachable code
        #we have a pruning pass to make sure of that
        alive = set(self.out)
        for i in reversed(self.ins+[self.br]):
            u = i.get_used()
            i.last_use = set()
            for v in u:
                if v not in alive:
                    i.last_use |= {v}
                    alive |= {v}
            ds = i.get_dfn()
            if ds:
                d, = ds
                alive -= {d}

    def assign_out_reg(self, R):
        for v in self.out:
            assert v in R or v in R.M, "%s not allocated" % v
            self.out_reg[v] = R.get_reg_or_mem(v)

class IR:
    def __str__(self):
        res = "\n\n==========================IR============================\n"
        for bb in self.bb:
            res += str(bb)
        return res

    def __init__(self, bb=None):
        if bb:
            self.bb = copy.copy(bb)
        else :
            self.bb = []
        self.bbmap = {}
        self.namecnt = 0

    def __iadd__(self, o):
        for i in o:
            assert i.name not in self.bbmap, "Basic blocks with duplicated name "+i.name+str(self.bbmap)
            self.bbmap[i.name] = i
            self.bb.append(i)
        return self

    def next_name(self):
        res = "L"+str(self.namecnt)
        self.namecnt += 1
        return res

    def append_bb(self, name):
        if not name:
            name = self.next_name()
        r = BB(name)
        self += [r]
        return r

    def calc_connections(self):
        for i in self.bb:
            for succ in i.succs:
                if not succ:
                    continue
                assert succ in self.bbmap, "Jumping to a non-existent block %s" % succ
                self.bbmap[succ].preds.append(i.name)

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
        numbb = len(self.bb)
        for n, bb in enumerate(self.bb):
            nextbb = None
            if n+1 < numbb:
                nextbb = self.bb[n+1].name
            f.write(bb.gencode(nextbb))
        f.close()
    def finish(self):
        logging.debug(self)
        for bb in self.bb:
            bb.finish()
        self.calc_connections()
        self.calc_avail()
        logging.info(self)
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
