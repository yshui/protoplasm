import copy
from utils import _str_set, _str_dict, _dict_print, _set_print
from functools import reduce
import logging
from .operand import Register, Cell, Global, get_operand
from .dfa import dfa_run

def print(*_):
    assert False

def _str_bb_list(a):
    res = ""
    for bb in a:
        if isinstance(bb, BB):
            res += bb.name+", "
        else :
            res += str(bb)+", "
    if a:
        res = res[:-2]
    return res
class BB:
    '''
    Last and only the last instruction can be Br
    Phi instructions must be at the beginning of a bb
    '''
    def __str__(self):
        res = self.name+":\n"
        res += "#availbb: "+_str_bb_list(self.avail)+"\n"
        res += "#a_dfn: "+_str_set(self.a_dfn)+"\n"
        res += "#pred: "+_str_bb_list(self.preds)+"\n"
        res += "#succ: "+_str_bb_list(self.succs)+"\n"
        res += "#In: "+_str_set(self.In)+"\n"
        for i in self.phis:
            res += "\t"+str(i)+"\n"
        for i in self.ins:
            res += "\t"+str(i)+"\n"
        res += "\t"+str(self.br)+"\t#end\n"
        res += "#Out: "+_str_set(self.out)+"\n"
        if self.out_reg:
            res += "#Out_reg: \n"
            for k, v in self.out_reg.items():
                res += str(k)+": "+str(v)+", "
            res += "\n"
        return res
    def gencode(self, ir, nextbb):
        res = self.name+":\n"
        assert not self.phis
        for i in self.ins:
            res += i.gencode(ir)
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
        self.br = None
        self.in_dfn = set() #in_dfn = definitions in this bb
        self.a_dfn = set() #available definitions
        self.in_used = set()
        self.succs = [] #next[0] = branch taken, next[1] = otherwise
        self.preds = []
        self.validated = False
        self.avail = set()
        self.out = set()
        self.In = set()
        self.out_reg = {}
        self.sub = set()
        self.entry = None
        if bb:
            self += bb.phis
            self += bb.ins
            self += [bb.br]

    @property
    def internal_used(self):
        if self.in_used:
            return self.in_used
        for i in self.ins+[self.br]:
            self.in_used |= i.get_used()
        return self.in_used
    @property
    def internal_dfn(self):
        if self.in_dfn:
            return self.in_dfn
        for i in self.phis+self.ins:
            x = i.get_dfn()
            assert not x & self.in_dfn, "Variable "+_str_set(x)+"defined again"
            self.in_dfn |= x
        if self.entry:
            self.in_dfn |= set(self.entry)
        return self.in_dfn

    def __iadd__(self, _ins):
        ins = copy.copy(_ins)
        while ins:
            assert not self.br, "Appending instruction after end of BB %s" % self
            i = copy.copy(ins.pop(0))
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
    def validate(self, rety, fmap):
        assert self.br
        self.validated = True
        dfn = set(self.In)
        if self.entry:
            dfn |= set(self.entry)
        assert not self.phis or len(self.preds) > 1, "Only 1 predecessor, but has phis"
        for i in self.phis:
            i.validate(self.preds)
            dfn |= {i.dst}
        for i in self.ins:
            assert i.get_used() <= dfn, "%s is undefined" % _str_set(i.get_used()-dfn)
            i.validate(fmap)
            dfn |= {i.dst}
    def machine_validate(self, fmap):
        assert not self.phis
        for i in self.ins:
            i.machine_validate(fmap)
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

def _phi_get_used(succ, pred):
    u = set()
    for i in succ.phis:
        assert pred.name in i.srcs, "%s %s" % (i, pred.name)
        if i.srcs[pred.name].is_var:
            u |= {i.srcs[pred.name]}
    return u
def inout_transfer(bb, In):
    out = set()


    for n in bb.succs:
        out |= In[n]
        #logging.info("Phi %s->%s, %s", bb.name, n.name, _str_set(_phi_get_used(n, bb)))
        out |= _phi_get_used(n, bb)

    #logging.info(str(bb.name)+"'s out:"+_str_set(out))
    #logging.info(str(bb.name)+"'s use:"+_str_set(bb.internal_used))
    #logging.info(str(bb.name)+"'s dfn:"+_str_set(bb.internal_dfn))
    new_in = (out|bb.internal_used)-bb.internal_dfn
    if new_in != In[bb]:
        #logging.info("Update %s's In add %s " % (bb.name, _str_set(new_in-In[bb])))
        In[bb] = new_in
        return True
    return False

def available_transfer(bb, avail):
    if not bb.preds or bb.entry is not None:
        assert bb.entry is not None, "BB %s unreachable, %s" % (bb.name, bb.entry)
        ret = bool(avail[bb])
        avail[bb] = set()
        return ret
    logging.info("BB %s, prev %s", bb.name, _str_bb_list(avail[bb]))
    new_avail = avail[bb.preds[0]]|{bb.preds[0]}
    for pbb in bb.preds[1:]:
        new_avail &= avail[pbb]|{pbb}
    logging.info("now: %s", _str_bb_list(new_avail))
    if new_avail != avail[bb]:
        logging.info("update")
        avail[bb] = new_avail
        return True
    logging.info("not update")
    return False

class Func:
    def tgt_used(self, n):
        for bb in self.bb:
            if n == bb.br.tgt[0] or n == bb.br.tgt[1]:
                return True
        return False
    def glob_for_str(self, s):
        if s not in self.ir.str_map:
            self.ir.str_map[s] = Global("str_%d" % len(self.ir.str_map))
            self.ir.globs[self.ir.str_map[s]] = s
        return self.ir.str_map[s]
    def mangle(self):
        res = "_Z"+self.name
        res += str(len(self.param))
        for p in self.param:
            res += str(p.get_type())
        return res
    def __str__(self):
        res = "defun "+self.name+"("
        for p in self.param:
            res += str(p)+","
        if self.param:
            res = res[:-1]
        res += ")\n"
        res += "#Used parameters: %s\n" % _str_set(self.bb[0].In)
        for bb in self.bb:
            res += str(bb)
        res += "endfun\n"
        return res

    def __init__(self, name, param, rety, bb=None):
        if bb:
            self.bb = copy.copy(bb)
        else :
            self.bb = []
        self.namecnt = 0
        self.name = name
        self.param = [get_operand(p) for p in param]
        self.rety = rety
        self.finished = False
        self.is_machine_ir = False
        self.ir = None

    def __iadd__(self, o):
        for i in o:
            self.bb.append(i)
        return self

    def next_name(self):
        res = "L"+str(self.namecnt)
        self.namecnt += 1
        return self.mangle()+"_"+res

    def append_bb(self, name=None):
        if name is None:
            name = self.next_name()
        r = BB(name)
        self += [r]
        return r

    def calc_connections(self):
        bbmap = {}
        for i in self.bb:
            assert i.name not in bbmap, "Basic blocks with duplicated name "+i.name
            bbmap[i.name] = i
        for i in self.bb:
            nsuccs = []
            for succ in i.succs:
                if not succ:
                    continue
                s = bbmap[succ]
                nsuccs.append(s)
                s.preds.append(i)
            i.succs = nsuccs

    def calc_avail(self):
        '''calculate blocks that are 'available' to this bb
        the definition of 'available' is the same as in the slides
        the 'available' variable would than be all variable defined in available blocks'''
        avail = {}
        dfa_run(self, available_transfer, avail, set(self.bb), False)
        for bb in self.bb:
            logging.info("BBxx  %s, %s", bb.name, _str_bb_list(avail[bb]))
            bb.avail = avail[bb]
            for p in bb.avail:
#                self.a_dfn |= p.internal_dfn
                p.sub |= {bb}

    def calc_inout(self):
        In = {}
        dfa_run(self, inout_transfer, In, set())
        logging.info(In)
        for bb in self.bb:
            bb.In = set(In[bb])
            for p in bb.preds:
                p.out |= bb.In|_phi_get_used(bb, p)

    def gencode(self, ir):
        assert self.is_machine_ir
        res = self.mangle()+":\n"
        #shift the stack pointer
        numbb = len(self.bb)
        for n, bb in enumerate(self.bb):
            nextbb = None
            if n+1 < numbb:
                nextbb = self.bb[n+1]
            res += bb.gencode(self, nextbb)
        return res

    def finish(self, fmap):
        self.finished = True
        logging.debug(self)
        self.calc_connections()
        self.bb[0].entry = self.param
        logging.info(self)
        self.calc_avail()

        self.calc_inout()
        logging.info(self)
        self.validate(fmap)
        for bb in self.bb:
            bb.liveness()

    def machine_finish(self, fmap):
        self.finished = True
        self.calc_connections()
        self.machine_validate(fmap)
        self.is_machine_ir = True

    @property
    def last_bb(self):
        assert self.bb
        return self.bb[-1]

    def validate(self, fmap):
        dfn = set()
        allname = set()
        for bb in self.bb:
            for i in bb.ins+bb.phis:
                d = i.get_dfn()
                assert not d&dfn, "%s is defined again" % _str_set(d&dfn)
                dfn |= d
            allname |= {bb.name}

        for i in self.bb:
            assert i.preds or not i.In, "Variables "+_str_set(i.In)+"not defined"
            i.validate(self.rety, fmap)
            i.br.validate(allname, self.rety)

    def machine_validate(self, fmap):
        allname = set()
        for i in self.bb:
            assert i.name not in allname, "Basic blocks with duplicated name "+i.name
            allname |= {i.name}
        for i in self.bb:
            i.machine_validate(fmap)
            i.br.machine_validate(allname)

class BuiltinFn:
    def __init__(self, name, code, rety, nparam):
        self.name = name
        self.code = code
        self.rety = rety
        self.param = [i for i in range(0, nparam)]
    def gencode(self):
        return self.name+":\n"+self.code
    def mangle(self):
        return self.name

class IR:
    def __init__(self, func=None):
        self.func = []
        self.builtin = []
        self.fmap = {}
        self.str_map = {}
        self.globs = {}
        if func:
            self += func

    def __str__(self):
        res = ""
        for f in self.func:
            res += str(f)
        return res

    def __iadd__(self, f):
        if isinstance(f, Func):
            f = [f]
        for func in f:
            if isinstance(func, Func):
                self.func.append(func)
            else :
                assert isinstance(func, BuiltinFn)
                self.builtin.append(func)
            self.fmap[func.name] = func
        return self

    def finish(self):
        for func in self.func:
            func.finish(self.fmap)

    def machin_finish(self):
        for func in self.func:
            func.machine_finish(self.fmap)
        for func in self.builtin:
            func.machine_finish()

    def validate(self):
        assert "main" in self.fmap
        for func in self.func:
            func.validate(self.fmap)

    def gencode(self, fname):
        f = open(fname, 'w')
        f.write(".data\n")
        for n, d in self.globs.items():
            if isinstance(d, str):
                f.write("%s: .asciiz \"%s\"\n" % (n.get_name(), d))
            else :
                f.write("%s: .word %d\n" % (n.get_name(), d))

        f.write(".text\n")

        for func in self.builtin:
            f.write(func.gencode())

        f.write("main:\n\tj %s\n" % self.fmap["main"].mangle())

        for func in self.func:
            f.write(func.gencode(self))

        logging.log(21, "Output written to %s", fname)
