import copy
from utils import _str_set, _str_dict, _dict_print, _set_print
from functools import reduce
import logging
from .operand import Register, Cell, Global, get_operand
class EntryBB:
    def __init__(self, args, succ):
        self.out_reg = {}
        self.internal_dfn = set(args)
        self.dombb = set()
        self.availbb = set()
        self.out = set()
        self.In = set()
        self.succs = [succ]
        for n, v in enumerate(args):
            if n > 3:
                break
            self.out_reg[v] = Register("a%d" % n)
        #arguments are passed in reverse order
        top = len(args)-4
        for n, v in enumerate(args[3:]):
            self.out_reg[v] = Cell((top-n)*4)
    def inout_next(self, *_):
        pass
    def inout_finish(self):
        pass

class BB:
    '''
    Last and only the last instruction can be Br
    Phi instructions must be at the beginning of a bb
    '''
    def __str__(self):
        res = self.name+":\n"
        res += "#availbb: "+str(self.availbb)+"\n"
        res += "#a_dfn: "+_str_set(self.a_dfn)+"\n"
        res += "#pred: "+str(self.preds)+"\n"
        res += "#succ: "+str(self.succs)+"\n"
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
                    queue |= {bbmap[nbb]}
            self.availbb = set(availbb_next)

    def avail_finish(self, bbmap):
        self.avail_done = True
        self.a_dfn = set()
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
        assert self.avail_done, "Call calc_avail before get avail_dfn"
        return self.a_dfn
    @property
    def internal_dfn(self):
        if self.in_dfn:
            return self.in_dfn
        for i in self.phis+self.ins:
            self.in_dfn |= i.get_dfn()
        return self.in_dfn
    def validate(self, fname, bbmap, fmap):
        #with the help of available dfn
        #we can make sure all of the variables used in this bb
        #is always defined on all the paths leading to this bb
        assert self.br
        self.validated = True
        _dfn = set(self.a_dfn)
        #skip phi instructions, only get their defines
        #because phi instruction can grab a variable defined later in this bb
        for i in self.phis:
            i.validate(self.preds, bbmap)
            _dfn |= i.get_dfn()
        #validate other instructions
        for i in self.ins:
            i.validate(_dfn, fmap)
            _dfn |= i.get_dfn()
        self.br.validate(_dfn, fmap[fname])
    def machine_validate(self, bbmap, fmap):
        assert not self.phis
        for i in self.ins:
            i.machine_validate(fmap)
        self.br.machine_validate(bbmap)
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

class Func:
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
        if 0 in self.bbmap:
            res += "#Used parameters: %s\n" % _str_set(self.bbmap[0].out)
        for bb in self.bb:
            res += str(bb)
        res += "endfun\n"
        return res

    def __init__(self, name, param, rety, bb=None):
        if bb:
            self.bb = copy.copy(bb)
        else :
            self.bb = []
        self.bbmap = {}
        self.namecnt = 0
        self.name = name
        self.param = [get_operand(p) for p in param]
        self.rety = rety
        self.finished = False
        self.is_machine_ir = False
        self.ir = None

    def __iadd__(self, o):
        for i in o:
            assert i.name not in self.bbmap, "Basic blocks with duplicated name "+i.name+str(self.bbmap)
            self.bbmap[i.name] = i
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
        reachable = set()
        for bb in self.bb:
            bb.availbb = init
        queue = {self.bb[0]}
        while queue :
            h = queue.pop()
            reachable |= {h}
            h.avail_next(self.bbmap, queue)
        for bb in self.bb:
            if bb not in reachable:
                bb.availbb = set()
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

    def gencode(self, ir):
        assert self.is_machine_ir
        res = self.mangle()+":\n"
        #shift the stack pointer
        numbb = len(self.bb)
        for n, bb in enumerate(self.bb):
            nextbb = None
            if n+1 < numbb:
                nextbb = self.bb[n+1].name
            res += bb.gencode(self, nextbb)
        return res

    def finish(self, fmap):
        self.finished = True
        self.bb[0].preds = [0]
        self.bbmap[0] = EntryBB(self.param, self.bb[0].name)
        logging.debug(self)
        self.calc_connections()
        self.calc_avail()
        self.validate(fmap)
        self.calc_inout()
        for bb in self.bb:
            bb.liveness()

    def machine_finish(self, fmap):
        self.finished = True
        self.machine_validate(fmap)
        self.is_machine_ir = True

    @property
    def last_bb(self):
        return self.bb[-1]

    def validate(self, fmap):
        for i in self.bb:
            i.validate(self.name, self.bbmap, fmap)

    def machine_validate(self, fmap):
        for i in self.bb:
            i.machine_validate(self.bbmap, fmap)

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
