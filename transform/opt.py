import IR.instruction as IRI
import IR.operand as opr
import IR.mod as mod
from utils import DisjointSet, _str_dict
import copy
import logging
from . import set_log_phase, unset_log_phase
def is_copy(ins):
    if not isinstance(ins, IRI.Arithm):
        return None
    if ins.op == 1:
        if ins.opr1 == opr.Register("0") and ins.opr2.is_var:
            return ins.opr2
        if ins.opr2.is_imm and ins.opr2.val == 0 and ins.opr1.is_var:
            return ins.opr1
        return None
    elif ins.op == 2:
        if ins.opr2.is_imm and ins.opr2.val == 0 and ins.opr1.is_var:
            return ins.opr1
        return None
    elif ins.op == 3 or ins.op == 4:
        if ins.opr2.is_imm and ins.opr2.val == 1 and ins.opr1.is_var:
            return ins.opr1
        return None
    return None
def copy_propagation(fn, fmap):
    #first, get where is every variable defined
    set_log_phase("copy"+fn.name)
    logging.info("%s", fn)
    vset = {}
    for bb in fn.bb:
        for ins in bb.ins:
            ds = ins.get_dfn()
            if not ds:
                continue
            d, = ds
            src = is_copy(ins)
            if src is None:
                #not copy, or src is from a phi
                continue
            if src not in vset:
                vset[src] = DisjointSet(src)
            logging.info("!!!!:%s\n    set %s->%s", ins, d, src)
            vset[d] = DisjointSet(d)
            vset[src].union(vset[d])

    varmap = {}
    for v in vset:
        vp = vset[v].get_father().i
        if vp == v:
            continue
        varmap[v] = vp

    if not varmap:
        unset_log_phase()
        return (False, fn)

    logging.info(_str_dict(varmap))
    nfn = mod.Func(fn.name, fn.param, fn.rety)
    for bb in fn.bb:
        nbb = mod.BB(bb.name)
        nbb += bb.phis
        for ins in bb.ins:
            ni = copy.copy(ins)
            ni.allocate(varmap, False) #don't change dst
            nbb += [ni]
        nbb += [bb.br]
        nfn += [nbb]
    nfn.finish(fmap)
    unset_log_phase()
    return (True, nfn)

def const_propagation(fn, fmap):
    pass
