import IR.instruction as IRI
import IR.operand as opr
import IR.mod as mod
from IR import dfa
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


def eval_const(i, value):
    if isinstance(i, IRI.Load):
        if i.m.is_imm:
            logging.info("%s is a const because it loads a const %d", i.dst, i.m.val)
            value[i.dst] = i.m.val
            return value[i.dst]
        return None

    if isinstance(i, IRI.Arithm) or isinstance(i, IRI.Cmp):
        opr1 = i.opr1
        if not opr1.is_imm:
            if opr1 not in value:
                return None
            opr1 = value[opr1]
        else :
            opr1 = opr1.val
        opr2 = i.opr2
        if not opr2.is_imm:
            if opr2 not in value:
                return None
            opr2 = value[opr2]
        else :
            opr2 = opr2.val

        res = int(eval("%d%s%d" % (opr1, i.ops[i.op], opr2)))
        logging.info("%s is a const because %s", i.dst, i)
        value[i.dst] = res
        return res
    return None

def const_transfer(bb, const):
    logging.info("============Const for %s=============", bb.name)
    value = {}
    for p in bb.preds:
        for v in const[p]:
            if v in value:
                assert value[v] == const[p][v]
                continue
            value[v] = const[p][v]
    for i in bb.ins:
        eval_const(i, value)
    if value != const[bb]:
        const[bb] = value
        return True
    return False

def const_propagation(fn, fmap):
    set_log_phase("const"+fn.name)
    const = {}
    dfa.dfa_run(fn, const_transfer, const, {}, False)
    changed = False
    nfn = mod.Func(fn.name, fn.param, fn.rety)
    for bb in fn.bb:
        nbb = mod.BB(bb.name, bb)
        val = {}
        for v in const[bb]:
            val[v] = opr.Imm(const[bb][v])
        allv = set(val)
        logging.info("Value in %s, %s", bb.name, _str_dict(val))
        for i in nbb.ins+[nbb.br]:
            u = i.get_used()
            if u&allv:
                changed = True
            i.allocate(val, False)
        nfn += [nbb]
    nfn.finish(fmap)
    unset_log_phase()
    return (changed, nfn)

