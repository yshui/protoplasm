#from IR import IR, BB, IR.Arithm, Phi, Var, IR.Cell, Nil, IInpt, Load, Store, Br, Rename, Register, mod.Func, all_reg
import IR.instruction as IRI
import IR.operand as opr
import IR.mod as mod
import IR.machine as machine
from . import set_log_phase, unset_log_phase
from collections import deque
from utils import _set_print, _dict_print, _str_dict, _str_set
import copy
import logging
def _phi_get_used(i):
    u = set()
    for _, v in i.srcs.items():
        if v.is_var:
            u |= {v}
    return u
def phi_branch_removal(bb, br, varmap):
    clear_phi = False
    for i in bb.phis:
        assert br in i.srcs
        logging.info("Removing %s from %s", br, i)
        del i.srcs[br]
        if len(i.srcs) == 1:
            clear_phi = True
            _, varmap[i.dst] = i.srcs.popitem()

    if clear_phi:
        bb.phis = []

def remap_all_uses(varmap, func):
    logging.info(_str_dict(varmap))
    def getmap(v):
        nonlocal varmap
        if v not in varmap:
            return v
        varmap[v] = getmap(varmap[v])
        return varmap[v]
    if varmap:
        for v in varmap:
            getmap(v)
        logging.info(_str_dict(varmap))
        for bb in func.bb:
            for i in bb.ins+[bb.br]:
                i.allocate(varmap)
            for i in bb.phis:
                for pred in i.srcs:
                    if i.srcs[pred] in varmap:
                        i.srcs[pred] = varmap[i.srcs[pred]]

def static_branch_removal(func, fmap):
    #remove all br with constant condition
    set_log_phase("static")
    nfn = mod.Func(func.name, func.param, func.rety)
    for bb in func.bb:
        nxbb = mod.BB(bb.name, bb)
        nfn += [nxbb]
    varmap = {}
    changed = False
    for bb in nfn.bb:
        if bb.br.src is None:
            continue
        if not bb.br.src.is_imm:
            continue
        #static branch
        logging.info("Static branch %s from %s", bb.br, bb.name)
        changed = True
        op = bb.br.op
        bb.br.op = 0
        bv = bb.br.src.val
        bb.br.src = opr.Nil()
        if (bv == 0 and op == 1) or (bv != 0 and op == 2):
            to_delete = bb.br.tgt[1]
        else :
            to_delete = bb.br.tgt[0]
            bb.br.tgt[0] = bb.br.tgt[1]
        bb.br.tgt[1] = None
        logging.info("Changed to %s" % bb.br)
        phi_branch_removal(nfn.bbmap[to_delete], bb.name, varmap)

    if not changed:
        unset_log_phase()
        return (False, func)

    remap_all_uses(varmap, nfn)
    nfn.calc_connections()
    logging.info(nfn)
    unset_log_phase()
    _, nfn = prune_unreachable(nfn, fmap)
    return (True, nfn)

def prune_unreachable(func, fmap):
    set_log_phase("unreachable"+func.name)
    logging.info(func)
    queue = {func.bb[0]}
    logging.info("BB[0] %s is always reachable", func.bb[0].name)
    removed = set(func.bb[1:])
    while queue:
        b = queue.pop()
        for s in b.succs:
            if s is None:
                continue
            ss = func.bbmap[s]
            if ss in removed:
                logging.info("BB %s is reachable", ss.name)
                removed -= {ss}
                queue |= {ss}

    if not removed:
        if not func.finished:
            func.finish()
        unset_log_phase()
        return (False, func)

    logging.info("Unreachable BBs:")
    for bb in removed:
        logging.info("* %s", bb.name)
    nfn = mod.Func(func.name, func.param, func.rety)
    for bb in func.bb:
        if bb not in removed:
            nxbb = mod.BB(bb.name, bb)
            nfn += [nxbb]

    varmap = {}
    for bb in removed:
        for s in bb.succs:
            if s is None:
                continue
            if func.bbmap[s] in removed:
                continue
            phi_branch_removal(nfn.bbmap[s], bb.name, varmap)

    remap_all_uses(varmap, nfn)

    logging.info(nfn)
    nfn.finish(fmap)
    unset_log_phase()
    return (True, nfn)

def sbr_and_unreachable(func, fmap):
    changed, nfn = static_branch_removal(func, fmap)
    if not changed:
        changed, nfn = prune_unreachable(func, fmap)
    return changed, nfn

def prune_unused(func, fmap):
    set_log_phase("prune"+func.name)
    logging.info(func)
    dfn_ins = {}
    used = set()
    queue = set()
    for bb in func.bb:
        for i in bb.phis+bb.ins+[bb.br]:
            ds = i.get_dfn()
            #Store, Invoke, Br and Ret are leaves
            if type(i) in {IRI.Invoke, IRI.Store, IRI.Ret, IRI.Br}:
                u = i.get_used()
                queue |= u
                used |= u
            if ds:
                d, = ds
                dfn_ins[d] = i
    while queue:
        d = queue.pop()
        if d in func.bbmap[0].out:
            #is a parameter
            continue
        assert d in dfn_ins, d
        i = dfn_ins[d]
        if i.is_phi:
            u = _phi_get_used(i)
        else :
            u = i.get_used()
        queue |= (u-used)
        used |= u

    nfn = mod.Func(func.name, func.param, func.rety)
    changed = False
    for bb in func.bb:
        nbb = mod.BB(bb.name)
        for i in bb.phis+bb.ins:
            ds = i.get_dfn()
            if not ds:
                nbb += [i]
                continue
            d, = ds
            if d not in used:
                logging.info("%s is not used", d)
                changed = True
                if isinstance(i, IRI.Invoke):
                    #the return value is not used
                    #but invoke can have side effects
                    ni = copy.copy(i)
                    ni.dst = opr.Nil()
                    nbb += [ni]
                continue
            nbb += [i]
        nbb += [bb.br]
        nfn += [nbb]
    nfn.finish(fmap)
    unset_log_phase()
    return (changed, nfn)


def block_coalesce(func, fmap):
    set_log_phase("bc"+func.name+str(func.is_machine_ir))
    logging.info(func)
    removed = set()
    nfn = mod.Func(func.name, func.param, func.rety)
    brmap = {}
    for bb in func.bb:
        #if a is b's only succ, b is a's only pred
        #append a to b
        #we need to rebuild the fallthrough chain
        if bb.name in removed:
            continue
        nxbb = mod.BB(bb.name)
        nxbb += bb.phis
        nxbb += bb.ins
        now = bb
        while not now.succs[1]:
            succ, _ = now.succs
            if not succ:
                break
            succ = func.bbmap[succ]
            if len(succ.preds) != 1 or succ == func.bb[0]:
                #bb[0] has an implicit predecessor
                break
            assert not succ.phis
            logging.info("%s <-> %s is one to one, remove %s", succ.name, now.name, succ.name)
            nxbb += succ.ins
            removed |= {succ.name}
            now = succ
        if now != bb:
            brmap[now.name] = bb.name
        nxbb += [now.br]
        #assert bb.name in set(succ.preds)
        nfn += [nxbb]

    map_needed = set(brmap)
    for bb in nfn.bb:
        for i in bb.phis:
            ps = set(i.srcs)
            ps &= map_needed
            if ps:
                logging.info("Change %s to...", i)
                for p in ps:
                    v = i.srcs[p]
                    i.del_source(p)
                    i.set_source(brmap[p], v)
                logging.info("...%s", i)

    if not func.is_machine_ir:
        nfn.finish(fmap)
    else :
        nfn.machine_finish(fmap)
    logging.info(nfn)

    if not removed:
        logging.info("Block coalesce done, no changes")
    unset_log_phase()
    return (bool(removed), nfn)
def variable_rename(func, fmap):
    set_log_phase("rename"+func.name)
    logging.info(func)
    nfn = mod.Func(func.name, func.param, func.rety)
    changed = False
    for bb in func.bb:
        logging.info("======%s======", bb.name)
        nxbb = mod.BB(bb.name, bb)
        if not bb.In and not bb.phis:
            logging.info("%s has no phi, no in, continue", bb.name)
            nfn += [nxbb]
            continue
        nbb = mod.BB(bb.name)
        #add phi nodes
        varmap = {}
        if len(bb.preds) > 1:
            #create phi node to grab the replaced
            #variable from different preds
            logging.info("Generate additional phi")
            nphi = []
            for v in bb.In:
                assert v.is_var
                changed = True
                ni = IRI.Phi(str(v)+"."+bb.name)
                for p in bb.preds:
                    pp = func.bbmap[p]
                    if v in pp.In:
                        ni.set_source(p, str(v)+"."+p)
                    else :
                        ni.set_source(p, str(v))
                nphi.append(ni)
                varmap[v] = opr.Var(v.val+"."+bb.name)
            logging.info("Rewrite original phi")
            for i in bb.phis:
                logging.info("%s: %s", bb.name, i)
                ni = copy.copy(i)
                for srcbb, v in ni.srcs.items():
                    if v.is_imm:
                        continue
                    sbb = func.bbmap[srcbb]
                    assert v.is_var
                    if v in sbb.In:
                        changed = True
                        logging.info("%s in %s's In, change name to %s", v, srcbb, str(v)+"."+srcbb)
                        ni.set_source(srcbb, str(v)+"."+srcbb)
                    else :
                        logging.info("%s not in %s's In", v, srcbb)
                nphi.append(ni)
            nbb += nphi
        else :
            #only one pred, but now the in variables might have changed
            logging.info("Single pred, rewrite var name")
            pred, = bb.preds
            pred = func.bbmap[pred]
            varmap = {}
            for v in bb.In:
                assert v.is_var
                if v in pred.In:
                    varmap[v] = opr.Var(v.val+"."+pred.name)
                    logging.info("%s -> %s", v, varmap[v])
        if varmap:
            changed = True
        for i in bb.ins:
            ni = copy.copy(i)
            ni.allocate(varmap)
            nbb += [ni]
        passthrou = bb.In&bb.out
        if len(bb.preds) == 1 and passthrou:
            changed = True
            pred, = bb.preds
            pred = func.bbmap[pred]
            for v in passthrou:
                vname = str(v)
                if v in pred.In:
                    vname += "."+pred.name
                i = IRI.Rename(str(v)+"."+bb.name, vname)
                nbb += [i]
                varmap[v] = opr.Var(i.dst.val)
        if bb.br:
            nbr = copy.copy(bb.br)
            nbr.allocate(varmap)
            nbb += [nbr]
        nfn += [nbb]
    nfn.finish(fmap)
    logging.info(nfn)
    for bb in nfn.bb:
        assert not bb.In or len(bb.preds) == 1, "%s %s %s" % (_str_set(bb.In), _str_set(bb.preds), bb)
        assert not (bb.In&bb.out), "%s: %s" %(bb.name, bb.In&bb.out)
    unset_log_phase()
    return (changed, nfn)
