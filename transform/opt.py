import IR.instruction as IRI
import IR.operand as opr
import IR.mod as mod
import IR.cmp as cmp
from IR import dfa
from utils import DisjointSet, _str_dict, _str_set
import copy
import logging
from . import set_log_phase, unset_log_phase
from .loop import get_loops
def phi_is_copy(ins, d, bbmap):
    var = None
    for k, v in ins.srcs.items():
        if not v.is_var:
            return None
        vv = v
        if v in d[bbmap[k]]:
            vv = d[bbmap[k]][v]
        if var is None:
            var = vv
            continue
        if not var == vv:
            return None
    return var

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
def _phi_varmap(i, varmap):
    ni = copy.copy(i)
    for k, v in i.srcs.items():
        if v in varmap:
            ni.srcs[k] = varmap[v]
    return ni

def copy_transfer(bb, d):
    bbmap = {}
    new_d = {}
    for p in bb.preds:
        bbmap[p.name] = p
        for v in d[p]:
            if v in new_d:
                assert d[p][v] == new_d[v]
            else :
                new_d[v] = d[p][v]

    for i in bb.phis:
        v = phi_is_copy(i, d, bbmap)
        if v is not None:
            new_d[i.dst] = v
    for ins in bb.ins:
        src = is_copy(ins)
        if src is None:
            continue
        osrc = src
        if src in new_d:
            src = new_d[src]
        logging.info("!!!!:%s\n    set %s->%s(%s)", ins, d, src, osrc)
        new_d[ins.dst] = src
    if new_d != d[bb]:
        d[bb] = new_d
        return True
    return False

def copy_propagation(fn, fmap):
    #first, get where is every variable defined
    set_log_phase("copy"+fn.name)
    logging.info("%s", fn)
    varmap = {}
    dfa.dfa_run(fn, copy_transfer, varmap, {}, False)
    logging.info(_str_dict(varmap))

    changed = False
    nfn = mod.Func(fn.name, fn.param, fn.rety)
    for bb in fn.bb:
        if varmap[bb]:
            changed = True
        else :
            nxbb = mod.BB(bb.name, bb)
            nfn += [nxbb]
            continue

        vm = varmap[bb]
        nbb = mod.BB(bb.name)
        nbb += [_phi_varmap(i, vm) for i in bb.phis]

        for ins in bb.ins+[bb.br]:
            ni = copy.copy(ins)
            ni.allocate(vm, False) #don't change dst
            nbb += [ni]
        nfn += [nbb]
    nfn.finish(fmap)
    unset_log_phase()
    return (changed, nfn)

def eval_const(i, value):
    if isinstance(i, IRI.Load):
        if i.m.is_imm:
            logging.info("%s is a const because it loads a const %d", i.dst, i.m.val)
            value[i.dst] = i.m.val
            return value[i.dst]
        return None

    if isinstance(i, IRI.Phi):
        val = None
        for k, v in i.srcs.items():
            nv = None
            if v not in value:
                if not v.is_imm:
                    return None
                nv = v.val
            else :
                nv = value[v]

            if val is None:
                val = nv
                continue
            if val != nv:
                return None
        value[i.dst] = val
        return val

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
    for i in bb.phis+bb.ins:
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
        nbb = mod.BB(bb.name)
        val = {}
        for v in const[bb]:
            val[v] = opr.Imm(const[bb][v])
        allv = set(val)
        logging.info("Value in %s, %s", bb.name, _str_dict(val))
        for i in bb.phis:
            if i.dst not in allv:
                for k, v in i.srcs.items():
                    if v in val:
                        changed = True
                        i.srcs[k] = val[v]
                print(i)
                nbb += [i]
        for i in bb.phis:
            if i.dst in allv:
                nbb += [IRI.Load(i.dst, val[i.dst])]
        for i in bb.ins+[bb.br]:
            if isinstance(i, IRI.Store) and i.dst.is_mem:
                nbb += [i]
                continue
            if i.get_dfn() and i.dst in allv:
                nbb += [IRI.Load(i.dst, val[i.dst].val)]
                continue
            u = i.get_used()
            if u&allv:
                changed = True
                i.allocate(val, False)
            nbb += [i]
        nfn += [nbb]
    nfn.finish(fmap)
    unset_log_phase()
    return (changed, nfn)

def cse_transfer(bb, parent, d):
    logging.info(bb.name)
    nfn = d[bb]
    assert isinstance(nfn, mod.Func), "BB called again ??? %s, p: %s" % (bb.name, parent.name)
    changed = False
    in_expr = {}
    varmap = {}
    sub_map = {}
    if parent:
        in_expr, pvarmap = d[parent]
        for sub in in_expr:
            sub_map[sub] = in_expr[sub]
        logging.info(_str_dict(sub_map))
        for v in pvarmap:
            varmap[v] = pvarmap[v]

    vmset = set(varmap)
    nbb = mod.BB(bb.name)
    nbb += bb.phis
    for i in bb.ins+[bb.br]:
        ni = copy.copy(i)
        if i.get_used()&vmset:
            print(i)
            print(_str_dict(varmap))
            changed = True
        ni.allocate(varmap)
        nbb += [ni]
        sub = cmp.SubExpr(ni)
        if not sub.eliminatable:
            continue
        if sub in sub_map:
            logging.info("%s, %s: %s", ni.dst, sub_map[sub], sub)
            varmap[ni.dst] = sub_map[sub]
            vmset |= {ni.dst}
            continue
        else :
            dst = copy.copy(i.dst)
            dst.dst = False
            logging.info("WTF %s", _str_dict(sub_map))
            sub_map[sub] = dst
            logging.info("xx %s->%s",ni.dst,sub)
    d[bb] = (sub_map, varmap)
    nfn += [nbb]
    return changed

def cse(fn, fmap):
    set_log_phase("cse"+fn.name)
    logging.info(fn)
    nfn = mod.Func(fn.name, fn.param, fn.rety)
    d = {}
    changed = dfa.walk_dominator_tree(fn, cse_transfer, d, nfn)
    if changed:
        #rewrite all phis
        nvarmap = {}
        for bb in d:
            _, nvarmap[bb.name] = d[bb]
        for bb in nfn.bb:
            for i in bb.phis:
                for k, v in i.srcs.items():
                    if v in nvarmap[k]:
                        i.srcs[k] = nvarmap[k][v]

    nfn.finish(fmap)
    unset_log_phase()
    return (changed, nfn)

def loop_motion(loop):
    use_of = {}
    dfn_ins = {}
    queue = set()
    print(loop)
    for bb in loop:
        for ins in bb.phis+bb.ins:
            logging.info(ins)
            ds = ins.get_dfn()
            if not ds:
                continue
            dfn_ins[ins.dst] = ins
            if type(ins) in (IRI.Phi, IRI.Invoke):
                logging.info("%s is not invariant because of %s", ins.dst, ins)
                queue |= {ins.dst}
                continue
            if isinstance(ins, IRI.Load) and ins.m.is_mem:
                logging.info("%s is not invariant because of %s", ins.dst, ins)
                queue |= {ins.dst}
                continue
            if type(ins) not in {IRI.Arithm, IRI.Cmp, IRI.GetAddrOf}:
                continue
            for u in ins.get_used():
                if u not in use_of:
                    use_of[u] = set()
                use_of[u] |= {ins.dst}
    loop_invariant = set(dfn_ins)-queue
    prehead = []
    while queue:
        v = queue.pop()
        logging.info("xxcxcxc %s", v)
        if v not in use_of:
            continue
        logging.info("%s is not invariant because of %s", _str_set(use_of[v]), v)
        loop_invariant -= use_of[v]
        queue |= use_of[v]

    if not loop_invariant:
        return []

    logging.info("Moving: ")
    for v in loop_invariant:
        logging.info("\t%s", dfn_ins[v])
    pending = set(dfn_ins)
    queue = set([v for v in loop_invariant if not dfn_ins[v].get_used()&pending])
    assert queue
    while queue:
        v = queue.pop()
        prehead.append(dfn_ins[v])
        pending -= {v}
        if v not in use_of:
            continue
        for v2 in use_of[v]:
            if not dfn_ins[v2].get_used()&pending and v2 in pending:
                queue |= {v2}

    return prehead

def loop_motion_all(fn, fmap):
    set_log_phase("loop"+fn.name)
    logging.info(fn)
    loop = get_loops(fn)
    prehead = {}
    moved = set()
    moved_head = set()
    for l in loop:
        prehead[l] = loop_motion(loop[l])
        if prehead[l]:
            moved_head |= {l.name}
        for i in prehead[l]:
            moved |= {i.dst}

    nfn = mod.Func(fn.name, fn.param, fn.rety)
    nbbmap = {}
    for bb in fn.bb:
        nbb = mod.BB(bb.name)
        if bb in prehead and prehead[bb]:
            loop_entries = set(bb.preds)-set(loop[bb])
            loop_entry_names = set([bb.name for bb in loop_entries])
            pnbb = mod.BB(bb.name+"_prehead")
            if len(loop_entries) > 1:
                for i in bb.phis:
                    #rewrite phi branch from any entry to from prehead
                    ni = IRI.Phi("%"+i.dst.val)
                    pni = IRI.Phi("%"+i.dst.val+".prehead")
                    for k in set(i.srcs):
                        if k in loop_entry_names:
                            pni.set_source(k, i.srcs[k])
                        else :
                            ni.set_source(k, i.srcs[k])
                    ni.set_source(pnbb.name, "%"+i.dst.val+".prehead")
                    nbb += [ni]
                    pnbb += [pni]
            else :
                e, = loop_entries
                for i in bb.phis:
                    ni = IRI.Phi("%"+i.dst.val)
                    for k in set(i.srcs):
                        if k != e.name:
                            ni.set_source(k, i.srcs[k])
                    ni.set_source(pnbb.name, i.srcs[e.name])
                    nbb += [ni]

            #in case of nested loops, some instruction might already
            #be moved out of upper loops. To do that, the upper loop
            #must dominate that instruction. And we know this loop's
            #head dominate all its instruction as well, therefore the
            #outer loop must dominate this loop head. So we just check
            #anything moved by its dominators.
            prehead_moved = set()
            for abb in bb.avail:
                if abb not in prehead:
                    continue
                for i in prehead[abb]:
                    prehead_moved |= {i.dst}

            pnbb += [i for i in prehead[bb] if i.dst not in prehead_moved]
            pnbb += [IRI.Br(0, None, bb.name, None, c="Prehead to real BB")]
            nfn += [pnbb]
        else :
            nbb += bb.phis
        for ins in bb.ins:
            if not ins.get_dfn or ins.dst not in moved:
                nbb += [ins]
        nbb += [bb.br]
        nbbmap[nbb.name] = nbb
        nfn += [nbb]

    #change all branch target name
    for bb in fn.bb:
        if bb in prehead and prehead[bb]:
            loop_entries = set(bb.preds)-set(loop[bb])
            for e in loop_entries:
                ebb = nbbmap[e.name]
                print(ebb.br)
                if ebb.br.tgt[0] == bb.name:
                    ebb.br.tgt[0] = bb.name+"_prehead"
                else :
                    assert ebb.br.tgt[1] == bb.name
                    ebb.br.tgt[1] = bb.name+"_prehead"
                print(ebb.br)

    nfn.finish(fmap)
    unset_log_phase()
    return (bool(moved), nfn)


