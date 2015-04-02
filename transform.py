from IR import IR, BB, Arithm, Phi, Var, Cell, IInpt, IPrnt, Load, Store, Br, Register, all_reg
from collections import deque
from utils import _set_print, _dict_print, _str_dict, link, get_father
from storage_models import Memory, Registers
import copy
import sys
import logging

myhdlr = logging.FileHandler(filename="nothing.log", mode = "w")
logger = logging.getLogger()
def _phi_get_used(i):
    u = set()
    for bb, v in i.srcs.items():
        if v.is_var:
            u |= {v}
    return u

def set_log_phase(n):
    global myhdlr
    myhdlr.close()
    myhdlr = logging.FileHandler(filename=n+".log", mode="w")
    logger.addHandler(myhdlr)

def unset_log_phase():
    global myhdlr
    logger.removeHandler(myhdlr)

def prune_unused(ir):
    set_log_phase("prune")
    logging.info(ir)
    dfn_ins = {}
    used = set()
    queue = set()
    #instructions doesn't produce a result is a *real* use of its operands
    for bb in ir.bb:
        for i in bb.phis+bb.ins+[bb.br]:
            ds = i.get_dfn()
            if not ds:
                u = i.get_used()
                queue |= u
                used |= u
            if ds:
                d, = ds
                dfn_ins[d] = i
    while queue:
        d = queue.pop()
        i = dfn_ins[d]
        if i.is_phi:
            u = _phi_get_used(i)
        else :
            u = i.get_used()
        queue |= (u-used)
        used |= u

    nir = IR()
    changed = False
    for bb in ir.bb:
        nbb = BB(bb.name)
        for i in bb.phis+bb.ins:
            ds = i.get_dfn()
            if not ds:
                nbb += [i]
                continue
            d, = ds
            if d not in used:
                logging.info("%s is not used" % d)
                changed = True
                if isinstance(i, IInpt):
                    nbb += [IInpt(None)]
                continue
            nbb += [i]
        nbb += [bb.br]
        nir += [nbb]
    nir.finish()
    unset_log_phase()
    return (changed, nir)

def jump_block_removal(ir):
    set_log_phase("jbr")
    logging.info(ir)
    jmap = {}
    changed = False
    for bb in ir.bb:
        jmap[bb.name] = bb.name
    for bb in ir.bb:
        assert not bb.phis, "Can't do jump block removal on bb with phi nodes"
        if bb.ins or bb.br.tgt[1]:
            continue
        if not bb.br.tgt[0]:
            continue
        changed = True
        logging.info("Link %s -> %s" % (bb.name, bb.br.tgt[0]))
        link(bb.br.tgt[0], bb.name, jmap)
    if not changed:
        unset_log_phase()
        return (False, ir)
    nir = IR()
    for bb in ir.bb:
        rdir = get_father(bb.name, jmap)
        if rdir != bb.name:
            continue
        nbb = BB(bb.name, bb)
        for x in range(0, 2):
            oldtgt = nbb.br.tgt[x]
            if not oldtgt:
                continue
            nbb.br.tgt[x] = get_father(oldtgt, jmap)
            logging.info("Redirect %s to %s" % (oldtgt, nbb.br.tgt[x]))
        nir += [nbb]
    nir.finish()
    unset_log_phase()
    return (True, nir)

def block_coalesce(ir):
    set_log_phase("bc")
    logging.info(ir)
    removed = set()
    nir = IR()
    for bb in ir.bb:
        #if a is b's only succ, b is a's only pred
        #append a to b
        #we need to rebuild the fallthrough chain
        if bb.name in removed:
            continue
        assert not bb.phis
        nxbb = BB(bb.name)
        nxbb += bb.ins
        now = bb
        while not now.succs[1]:
            succ, _ = now.succs
            if not succ:
                break
            succ = ir.bbmap[succ]
            assert not succ.phis
            if len(succ.preds) != 1:
                break
            logging.info("%s <-> %s is one to one, remove %s" % (succ.name, now.name, succ.name))
            nxbb += succ.ins
            removed |= {succ.name}
            now = succ
        nxbb += [now.br]
        #assert bb.name in set(succ.preds)
        nir += [nxbb]
    nir.finish()

    if not removed:
        logging.info("Block coalesce done, no changes")
    unset_log_phase()
    return (bool(removed), nir)
def chain_breaker(ir):
    set_log_phase("chain")
    logging.info(ir)
    nir = IR()
    changed = False
    for bb in ir.bb:
        logging.info("======%s======" % bb.name)
        nxbb = BB(bb.name, bb)
        if not bb.In and not bb.phis:
            logging.info("%s has no phi, no in, continue" % bb.name)
            nir += [nxbb]
            continue
        nbb = BB(bb.name)
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
                ni = Phi(str(v)+"."+bb.name)
                for p in bb.preds:
                    pp = ir.bbmap[p]
                    if v in pp.In:
                        ni.set_source(p, str(v)+"."+p)
                    else :
                        ni.set_source(p, str(v))
                nphi.append(ni)
                varmap[v] = Var(v.val+"."+bb.name)
            logging.info("Rewrite original phi")
            for i in bb.phis:
                logging.info("%s: %s" % (bb.name, i))
                ni = copy.copy(i)
                for srcbb, v in ni.srcs.items():
                    if v.is_imm:
                        continue
                    sbb = ir.bbmap[srcbb]
                    assert v.is_var
                    if v in sbb.In:
                        changed = True
                        logging.info("%s in %s's In, change name to %s" % (v, srcbb, str(v)+"."+srcbb))
                        ni.set_source(srcbb, str(v)+"."+srcbb)
                    else :
                        logging.info("%s not in %s's In" % (v, srcbb))
                nphi.append(ni)
            nbb += nphi
        else :
            #only one pred, but now the in variables might have changed
            logging.info("Single pred, rewrite var name")
            pred, = bb.preds
            pred = ir.bbmap[pred]
            varmap = {}
            for v in bb.In:
                assert v.is_var
                if v in pred.In:
                    varmap[v] = Var(v.val+"."+pred.name)
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
            pred = ir.bbmap[pred]
            for v in passthrou:
                vname = str(v)
                if v in pred.In:
                    vname += "."+pred.name
                nbb += [Arithm('+', str(v)+"."+bb.name, vname, 0)]
        if bb.br:
            nbr = copy.copy(bb.br)
            nbr.allocate(varmap)
            nbb += [nbr]
        nir += [nbb]
    nir.finish()
    logging.debug(nir)
    for bb in nir.bb:
        assert not bb.In or len(bb.preds) == 1
        assert not (bb.In&bb.out), "%s: %s" %(bb.name, bb.In&bb.out)
    unset_log_phase()
    return (changed, nir)

def allocate_bb(bb, bbmap):
    #allocate for phi
    ret = {}
    M = Memory()
    R = Registers(M)
    prmap = {}
    logging.info(">>>>>>>>>>>>>>%s<<<<<<<<<<<<<<<<<" % (bb.name))
    if len(bb.preds) == 1:
        assert not bb.phis
        only_pred, = bb.preds
        only_pred = bbmap[only_pred]
        for v in bb.In:
            assert v in only_pred.out_reg, str(bb)+str(only_pred)
            vreg = only_pred.out_reg[v]
            ret[v] = deque([])
            if vreg.is_reg:
                R.reserve(v, vreg)
            else :
                M.reserve(v, vreg)
    else :
        M2 = Memory()
        R2 = Registers()
        for i in bb.phis:
            for phibb, v in i.srcs.items():
                pbb = bbmap[phibb]
                if v not in pbb.out_reg:
                    continue
                sreg = pbb.out_reg[v]
                if not sreg.is_reg:
                    if sreg not in M2:
                        M2.reserve(v, sreg)
                else :
                    if sreg not in R2:
                        R2.reserve(v, sreg)
        #register preference:
        #same reg as src > same memory as src > reg different from src > other memory
        for i in bb.phis:
            logging.info(M)
            reg = None #reg in srcs not used
            for phibb, v in i.srcs.items():
                pbb = bbmap[phibb]
                if v not in pbb.out_reg:
                    #the pbb is not allocated yet
                    continue
                srcreg = pbb.out_reg[v]
                if srcreg.is_reg:
                    if srcreg not in R:
                        R.reserve(i.dst, srcreg)
                        reg = srcreg
                        break
                else :
                    if srcreg not in M:
                        #this memory is not used by any phi yet
                        M.reserve(i.dst, srcreg)
                        reg = srcreg
                        break
            if not reg:
                #try to avoid registers used by other src
                #(so other phis will be able to use them)
                reg = R2.get(i.dst)
                if reg:
                    R.reserve(i.dst, reg)
            if not reg:
                reg = R.get(i.dst)
            if not reg:
                #avoid using same memory as src so
                #other phis will be able to use them
                #     v----- change to M to test phi block gen
                e, reg = M2.get(i.dst)
                assert not e
                M.reserve(i.dst, reg)
            logging.info("Phi allocation: %s -> %s" % (reg, i.dst))
            ret[i.dst] = deque([reg])
            prmap[i.dst] = reg
    #phi allocation ends here
    logging.info(M)
    _dict_print(R.vrmap)
    _dict_print(M.vmmap)
    _set_print(bb.In)
    for i in bb.ins+[bb.br]:
        if i.is_phi:
            continue
        logging.debug(i)
        ds = i.get_dfn()
        logging.debug(ds)
        u = i.get_used()
        for v in u:
            if v in R:
                R.get(v) #get once to move reg to the end of spill list
                continue
            reg, s, sm = R.get_may_spill(v)
            ret[v].append(reg)
            if s:
                assert s in ret, s
                ret[s].append(sm)

        dreg = None
        for v in i.last_use:
            assert v in R
            dreg = R.get(v)
            R.drop_both(v)
        if not ds:
            continue
        d, = ds
        logging.info("%s: Last use: " % i)
        _set_print(i.last_use)
        if len(i.last_use) == 1:
            #reuse the operand register
            R.reserve(d, dreg)
            ret[d] = deque([dreg])
            logging.info("Reuse %s for %s" % (dreg, d))
        else :
            #more than one or none, reuse does not make sense
            reg, s, sm = R.get_may_spill(d)
            ret[d] = deque([reg])
            logging.info("xxx%s -> %s" % (reg, d))
            if s:
                ret[s].append(sm)
    bb.assign_out_reg(R)
    logging.info("OUT REG:" + _str_dict(bb.out_reg))
    return (ret, prmap)

def promote_replay(v, R, allocation):
    #promote v into reg, do store/load if necessary
    #but don't change vrmap besides for v
    if v in R:
        return []
    ret = []
    assert v in allocation, str(v)
    r = allocation[v].popleft()
    assert r.is_reg
    oldv = None
    m = None
    if r in R:
        oldv = R.rvmap[r]
        #empty allocation means it's not longer needed
        e, m = allocation[oldv].popleft()
        logging.info("Store %s(%s) -> %s, for %s" % (oldv, R.vrmap[oldv], m, v))
        assert m, v
        assert m.is_mem
        if not e:
            ret += [Store(m, r)]
        R.demote(oldv, m)
    if v in R.M:
        m = R.M.vmmap[v]
        ret += [Load(r, m)]
        logging.info("Load %s(%s) -> %s" % (v, m, r))
    R.reserve(v, r)
    _dict_print(R.vrmap)
    return ret

def allocate(ir):
    set_log_phase("allocate")
    logging.info(ir)
    unallocated_pred = {}
    todo = set()
    mentry = set()
    allocation = {}
    prmaps = {}
    for bb in ir.bb:
        if len(bb.preds) > 1:
            mentry |= {bb}
        todo |= {bb}
        unallocated_pred[bb] = len(bb.preds)

    queue = set([bb for bb in todo if unallocated_pred[bb] == 0])
    while todo:
        h = queue.pop()
        todo -= {h}
        mentry -= {h}
        #allocate bb
        allocation[h], prmaps[h] = allocate_bb(h, ir.bbmap)
        for nbb in h.succs:
            if not nbb:
                continue
            nbb = ir.bbmap[nbb]
            logging.info("%s-=1" % nbb.name)
            unallocated_pred[nbb] -= 1
            if unallocated_pred[nbb] <= 0 and nbb in todo:
                queue |= {nbb}
        if not queue and todo:
            #queue empty, find the bb with the least unallocated pred
            candidate = min(mentry, key=unallocated_pred.get)
            logging.info("%s!_!->%s" % (candidate.name, unallocated_pred[candidate]))
            queue = {candidate}

    for bb in allocation:
        logging.info("<=====%s=====>" % bb.name)
        res = ""
        for v in allocation[bb]:
            res += ("%s: " % v)
            for reg in allocation[bb][v]:
                if isinstance(reg, tuple):
                    res += ("(%s, %s), " % reg)
                else :
                    res += ("%s, " % reg)
        logging.info(res)


    nir = IR()
    for bb in ir.bb:
        #generate new ir with registers
        #phi nodes is generated by its predecessors
        logging.info("!!!!!!!!%s!!!!!!!!" % bb.name)
        R = Registers(Memory())
        pred = None
        nbb = BB(bb.name)
        bballoc = allocation[bb]
        if len(bb.preds) == 1:
            pred, = bb.preds
            pred = ir.bbmap[pred]
            for v in bb.In:
                R.reserve(v, pred.out_reg[v])
        else :
            for i in bb.phis:
                v = i.dst
                reg = bballoc[v].popleft()
                R.reserve(v, reg)
        for i in bb.ins+[bb.br]:
            ni = copy.copy(i)
            u = ni.get_used()
            for v in u:
                nbb += promote_replay(v, R, allocation[bb])
            vrmap2 = {}
            for v in i.last_use:
                assert v not in allocation or not allocation[v]
                logging.info("Last use: %s" % v)
                vrmap2[v] = R.vrmap[v] #save the allocation
                R.drop_both(v)
            ds = i.get_dfn()
            d, oldv, m = None, None, None
            if ds:
                d, = ds
                nbb += promote_replay(d, R, allocation[bb])
            for v in vrmap2:
                R.vrmap[v] = vrmap2[v]
            ni.allocate(R.vrmap)
            for v in vrmap2:
                del R.vrmap[v]
            if ni.is_br:
                #if the branch instruction has a target
                #change the target to point to the phi block
                ni.tgt = list(ni.tgt) #copy the target list
                for i in range(0, 2):
                    if ni.tgt[i]:
                        ni.tgt[i] = bb.name+"_"+ni.tgt[i]
            nbb += [ni]
        nir += [nbb]

        if not bb.succs:
            continue
        assert len(bb.succs) <= 2
        for succ in bb.succs:
            if not succ:
                continue
            sbb = ir.bbmap[succ]
            nbb = gen_phi_block(bb, sbb, prmaps[sbb])
            #fallthrough should be put right after
            nir += [nbb]
        logging.info(bb.name)
    nir.finish()
    unset_log_phase()
    return (True, nir)

def gen_phi_block(bb, sbb, prmap):
    logging.info("Gen Phi block, edge %s -> %s" % (bb.name, sbb.name))
    nbb = BB(bb.name+"_"+sbb.name)
    todo = set()
    src_reg = {} #any register holds src
    src_mem = {} #any memory cell holds src
    src_rcv = {} #all the phis for a src
    dsmap = {} #map from a conflict entry to the corresponding src
    a_mem = set(range(0, 4*len(sbb.phis))) #which memory cell is free? used for finding temp memory cell
    def valid_move(src, dst):
        nonlocal src_reg, src_mem, prmap, dsmap
        dreg = prmap[dst]
        if not src_reg[src] and dreg.is_mem:
            #memory to memory
            logging.info("Invalid case 1, %s has no reg, and %s's dst is %s" % (src, dst, dreg))
            return False
        #does dreg conflict with anything?
        if dreg.is_reg and dreg in dsmap:
            logging.info("%s's dst %s is conflict with %s" % (dst, dreg, dsmap[dreg]))
            return False
        if dreg.is_mem and dreg.val in dsmap:
            logging.info("%s's dst %s is conflict with %s" % (dst, dreg, dsmap[dreg.val]))
            return False
        return True

    def do_move(src, dst):
        nonlocal src_reg, src_mem, src_rcv, prmap, dsmap
        nonlocal todo
        dreg = prmap[dst]
        #first try register
        sreg = src_reg[src]
        smem = src_mem[src]
        ret = []
        if dreg.is_mem:
            #writing to memory
            #must be from a register
            assert sreg
            if dreg.val in dsmap:
                #we overwrite something
                src_mem[dsmap[dreg.val]] = None
                del dsmap[dreg.val]
            #use this memory cell instead of the original
            #memory cell. Because a phi memory cell is guaranteed to not
            #have conflicts
            if smem and smem.val in dsmap:
                del dsmap[smem.val]
            src_mem[src] = dreg
            ret = [Store(dreg, sreg)]
        else :
            #move/load into register
            if dreg in dsmap:
                #we are overwriting some src
                src_reg[dsmap[dreg]] = None
                del dsmap[dreg]
            #prefer phi register over original src register
            if sreg in dsmap:
                del dsmap[sreg]
            src_reg[src] = dreg
            if sreg:
                ret = [Arithm('+', dreg, sreg, 0)]
            else :
                ret = [Load(dreg, smem)]
        #one phi done, remove from src_rcv
        src_rcv[src] -= {dst}
        if not src_rcv[src]:
            #we no longer need this src
            #so remove it from conflicts
            if sreg in dsmap:
                del dsmap[sreg]
            if smem and smem.val in dsmap:
                del dsmap[smem.val]
            todo -= {src}
        return ret
    #do_move end

    nosrcreg = set(all_reg)
    #preprocessing, filling in the needed maps
    for i in sbb.phis:
        dst = i.dst
        dreg = prmap[dst]
        src = i.srcs[bb.name]
        if src.is_imm:
            continue
        sreg = bb.out_reg[src]
        if src not in src_rcv:
            src_rcv[src] = {dst}
        else :
            src_rcv[src] |= {dst}
        if sreg.is_mem:
            src_mem[src] = sreg
            src_reg[src] = None
            dsmap[sreg.val] = src
            a_mem -= {sreg.val}
        else :
            src_mem[src] = None
            src_reg[src] = sreg
            dsmap[sreg] = src
            nosrcreg -= {sreg}
        if dreg.is_mem:
            a_mem -= {dreg.val}
        if sreg == dreg:
            if dreg.is_mem:
                del dsmap[sreg.val]
            else :
                del dsmap[sreg]
            src_rcv[src] -= {dst}
            continue

    #calculate free registers
    phiregs = set([prmap[i.dst] for i in sbb.phis if prmap[i.dst].is_reg])
    nophiregs = set(all_reg)-phiregs
    todo = set([x for x in src_rcv if src_rcv[x]])

    #step 0
    #handle all imm srcs
    s0ins = []
    immmap = {}
    tmpreg = False
    for i in sbb.phis:
        src = i.srcs[bb.name]
        if not src.is_imm:
            continue
        if src.val not in immmap:
            immmap[src.val] = set()
        dreg = prmap[i.dst]
        if dreg.is_mem:
            tmpreg = True
        immmap[src.val] |= {i.dst.val}
    popcell = None
    if nosrcreg:
        tmpreg = next(iter(nosrcreg)) #we have a free reg, grab it any way
    elif tmpreg:
        popcell = Cell(next(iter(a_mem)))
        tmpreg = next(iter(all_reg))
        s0ins.append(Store(popcell, tmpreg))
    for val in immmap:
        reg_set = False
        for dst in immmap[val]:
            dreg = prmap[i.dst]
            if dreg.is_reg:
                s0ins.append(Load(dreg, val))
            else :
                if not reg_set:
                    s0ins.append(Load(tmpreg, val))
                    reg_set = True
                s0ins.append(Store(dreg, tmpreg))

    s0tmpreg = tmpreg

    #step 1
    #restore popcell used in step 0 first
    s1ins = []
    if popcell:
        s1ins.append(Load(tmpreg, popcell))
    #Real work is done here
    while todo:
        #First step, we only care register dsts
        #we do memory dsts when possible, but we not necessarily finish all of them
        pairs = [1]
        while bool(pairs):
            pairs = [(src, dst) for src in todo for dst in src_rcv[src] if valid_move(src, dst)]
            for src, dst in pairs:
                logging.info("do_move(%s, %s)" % (src,dst))
                s1ins += do_move(src, dst)
        #no action available, trying to improve the situation
        #we only care about making register dsts available
        #so only thing we do is storing srcs into memory

        #What we do is therefore:
        # 1) get any registers from dsmap.keys(), that conflicts with some phi
        # 2) store it or move it to another register

        creg = None
        for x in phiregs:
            if x in dsmap:
                creg = x
                break
        avail_reg = None
        for x in nophiregs:
            if x not in dsmap:
                avail_reg = x
                break
        if creg:
            src = dsmap[creg]
            del dsmap[creg]
            if not avail_reg:
                #no free reg, store to memory
                mcell = Cell(a_mem.pop())
                src_mem[src] = mcell
                src_reg[src] = None
                s1ins.append(Store(mcell, creg))
                logging.info("Resolving conflict by %s(%s)->%s" % (src, creg, mcell))
            else :
                #otherwise move to the free reg
                reg = avail_reg
                src_reg[src] = reg
                dsmap[reg] = src
                s1ins.append(Arithm('+', reg, creg, 0))
                logging.info("Resolving conflict by %s(%s)->%s" % (src, creg, reg))
        else :
            #there's no register in dsmap, and there're no possible moves
            #which means all remaining dsts are memory
            break
    #while todo end

    end = Br(0, None, sbb.name, None)
    if not todo:
        nbb += s0ins
        nbb += s1ins
        nbb += [end]
        return nbb

    #step 2
    s2ins = []
    #when we reach this point, all dsts are memory
    #obviously, the only thing preventing us from doing work
    #is conflicts

    #we might need a temporary register
    resolve_ins = s2ins
    popcell = None
    tmpreg = None
    if s0tmpreg:
        #tmpreg available during step 0 means we can use it and put all the
        #conflict resolution in step 2 into step 0
        logging.info("We have one tmpreg during step 0 (which is %s)" % tmpreg)
        tmpreg = s0tmpreg
        resolve_ins = s0ins
    else :
        avail_reg = None
        for x in nophiregs:
            if x not in dsmap:
                avail_reg = x
                break
        if not avail_reg:
            popcell = Cell(a_mem.pop())
            tmpreg = Register("t0")
            s2ins.append(Store(popcell, tmpreg))
        else :
            tmpreg = avail_reg

    logging.info("First phase done")
    while todo:
        #pick any src, load it, do all the valid moves, store it somewhere else
        #first see it we can find any src of whom all moves are valid
        to_promote = None
        for src in todo:
            flag = True
            assert src_rcv[src], src
            for dst in src_rcv[src]:
                dmem = prmap[dst]
                if dmem.val in dsmap:
                    flag = False
                    break
            if flag:
                to_promote = src
                break
        #otherwise we choose any one
        if not to_promote:
            for src in todo:
                if src_mem[src].val in dsmap:
                    to_promote = src
                    break
        assert to_promote
        logging.info("promoting %s to resolve conflicts" % to_promote)
        _set_print(src_rcv[to_promote])
        pmem = src_mem[to_promote]
        assert pmem, to_promote
        resolve_ins.append(Load(tmpreg, pmem))
        done = set()
        for dst in src_rcv[to_promote]:
            dmem = prmap[dst]
            if dmem.val in dsmap:
                continue
            resolve_ins.append(Store(dmem, tmpreg))
            done |= {dst}
        src_rcv[to_promote] -= done
        if pmem.val in dsmap:
            del dsmap[pmem.val]
        if not src_rcv[to_promote]:
            #this to_promote is selected in first step
            #so no need to store it again
            todo -= {to_promote}
        else :
            #this to_promote is in dsmap
            #so store it to a new place to resolve conflict
            mcell = Cell(a_mem.pop())
            src_mem[to_promote] = mcell
            resolve_ins.append(Store(mcell, tmpreg))
        pairs = [1]
        while bool(pairs):
            pairs = []
            for src in todo:
                if not src_reg[src]:
                    continue
                for dst in src_rcv[src]:
                    if prmap[dst].val not in dsmap:
                        pairs.append((src, dst))
            for src, dst in pairs:
                logging.info("reg to mem(%s, %s)" % (src,dst))
                s2ins.append(Store(prmap[dst], src_reg[src]))
                src_rcv[src] -= {dst}
                if not src_rcv[src]:
                    todo -= {src}
    if popcell:
        s2ins.append(Load(tmpreg, popcell))
    nbb += s0ins
    nbb += s1ins
    nbb += s2ins
    nbb += [end]
    return nbb
