from . import set_log_phase, unset_log_phase
import IR.instruction as IR
import IR.operand as IRO
import IR.mod as mod
import IR.machine as machine
from storage_models import Registers, Memory
from .machine import callee_saved
from .utils import arg_passing
from collections import deque
import logging
from utils import _str_dict, _str_set, _dict_print, _set_print
import copy
def allocate_bb(bb, allocated):
    #allocate for phi
    ret = {}
    M = Memory()
    R = Registers(M)
    prmap = {}
    logging.info(">>>>>>>>>>>>>>%s<<<<<<<<<<<<<<<<<", bb.name)
    if bb.entry is not None:
        for n, v in enumerate(bb.entry[:4]):
            reg = IRO.Register("a%d" % n)
            R.reserve(v, reg)
            ret[v] = deque([reg])
        top = len(bb.entry)
        for n, v in enumerate(bb.entry[4:]):
            m = IRO.Cell((top-n)*4)
            R.reserve(v, m)
            ret[v] = deque([m])
    elif len(bb.preds) == 1:
        assert not bb.phis
        pred, = bb.preds
        for v in bb.In:
            assert v in pred.out_reg, str(bb)+str(pred)
            ret[v] = deque([pred.out_reg[v]])
            R.reserve(v, pred.out_reg[v])
        logging.info("On block entry"+_str_dict(R.vrmap))
    else :
        M2 = Memory()
        R2 = Registers()
        for i in bb.phis:
            for pbb, v in i.srcs.items():
                if pbb not in allocated:
                    continue
                if not v.is_var:
                    continue
                pbb = allocated[pbb]
                assert v in pbb.out_reg, "%s %s %s %s" % (v, pbb.name, bb.name, _str_dict(pbb.out_reg))
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
            for pbb, v in i.srcs.items():
                if pbb not in allocated:
                    #the pbb is not allocated yet
                    continue
                if not v.is_var:
                    continue
                pbb = allocated[pbb]
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
            logging.info("Phi allocation: %s -> %s", reg, i.dst)
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
        if isinstance(i, IR.Rename):
            #rename instruction, simply change the mapping
            assert {i.src} == i.last_use #make sure the renamed variable is not used afterwards
            logging.info("Handling rename %s", i)
            if i.src in R.M:
                _, s = R.M.get(i.src)
            else :
                assert i.src in R
                s = R.get(i.src)
            R.drop_both(i.src)
            R.reserve(i.dst, s)
            ret[i.dst] = deque([])
            continue

        if isinstance(i, IR.Invoke):
            #store every variable still alive
            alive_v = set(R.vrmap)-i.last_use
            for v in alive_v:
                if R.vrmap[v] in callee_saved:
                    continue
                R.drop(v)
                m = R.M.get(v)
                logging.info("Saving %s to %s for invoke", v, m[1])
                ret[v].append(m)

        ds = i.get_dfn()
        logging.debug(ds)
        if not isinstance(i, IR.Invoke):
            u = i.get_used()
        else :
            u = set() #don't promote invoke arguments, will be dealt with later
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
            if v in R:
                dreg = R.get(v)
                R.drop_both(v)
            else :
                assert isinstance(i, IR.Invoke), v
        logging.info("%s: Last use: %s ", i, _str_set(i.last_use))
        if not ds:
            continue
        d, = ds
        #if len(i.last_use) == 1:
            #reuse the operand register
        #    R.reserve(d, dreg)
        #    ret[d] = deque([dreg])
        #    logging.info("Reuse %s for %s", dreg, d)
        #else :
        #just get new reg, reuse will be handled by storage model
        reg, s, sm = R.get_may_spill(d)
        ret[d] = deque([reg])
        if s:
            ret[s].append(sm)
    bb.assign_out_reg(R)
    logging.info("OUT REG:" + _str_dict(bb.out_reg))
    allocated[bb.name] = bb
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
        logging.info("Store %s(%s) -> %s, for %s", oldv, R.vrmap[oldv], m, v)
        assert m, v
        assert m.is_mem
        if not e:
            ret += [IR.Store(m, r, c="Demoting "+str(oldv))]
        R.demote(oldv, m)
    if v in R.M:
        m = R.M.vmmap[v]
        ret += [IR.Load(r, m, c="Promoting "+str(v))]
        logging.info("Load %s(%s) -> %s", v, m, r)
    R.reserve(v, r)
    _dict_print(R.vrmap)
    return ret


def allocate(func, fmap):
    set_log_phase("allocate"+func.name)
    logging.info(func)
    unallocated_pred = {}
    todo = set()
    mentry = set()
    allocation = {}
    allocated = {}
    prmaps = {}
    for bb in func.bb:
        if len(bb.preds) > 1:
            mentry |= {bb}
        todo |= {bb}
        unallocated_pred[bb] = len(bb.preds)

    queue = set([bb for bb in todo if unallocated_pred[bb] == 0])
    assert queue
    while todo:
        h = queue.pop()
        todo -= {h}
        mentry -= {h}
        #allocate bb
        allocation[h], prmaps[h] = allocate_bb(h, allocated)
        for nbb in h.succs:
            logging.info("%s-=1", nbb.name)
            unallocated_pred[nbb] -= 1
            if unallocated_pred[nbb] <= 0 and nbb in todo:
                queue |= {nbb}
        if not queue and todo:
            #queue empty, find the bb with the least unallocated pred
            candidate = min(mentry, key=unallocated_pred.get)
            logging.info("%s!_!->%s", candidate.name, unallocated_pred[candidate])
            queue = {candidate}

    for bb in allocation:
        logging.info("<=====%s=====>", bb.name)
        res = ""
        for v in allocation[bb]:
            res += ("%s: " % v)
            for reg in allocation[bb][v]:
                if isinstance(reg, tuple):
                    res += ("(%s, %s), " % reg)
                else :
                    res += ("%s, " % reg)
        logging.info(res)


    nfn = mod.Func(func.name, func.param, func.rety)
    for bb in func.bb:
        #generate new func with registers
        #phi nodes is generated by its predecessors
        logging.info("!!!!!!!!%s!!!!!!!!", bb.name)
        R = Registers(Memory())
        pred = None
        nbb = mod.BB(bb.name)
        bballoc = allocation[bb]

        In = bb.In
        if bb.entry:
            In = In|set(bb.entry)
        for v in In:
            reg = bballoc[v].popleft()
            R.reserve(v, reg)

        for i in bb.phis:
            v = i.dst
            reg = bballoc[v].popleft()
            R.reserve(v, reg)
        for i in bb.ins+[bb.br]:
            logging.info("Allocating for %s", i)
            if isinstance(i, IR.Rename):
                logging.info("Update mapping for %s", i)
                if i.src in R.M:
                    _, s = R.M.get(i.src)
                else :
                    assert i.src in R
                    s = R.get(i.src)
                R.drop_both(i.src)
                logging.info("%s->%s", i.dst, s)
                R.reserve(i.dst, s)
                continue
            u = i.get_used()
            if isinstance(i, IR.Invoke):
                alive_v = set(R.vrmap)-i.last_use
                u = set()
                for v in alive_v:
                    if R.vrmap[v] in callee_saved:
                        logging.info("Don't need to save %s(%s)", v, R.vrmap[v])
                        continue
                    assert v in allocation[bb], v
                    e, m = allocation[bb][v].popleft()
                    if not e:
                        R.M.reserve(v, m)
                        nbb += [IR.Store(m, R.get(v), c="Saving %s before invoke" % v)]
                    #drop all variables
                logging.info("!@#$"+_str_dict(R.vrmap))
                arg_passing(nbb, i.args, R)
                for v in alive_v:
                    if R.vrmap[v] in callee_saved:
                        continue
                    R.drop(v)
            ni = copy.copy(i)
            logging.info("Used set: %s", _str_set(u))
            vrmap2 = {}
            for v in u:
                nbb += promote_replay(v, R, allocation[bb])
                vrmap2[v] = R.vrmap[v] #save the allocation
            for v in i.last_use:
                assert v not in allocation or not allocation[v]
                logging.info("Last use: %s", v)
                R.drop_both(v)
            ds = i.get_dfn()
            d = None
            if ds:
                d, = ds
                nbb += promote_replay(d, R, allocation[bb])
            tmpvrmap = copy.copy(R.vrmap)
            for v in vrmap2:
                tmpvrmap[v] = vrmap2[v]
            ni.allocate(tmpvrmap)
            if ni.is_br:
                #if the branch instruction has a target
                #change the target to point to the phi block
                ni.tgt = list(ni.tgt) #copy the target list
                for i in range(0, 2):
                    if ni.tgt[i]:
                        ni.tgt[i] = bb.name+"_"+ni.tgt[i]
            nbb += [ni]
        nfn += [nbb]

        if not bb.succs:
            continue
        assert len(bb.succs) <= 2
        for succ in bb.succs:
            if not succ:
                continue
            nbb = gen_phi_block(bb, succ, prmaps[succ])
            #fallthrough should be put right after
            nfn += [nbb]
        logging.info(bb.name)
    nfn.machine_finish(fmap)
    logging.info(nfn)
    unset_log_phase()
    return (True, nfn)

def gen_phi_block(bb, sbb, prmap):
    logging.info("Gen Phi block, edge %s -> %s", bb.name, sbb.name)
    nbb = mod.BB(bb.name+"_"+sbb.name)
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
            logging.info("Invalid case 1, %s has no reg, and %s's dst is %s", src, dst, dreg)
            return False
        #does dreg conflict with anything?
        if dreg in dsmap:
            logging.info("%s's dst %s is conflict with %s", dst, dreg, dsmap[dreg])
            return False
        return True

    def do_move(src, dst):
        nonlocal src_reg, src_mem, src_rcv, prmap, dsmap
        nonlocal todo
        dreg = prmap[dst]
        assert dreg not in dsmap
        #first try register
        sreg = src_reg[src]
        smem = src_mem[src]
        ret = []
        if dreg.is_mem:
            #writing to memory
            #must be from a register
            assert sreg
            #use this memory cell instead of the original
            #memory cell. Because a phi memory cell is guaranteed to not
            #have conflicts
            if smem in dsmap:
                del dsmap[smem]
            src_mem[src] = dreg
            ret = [IR.Store(dreg, sreg, c=("%s->%s" % (src, dst)))]
        else :
            #move/load into register
            #prefer phi register over original src register
            if sreg in dsmap:
                del dsmap[sreg]
            src_reg[src] = dreg
            if sreg:
                ret = [IR.Arithm('+', dreg, sreg, 0)]
            elif smem:
                ret = [IR.Load(dreg, smem, c=("%s->%s" % (src, dst)))]
            else :
                #imm
                ret = [IR.Load(dreg, src, c=str(dst))]
        #one phi done, remove from src_rcv
        src_rcv[src] -= {dst}
        if not src_rcv[src]:
            #we no longer need this src
            #so remove it from conflicts
            if sreg in dsmap:
                del dsmap[sreg]
            if smem in dsmap:
                del dsmap[smem]
            todo -= {src}
        return ret
    #do_move end

    #preprocessing, filling in the needed maps
    for i in sbb.phis:
        dst = i.dst
        dreg = prmap[dst]
        logging.debug("PHI dst %s: %s", dst, dreg)
        src = i.srcs[bb.name]
        if src not in src_rcv:
            src_rcv[src] = {dst}
        else :
            src_rcv[src] |= {dst}
        if dreg.is_mem:
            a_mem -= {dreg.off//4}
        if src.is_imm:
            src_mem[src] = src_reg[src] = None
            continue
        sreg = bb.out_reg[src]
        dsmap[sreg] = src
        if sreg.is_mem:
            src_mem[src] = sreg
            src_reg[src] = None
            a_mem -= {sreg.off//4}
        elif sreg.is_reg :
            src_mem[src] = None
            src_reg[src] = sreg
        if sreg == dreg:
            del dsmap[sreg]
            src_rcv[src] -= {dst}
            continue
    logging.info("Memory not used by any dst or src: %s", a_mem)

    #calculate free registers
    phiregs = set([prmap[i.dst] for i in sbb.phis if prmap[i.dst].is_reg])
    nophiregs = set(machine.all_reg)-phiregs
    todo = set([x for x in src_rcv if src_rcv[x]])

    #step 1
    s1ins = []
    #Real work is done here
    while todo:
        #First step, we only care register dsts
        #we do memory dsts when possible, but we not necessarily finish all of them
        pairs = [1]
        while bool(pairs):
            pairs = [(src, dst) for src in todo for dst in src_rcv[src] if valid_move(src, dst)]
            for src, dst in pairs:
                logging.info("do_move(%s, %s)", src,dst)
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
                mcell = IRO.Cell(a_mem.pop()*4)
                src_mem[src] = mcell
                src_reg[src] = None
                s1ins.append(IR.Store(mcell, creg, c=str(src)))
                logging.info("Resolving conflict by %s(%s)->%s", src, creg, mcell)
            else :
                #otherwise move to the free reg
                reg = avail_reg
                src_reg[src] = reg
                dsmap[reg] = src
                s1ins.append(IR.Arithm('+', reg, creg, 0))
                logging.info("Resolving conflict by %s(%s)->%s", src, creg, reg)
        else :
            #there's no register in dsmap, and there're no possible moves
            #which means all remaining dsts are memory
            break
    #while todo end

    end = IR.Br(0, None, sbb.name, None)
    if not todo:
        nbb += s1ins
        nbb += [end]
        return nbb

    #step 2
    s2ins = []
    #when we reach this point, all dsts are memory
    #obviously, the only thing preventing us from doing work
    #is conflicts

    #we might need a temporary register

    tmpreg = IR.Register("v0")
    logging.info("First phase done")
    while todo:
        #pick any src, load it, do all the valid moves, store it somewhere else
        #first see if we can find any src of whom all moves are valid
        to_promote = None
        for src in todo:
            flag = True
            assert src_rcv[src], src
            for dst in src_rcv[src]:
                dmem = prmap[dst]
                if dmem in dsmap:
                    logging.debug("%s dst %s %s conflict with %s" % (src, dst, dmem, dsmap[dmem]))
                    logging.debug(_str_set(todo))

                    flag = False
                    break
            if flag:
                to_promote = src
                break
        #otherwise we choose any one
        if not to_promote:
            for src in todo:
                if src_mem[src] in dsmap:
                    to_promote = src
                    break
        assert to_promote
        _set_print(src_rcv[to_promote])
        pmem = src_mem[to_promote]
        if not pmem:
            pmem = to_promote #imm
        assert pmem, to_promote
        s2ins.append(IR.Load(tmpreg, pmem, c="Promoting "+str(to_promote)))
        logging.info("promoting %s->%s to resolve conflicts", to_promote, tmpreg)
        done = set()
        for dst in src_rcv[to_promote]:
            dmem = prmap[dst]
            if dmem in dsmap:
                continue
            logging.info("Storing %s(%s)->%s", tmpreg, to_promote, dmem)
            s2ins.append(IR.Store(dmem, tmpreg, c=str(to_promote)+"->"+str(dst)))
            done |= {dst}
        src_rcv[to_promote] -= done
        if pmem in dsmap:
            del dsmap[pmem]
        if not src_rcv[to_promote]:
            #this to_promote is selected in first step
            #so no need to store it again
            logging.info("%s is done", to_promote)
            todo -= {to_promote}
        else :
            #this to_promote is in dsmap
            #so store it to a new place to resolve conflict
            mcell = IRO.Cell(a_mem.pop()*4)
            src_mem[to_promote] = mcell
            logging.info("%s still have left overs, storing to %s", to_promote, mcell)
            s2ins.append(IR.Store(mcell, tmpreg, c=str(to_promote)))
        pairs = [1]
        while bool(pairs):
            pairs = []
            for src in todo:
                if not src_reg[src]:
                    continue
                for dst in src_rcv[src]:
                    if prmap[dst] not in dsmap:
                        logging.info("New possible move %s(%s)->%s(%s)", src, src_reg[src], dst, prmap[dst])
                        pairs.append((src, dst))
            for src, dst in pairs:
                logging.info("reg to mem(%s, %s)", src,dst)
                s2ins.append(IR.Store(prmap[dst], src_reg[src], c=("%s->%s" % (src, dst))))
                src_rcv[src] -= {dst}
                if not src_rcv[src]:
                    todo -= {src}
    nbb += s1ins
    nbb += s2ins
    nbb += [end]
    return nbb
