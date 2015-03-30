from IR import IR, BB, Arithm, Phi, Var, Cell, IInpt, Load, Store, Br, Register, all_reg
from collections import deque
from utils import _set_print, _dict_print
from storage_models import Memory, Registers
import copy
def _phi_get_used(i):
    u = set()
    for bb, v in i.srcs.items():
        if v.is_var:
            u |= {v}
    return u

def prune_unused(ir):
    refcount = {}
    dfn_ins = {}
    queue = set()
    for bb in ir.bb:
        for i in bb.ins:
            if i.is_phi:
                u = _phi_get_used(i)
            else :
                u = i.get_used()
            ds = i.get_dfn()
            if ds:
                d, = ds
                dfn_ins[d] = i
            for v in u:
                if v not in refcount:
                    refcount[v] = 0
                refcount[v] += 1
            if not i.used:
                queue |= {i}
    if not queue:
        return (False, ir)
    for i in queue:
        print("Removing %s" % i)
    while queue:
        unused = queue.pop()
        if unused.is_phi:
            uu = _phi_get_used(unused)
        else :
            uu = unused.get_used()
        for v in uu:
            refcount[v] -= 1
            if refcount[v] <= 0:
                dfn_ins[v].mark_as_unused()
                queue |= {dfn_ins[v]}

    nir = IR()
    for bb in ir.bb:
        nbb = BB(bb.name)
        for i in bb.ins:
            if not i.is_br and not i.used:
                if isinstance(i, IInpt):
                    nbb += [IInpt(None)]
                continue
            nbb += [i]
        nir += [nbb]
    nir.finish()
    return (True, nir)

def empty_block_removal(ir):
    jmap = {}
    stack = []
    nir = IR()
    changed = False
    for bb in ir.bb:
        assert not bb.phi, "Can perform block removal when bb has phinodes"
        nxbb = BB(bb.name, bb.ins)
        if not bb.ins:
            #empty block
            stack.append(bb)
            changed = True
        else :
            while stack:
                ebb = stack.pop()
                jmap[ebb.name] = bb.name
    for bb in ir.bb:
        if not bb.ins:
            continue
        if not bb.br or bb.br.tgt not in jmap:
            nir += [nxbb]
            continue
        nbb = BB(bb.name)
        nbb += bb.nonbr_ins
        nbr = copy.copy(bb.br)
        nbr.tgt = jmap[nbr.tgt]
        nbb += [nbr]
        nir += [nbb]
    print(nir)
    nir.finish()
    return (changed, nir)

def block_coalesce(ir):
    removed = {}
    nir = IR()
    changed = True
    nextbb = {}
    nbbmap = {}
    prev = None
    for bb in ir.bb:
        if prev:
            if prev.fall_through:
                nextbb[prev.name] = bb
            else :
                nextbb[prev.name] = None
        prev = bb
    nextbb[prev.name] = None
    for bb in ir.bb:
        #if a is b's only succ, b is a's only pred
        #prepend b to a
        #we need to rebuild the fallthrough chain
        nxbb = BB(bb.name, bb.ins)
        if bb.name in removed:
            continue
        if len(bb.successors) != 1:
            nbbmap[nxbb.name] = nxbb
            continue
        succ, = bb.successors
        succ = ir.bbmap[succ]
        if len(succ.predecessors) > 1:
            nbbmap[nxbb.name] = nxbb
            continue
        assert bb.name in succ.predecessors
        if succ.phi:
            nbbmap[nxbb.name] = nxbb
            continue
        nbb = BB(bb.name)
        nbb += bb.nonbr_ins
        nbb += succ.ins
        nextbb[bb.name] = nextbb[succ.name]
        del nextbb[succ.name]
        removed |= {succ.name}
        changed = True

    print (nbbmap)
    now = ir.bb[0]
    nbbmap.pop(now.name)
    while nbbmap:
        nir += [now]
        now = nextbb[now.name]
        if not now:
            key = next(iter(nbbmap))
            now = nbbmap.pop(key)
        else :
            nbbmap.pop(now.name)
    nir += [now]
    nir.finish()

    return (changed, nir)
def chain_breaker(ir):
    nir = IR()
    changed = False
    for bb in ir.bb:
        print("======%s======" % bb.name)
        nxbb = BB(bb.name, bb.ins)
        if not bb.In and not bb.phi:
            print("No phi, no in, continue")
            nir += [nxbb]
            continue
        nbb = BB(bb.name)
        #add phi nodes
        varmap = {}
        if len(bb.predecessors) > 1:
            #create phi node to grab the replaced
            #variable from different preds
            print("Generate additional phi")
            for v in bb.In:
                assert v.is_var
                changed = True
                nphi = Phi(str(v)+"."+bb.name)
                for p in bb.predecessors:
                    pp = ir.bbmap[p]
                    if v in pp.In:
                        nphi.set_source(p, str(v)+"."+p)
                    else :
                        nphi.set_source(p, str(v))
                print(nphi)
                nbb += [nphi]
                varmap[v] = Var(v.val+"."+bb.name)
            print("Rewrite original phi")
            for phi in bb.phi:
                print("%s: %s" % (bb.name, phi))
                for srcbb, v in phi.srcs.items():
                    if v.is_imm:
                        continue
                    sbb = ir.bbmap[srcbb]
                    assert v.is_var
                    if v in sbb.In:
                        changed = True
                        print("%s in %s's In, change name to %s" % (v, srcbb, str(v)+"."+srcbb))
                        phi.set_source(srcbb, str(v)+"."+srcbb)
                    else :
                        print("%s not in %s's In" % (v, srcbb))
                print(phi)
        else :
            #only one pred, but now the in variables might have changed
            print("Single pred, rewrite var name")
            if not bb.predecessors:
                print(bb.In)
                print(bb.phi)
                print(not bb.In and not bb.phi)
            pred, = bb.predecessors
            pred = ir.bbmap[pred]
            varmap = {}
            for v in bb.In:
                assert v.is_var
                if v in pred.In:
                    varmap[v] = Var(v.val+"."+pred.name)
        if varmap:
            changed = True
        for i in bb.nonbr_ins:
            ni = copy.copy(i)
            ni.allocate(varmap)
            nbb += [ni]
        passthrou = bb.In&bb.out
        if len(bb.predecessors) == 1 and passthrou:
            changed = True
            pred, = bb.predecessors
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
    print(nir)
    for bb in nir.bb:
        assert not bb.In or len(bb.predecessors) == 1
        assert not (bb.In&bb.out), "%s: %s" %(bb.name, bb.In&bb.out)
    return (changed, nir)

def any_reg(avail_reg):
    'return any register, but prefer registers that are not being used'
    if avail_reg:
        return avail_reg.pop()
    return next(iter(all_reg))

def promote(v, avail_reg, vrmap, rvmap, ret, M):
    reg = any_reg(avail_reg)
    if v not in ret:
        ret[v] = deque([reg])
    else :
        ret[v].append(reg)
    if reg in rvmap:
        e, mcell = M.get(rvmap[reg])
        print("Demoted %s from %s to %s, %s" % (rvmap[reg], reg, mcell, e))
        vrmap[rvmap[reg]] = mcell
        ret[rvmap[reg]].append((e, mcell))
    oldreg = "(none)"
    if v in vrmap:
        oldreg = str(vrmap[v])
    rvmap[reg] = v
    vrmap[v] = reg
    print("Promoted %s from %s to %s" % (v, oldreg, reg))

def allocate_bb(bb, bbmap):
    #allocate for phi
    ret = {}
    avail_reg = set(all_reg)
    rvmap = {}
    vrmap = {}
    M = Memory()
    only_pred = None
    mem_phi = set()
    prmap = {}
    print(">>>>>>>>>>>>>>%s<<<<<<<<<<<<<<<<<" % (bb.name))
    if len(bb.predecessors)==1:
        assert not bb.phi
        only_pred, = bb.predecessors
        only_pred = bbmap[only_pred]
        for v in bb.In:
            #we assume chain_breaker has been run
            assert v in only_pred.out_reg
            vreg = only_pred.out_reg[v]
            vrmap[v] = vreg
            ret[v] = deque([])
            if vreg.is_reg:
                avail_reg -= {vreg}
                rvmap[vreg] = v
            else :
                M.reserve(v, vreg)
    else :
        M2 = Memory()
        mem = set()
        nosrcreg = set(all_reg)
        for phi in bb.phi:
            for phibb, v in phi.srcs.items():
                pbb = bbmap[phibb]
                if v not in pbb.out_reg:
                    continue
                sreg = pbb.out_reg[v]
                if not sreg.is_reg:
                    #we don't reserve this memory
                    #because our phi block generate can handle
                    #the case where src and dst has same memory cell
                    #is memory
                    if sreg not in M2:
                        M2.reserve(v, sreg)
                    continue
                nosrcreg -= {sreg}
        #register preference:
        #same reg as src > same memory as src > reg different from src > other memory
        for phi in bb.phi:
            print(M)
            reg = None #reg in srcs not used
            for phibb, v in phi.srcs.items():
                pbb = bbmap[phibb]
                if v not in pbb.out_reg:
                    #the pbb is not allocated yet
                    continue
                srcreg = pbb.out_reg[v]
                if srcreg.is_reg:
                    if srcreg not in rvmap:
                        avail_reg -= {srcreg}
                        reg = srcreg
                        break
                else :
                    if srcreg not in M:
                        #this memory is not used by any phi yet
                        M.reserve(phi.dst, srcreg)
                        reg = srcreg
                        break
            if not reg:
                #try to avoid registers used by other src
                #(so other phis will be able to use them)
                if nosrcreg:
                    reg = nosrcreg.pop()
                    avail_reg -= {reg}
                elif avail_reg:
                    reg = avail_reg.pop()
                else :
                    #avoid using same memory as src so
                    #other phis will be able to use them
                    #        v----- change to M to test phi block gen
                    _, reg = M.get(phi.dst)
            print("Phi allocation: %s -> %s" % (reg, phi.dst))
            ret[phi.dst] = deque([reg])
            if reg.is_reg:
                rvmap[reg] = phi.dst
            else :
                mem |= {phi.dst}
            vrmap[phi.dst] = reg
            prmap[phi.dst] = reg
        mem_phi = set(mem)
        print("In mem phi")
        _set_print(mem_phi)
    #phi allocation ends here
    print(M)
    _dict_print(vrmap)
    _set_print(bb.In)
    for i in bb.ins:
        if i.is_phi:
            continue
        print(i)
        ds = i.get_dfn()
        u = i.get_used()
        for v in u:
            assert(v in vrmap)
            if not vrmap[v].is_reg:
                promote(v, avail_reg, vrmap, rvmap, ret, M)

        dreg = None
        for v in i.last_use:
            assert v in vrmap, str(v)
            M.drop(v)
            dreg = vrmap[v]
            avail_reg |= {vrmap[v]}
            del rvmap[vrmap[v]]
            del vrmap[v]
        if not ds:
            continue
        d, = ds
        if len(i.last_use) == 1:
            #reuse the operand register
            rvmap[dreg] = d
            vrmap[d] = dreg
            ret[d] = deque([dreg])
            avail_reg -= {dreg}
            print("Reuse %s for %s" % (dreg, d))
        else :
            #more than one or none, reuse does not make sense
            promote(d, avail_reg, vrmap, rvmap, ret, M)
    bb.assign_out_reg(vrmap)
    _dict_print(bb.out_reg)
    return (ret, mem_phi, prmap)

def promote_replay_half(v, rvmap, vrmap, allocation):
    #promote v into reg, do store/load if necessary
    #but don't change vrmap besides for v
    if v in vrmap and vrmap[v].is_reg:
        return (None, None, [])
    ret = []
    assert v in allocation, str(v)
    r = allocation[v].popleft()
    assert r.is_reg
    oldv = None
    m = None
    if r in rvmap:
        oldv = rvmap[r]
        #empty allocation means it's not longer needed
        e, m = allocation[oldv].popleft()
        print("Store %s(%s) -> %s, for %s" % (oldv, vrmap[oldv], m, v))
        assert m.is_mem
        if not e:
            ret += [Store(m, r)]
    if v in vrmap:
        ret += [Load(r, vrmap[v])]
        print("Load %s(%s) -> %s" % (v, vrmap[v], r))
    vrmap[v] = r
    _dict_print(vrmap)
    rvmap[r] = v
    return (oldv, m, ret)


def promote_replay(v, rvmap, vrmap, allocation):
    oldv, m, ins = promote_replay_half(v, rvmap, vrmap, allocation)
    if oldv:
        vrmap[oldv] = m
    return ins

def allocate(ir):
    total_pred = {}
    total_avail = {}
    allocated_pred = {}
    allocated_avail = {}
    allocation = {}
    in_mem_phi = {}
    prmaps = {}
    for bb in ir.bb:
        total_pred[bb.name] = len(bb.predecessors)
        total_avail[bb.name] = len(bb.availbb)
        allocated_pred[bb.name] = 0
        allocated_avail[bb.name] = 0

    queue = set([bb for bb in ir.bb if total_pred[bb.name] == 0])
    queue2 = set([bb for bb in ir.bb if total_avail[bb.name] == 0])
    queue2 -= queue
    while queue:
        h = queue.pop()
        queue2 -= {h}
        #allocate bb
        allocation[h], in_mem_phi[h], prmaps[h] = allocate_bb(h, ir.bbmap)
        for nbb in h.successors:
            allocated_pred[nbb] += 1
            if allocated_pred[nbb] == total_pred[nbb] and nbb not in allocation:
                queue |= {ir.bbmap[nbb]}
        for dbb in h.dombb:
            allocated_avail[dbb] += 1
            if allocated_avail[dbb] == total_avail[dbb] and dbb not in allocation:
                queue2 |= {ir.bbmap[dbb]}
        if not queue:
            #queue empty, add all bb whose availbb is allocated
            queue = queue2
            queue2 = set()
    for bb in allocation:
        print("<=====%s=====>" % bb.name)
        res = ""
        for v in allocation[bb]:
            res += ("%s: " % v)
            for reg in allocation[bb][v]:
                if isinstance(reg, tuple):
                    res += ("(%s, %s), " % reg)
                else :
                    res += ("%s, " % reg)
        print(res)

    #_dict_print(in_mem_phi)

    nir = IR()
    for bb in ir.bb:
        #generate new ir with registers
        #phi nodes is generated by its predecessors
        vrmap = {}
        rvmap = {}
        pred = None
        nbb = BB(bb.name)
        bballoc = allocation[bb]
        bbmemphi = in_mem_phi[bb]
        if len(bb.predecessors) == 1:
            pred, = bb.predecessors
            pred = ir.bbmap[pred]
            for v in bb.In:
                assert v in pred.out_reg
                vrmap[v] = pred.out_reg[v]
                if vrmap[v].is_reg:
                    rvmap[vrmap[v]] = v
        else :
            for i in bb.phi:
                v = i.dst
                vrmap[v] = bballoc[v].popleft()
                if vrmap[v].is_reg:
                    rvmap[vrmap[v]] = v
                else :
                    assert v in bbmemphi, "%s has %s, but not in bbmemphi, %s" % (v, vrmap[v], bb.name)
        for i in bb.ins:
            if i.is_phi:
                continue
            ni = copy.copy(i)
            u = ni.get_used()
            for v in u:
                nbb += promote_replay(v, rvmap, vrmap, allocation[bb])
            for v in i.last_use:
                assert v not in allocation or not allocation[v]
                print("Last use: %s" % v)
                del rvmap[vrmap[v]]
            ds = i.get_dfn()
            d = None
            oldv = None
            m = None
            if ds:
                d, = ds
                oldv, m, ins = promote_replay_half(d, rvmap, vrmap, allocation[bb])
                if oldv:
                    print("...but delay vrmap change")
                nbb += ins
            ni.allocate(vrmap)
            if oldv:
                vrmap[oldv] = m
            for v in i.last_use:
                del vrmap[v]
            if ni.is_br:
                print(ni)
                ni.tgt = bb.name+"_"+ni.tgt
            nbb += [ni]
        nir += [nbb]

        if not bb.successors:
            continue
        phibb = [None, None]
        assert len(bb.successors) <= 2
        for succ in bb.successors:
            sbb = ir.bbmap[succ]
            nbb = gen_phi_block(bb, sbb, prmaps[sbb])
            #fallthrough should be put right after
            if not bb.br or not bb.fall_through:
                phibb = [nbb]
            elif succ == bb.br.tgt:
                phibb[1] = nbb
            else :
                phibb[0] = nbb
        print(bb.name)
        print(phibb)
        nir += phibb
    nir.finish()
    return (True, nir)

def gen_phi_block(bb, sbb, prmap):
    nbb = BB(bb.name+"_"+sbb.name)
    todo = set()
    src_reg = {} #any register holds src
    src_mem = {} #any memory cell holds src
    src_rcv = {} #all the phis for a src
    dsmap = {} #map from a conflict entry to the corresponding src
    a_mem = set(range(0, 4*len(sbb.phi))) #which memory cell is free? used for finding temp memory cell
    def valid_move(src, dst):
        nonlocal src_reg, src_mem, prmap, dsmap
        dreg = prmap[dst]
        if not src_reg[src] and dreg.is_mem:
            #memory to memory
            return False
        #does dreg conflict with anything?
        if dreg.is_reg and dreg in dsmap:
            return False
        if dreg.is_mem and dreg.val in dsmap:
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
    for i in sbb.phi:
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
    phiregs = set([prmap[i.dst] for i in sbb.phi if prmap[i.dst].is_reg])
    nophiregs = set(all_reg)-phiregs
    todo = set([x for x in src_rcv if src_rcv[x]])

    #step 0
    #handle all imm srcs
    s0ins = []
    immmap = {}
    tmpreg = False
    for i in sbb.phi:
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
                print("do_move(%s, %s)" % (src,dst))
                s1ins += do_move(src, dst)
        #no action available, trying to improve the situation
        #we only care about making register dsts available
        #so only thing we do is storing srcs into memory

        #What we do is therefore:
        # 1) get any registers from dsmap.keys()
        # 2) store it or move it to another register

        creg = None
        for x in dsmap:
            if isinstance(x, Register):
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
                print("Resolving conflict by %s(%s)->%s" % (src, creg, mcell))
            else :
                #otherwise move to the free reg
                reg = next(iter(avail_reg))
                src_reg[src] = reg
                dsmap[reg] = src
                s1ins.append(Arithm('+', reg, creg, 0))
                print("Resolving conflict by %s(%s)->%s" % (src, creg, reg))
        else :
            #there's no register in dsmap, and there're no possible moves
            #which means all remaining dsts are memory
            break
    #while todo end

    end = Br(0, None, sbb.name)
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
        print("We have one tmpreg during step 0")
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

    print("First phase done")
    while todo:
        #pick any src, load it, do all the valid moves, store it somewhere else
        #first see it we can find any src of whom all moves are valid
        to_promote = None
        for src in todo:
            flag = True
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
        print("promoting %s to resolve conflicts" % to_promote)
        _set_print(src_rcv[to_promote])
        pmem = src_mem[to_promote]
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
            resolve_ins.append(Store(tmpreg, mcell))
        pairs = [1]
        while bool(pairs):
            pairs = []
            for src in todo:
                if not src_reg:
                    continue
                for dst in src_rcv[src]:
                    if prmap[dst] not in dsmap:
                        pairs.append((src, dst))
            for src, dst in pairs:
                print("reg to mem(%s, %s)" % (src,dst))
                s2ins.append(Store(prmap[dst], src_reg[src]))
                src_rcv[src] -= {dst}
                if not src_rcv:
                    todo -= {src}
    if popcell:
        s2ins.append(Load(tmpreg, popcell))
    nbb += s0ins
    nbb += s1ins
    nbb += s2ins
    nbb += [end]
    return nbb
