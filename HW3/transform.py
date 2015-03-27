from IR import IR, BB, Arithm, Phi, Var, Cell, IInpt, Load, Store, Br, all_reg
from collections import deque
import copy
def _phi_get_used(i):
    u = set()
    for bb, v in i.srcs.items():
        if v.is_var:
            u |= {v}
    return u
def _dict_print(d):
    res = "{"
    for k, v in d.items():
        res += ", %s: %s" % (k, v)
    res += "}"
    print(res)
def _set_print(a):
    res = "set("
    for b in a:
        res += str(b)+", "
    res += ")"
    print(res)

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
        mcell = M.get(rvmap[reg])
        vrmap[rvmap[reg]] = mcell
        ret[rvmap[reg]].append(mcell)
    oldreg = "(none)"
    if v in vrmap:
        oldreg = str(vrmap[v])
    rvmap[reg] = v
    vrmap[v] = reg
    print("Promoted %s from %s to %s" % (v, oldreg, reg))

class Memory:
    def __init__(self):
        self.top = 0
        self.avail = set()
        self.rsrv = set()
        self.vmmap = {}
    def reserve(self, var, pos):
        assert isinstance(pos, Cell)
        self.vmmap[var] = pos
        pos = pos.val
        if pos < self.top:
            assert pos in self.avail
            self.avail -= {pos}
            return
        self.rsrv |= {pos}
    def get(self, var):
        if var in self.vmmap:
            return self.vmmap[var]
        if self.avail:
            self.vmmap[var] = Cell(self.avail.pop())
        else :
            while self.top in self.rsrv:
                self.rsrv -= {self.top}
                self.top += 1
            self.vmmap[var] = Cell(self.top)
            self.top += 1
        return self.vmmap[var]
    def drop(self, var):
        if var not in self.vmmap:
            return
        pos = self.vmmap[var].val
        del self.vmmap[var]
        if pos in self.rsrv:
            self.rsrv -= {pos}
            return
        if pos == self.top-1:
            self.top -= 1
            return
        self.avail |= {pos}

def allocate_bb(bb, bbmap):
    #allocate for phi
    ret = {}
    avail_reg = set(all_reg)
    rvmap = {}
    vrmap = {}
    M = Memory()
    only_pred = None
    mem_phi = set()
    if len(bb.predecessors)==1:
        assert not bb.phi
        only_pred, = bb.predecessors
        only_pred = bbmap[only_pred]
        for v in bb.In:
            #we assume chain_breaker has been run
            assert v in only_pred.out_reg
            vreg = only_pred.out_reg[v]
            vrmap[v] = vreg
            if vreg.is_reg:
                avail_reg -= {vreg}
                rvmap[vreg] = v
            else :
                M.reserve(v, vreg)
    else :
        mem = set()
        phireg = set()
        for phi in bb.phi:
            for phibb, v in phi.srcs.items():
                pbb = bbmap[phibb]
                if v not in pbb.out_reg:
                    continue
                phireg |= {pbb.out_reg[v]}
                avail_reg -= {pbb.out_reg[v]}
        #register preference:
        #reg in src >  reg not in any src > other reg > memory
        for phi in bb.phi:
            reg = None #reg in srcs not used
            for phibb, v in phi.srcs.items():
                pbb = bbmap[phibb]
                if v not in pbb.out_reg:
                    #the pbb is not allocated yet
                    continue
                srcreg = pbb.out_reg[v]
                if srcreg.is_reg:
                    if srcreg in avail_reg:
                        reg = srcreg
                        break
            if not reg:
                if avail_reg:
                    reg = avail_reg.pop()
                elif phireg:
                    reg = phireg.pop()
                else :
                    reg = M.get(phi.dst)
            ret[phi.dst] = deque([reg])
            avail_reg -= {reg}
            assert reg not in rvmap
            rvmap[reg] = phi.dst
            vrmap[phi.dst] = reg
        mem_phi = set(mem)
    print(">>>>>>>>>>>>>>%s<<<<<<<<<<<<<<<<<" % (bb.name))
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
    return (ret, mem_phi)

def promote_replay(v, rvmap, vrmap, allocation):
    if v in vrmap and vrmap[v].is_reg:
        return []
    ret = []
    assert v in allocation, str(v)
    r = allocation[v].popleft()
    assert r.is_reg
    if r in rvmap:
        oldv = rvmap[r]
        #empty allocation means it's not longer needed
        m = allocation[oldv].popleft()
        assert m.is_mem
        ret += [Store(m, r)]
        vrmap[oldv] = m
    if v in vrmap:
        ret += [Load(r, vrmap[v])]
    vrmap[v] = r
    rvmap[r] = v
    return ret

def phi_do_no_conflict(phi, src_regs, src_mems, src_rcv, rsrcmap, bballoc, name):
    #definition of no conflict:
    #   this src->dst move will not demote any src from reg to memory

    #1) phi.dst's reg is the same as src's reg
    #2) phi.dst's reg is not used by any src
    #3) phi.dst's reg is used by some src, but this src is held by another register
    #3.5) phi.dst's reg is used by some src, but that src is no longer needed
    #4) phi.dst is memory
    #srcholder is a list of places the src is held
    nphi = []
    ins = []
    progress = False
    for i in phi:
        dst = i.dst
        src = i.srcs[name]
        dreg = bballoc[dst][0]
        sregs = src_regs[src]
        if dreg in sregs:
            #case 1 dreg already hold src
            print("case 1: %s, %s: %s" % (src, dst, dreg))
            progress = True
            src_rcv[src] -= 1
            continue
        if dreg.is_mem:
            #case 4 memory
            #store from any register hold src
            print("case 4: %s, %s: %s" % (src, dst, dreg))
            ins += [Store(dreg, next(iter(sregs)))]
            src_mems[src] |= {dreg}
            src_rcv[src] -= 1
            progress = True
            continue
        if dreg not in rsrcmap:
            #case 2
            _sreg = next(iter(sregs))
            print("case 2: %s, %s: %s->%s" % (src, dst, _sreg, dreg))
            ins += [Arithm('+', dreg, _sreg, 0)]
            src_regs[src] |= {dreg}
            src_rcv[src] -= 1
            progress = True
            continue
        if src_rcv[rsrcmap[dreg]] <= 0:
            #case 3.5
            _sreg = next(iter(sregs))
            print("case 3.5: %s, %s: %s->%s" % (src, dst, _sreg, dreg))
            ins += [Arithm('+', dreg, _sreg, 0)]
            src_regs[src] |= {dreg}
            del src_regs[rsrcmap[dreg]]
            del src_mems[rsrcmap[dreg]]
            progress = True
            src_rcv[src] -= 1
            continue
        nsregs = src_regs[rsrcmap[dreg]] - {dreg}
        if nsregs:
            #case 3
            _sreg = next(iter(sregs))
            print("case 3: %s, %s: %s->%s" % (src, dst, _sreg, dreg))
            ins += [Arithm('+', dreg, _sreg, 0)]
            src_regs[src] |= {dreg}
            src_regs[rsrcmap[dreg]] -= {dreg}
            src_rcv[src] -= 1
            progress = True
            continue
        nphi.append(i)
    return (progress, ins, nphi)

def allocate(ir):
    total_pred = {}
    total_avail = {}
    allocated_pred = {}
    allocated_avail = {}
    allocation = {}
    in_mem_phi = {}
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
        allocation[h], in_mem_phi[h] = allocate_bb(h, ir.bbmap)
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
                    assert v in bbmemphi
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
            if ds:
                d, = ds
                nbb += promote_replay(d, rvmap, vrmap, allocation[bb])
            ni.allocate(vrmap)
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
            nbb = BB(bb.name+"_"+succ)
            phi = []
            src_regs = {}
            src_mems = {}
            src_rcv = {}
            rsrcmap = {}
            M = Memory()
            for i in sbb.phi:
                src = i.srcs[bb.name]
                dst = i.dst
                dst_reg = allocation[sbb][dst][0]
                if src.is_imm:
                    nbb += [Load(dst_reg, src)]
                    continue
                phi += [i]
                src_reg = bb.out_reg[src]
                if dst_reg.is_mem:
                    M.reserve(dst, dst_reg)
                if src in src_rcv:
                    src_rcv[src] += 1
                else :
                    src_rcv[src] = 1
                if src_reg.is_reg:
                    rsrcmap[src_reg] = src
                    src_regs[src] = {src_reg}
                    src_mems[src] = set()
                else :
                    src_regs[src] = set()
                    src_mems[src] = {src_reg}
            while phi:
                progress = True
                while progress:
                    #finish anything with no conflict
                    progress, ins, phi = phi_do_no_conflict(phi, src_regs, src_mems, src_rcv, rsrcmap, allocation[sbb], bb.name)
                    nbb += ins
                if not phi:
                    break
                #demote any src to memory
                demote = set()
                src_rcv = set([i for i in src_rcv if src_rcv[i] > 0])
                demote = set([next(iter(src_rcv))])
                queue = set(demote)
                while queue:
                    dmt = queue.pop()
                    for i in phi:
                        dmt = i.srcs[bb.name]
                        if dmt not in demote:
                            continue
                        dst_reg = allocation[sbb][i.dst]
                        assert dst_reg.is_reg
                        if dst_reg not in rsrcmap:
                            continue
                        osrc = rsrcmap[dst_reg]
                        if osrc not in src_rcv or src_rcv[osrc] <= 0:
                            continue
                        queue |= {osrc}
                        demote |= {osrc}
                for dmt in demote:
                    if not src_mems[dmt]:
                        mcell = M.get(dmt)
                        reg = next(iter(src_regs[dmt]))
                        nbb += [Store(mcell, reg)]
                    else :
                        mcell = next(iter(src_mems[dmt]))
                nphi = []
                for i in phi:
                    dmt = i.srcs[bb.name]
                    if dmt not in demote:
                        nphi += [i]
                        continue
                    if not src_mems[dmt]:
                        mcell = M.get(dmt)
                    dst = i.dst
                    dst_reg = allocation[sbb][dst][0]
                    assert dst_reg.is_reg
                    nbb += [Load(dst_reg, mcell)]
                phi = nphi
                for dmt in demote:
                    if not src_mems[dmt]:
                        M.drop(dmt)
                    del src_rcv[dmt]
                    del src_regs[dmt]
                    del src_mems[dmt]

            nbb += [Br(0, None, succ)]
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
