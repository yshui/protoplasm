from IR import IR, BB, Arithm, Phi, Var, Cell, IInpt, all_reg
from collections import deque
import copy
def _phi_get_used(i):
    u = set()
    for bb, v in i.srcs.items():
        if v.is_var:
            u |= {v.val}
    return u
def _dict_print(d):
    res = "{"
    for k, v in d.items():
        res += ", %s: %s" % (k, v)
    res += "}"
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
            nir += [bb]
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
    removed = set()
    nir = IR()
    changed = False
    for bb in ir.bb:
        if bb.name in removed:
            continue
        if len(bb.successors) != 1:
            nir += [bb]
            continue
        succ, = bb.successors
        succ = ir.bbmap[succ]
        if len(succ.predecessors) > 1:
            nir += [bb]
            continue
        assert bb.name in succ.predecessors
        if succ.phi:
            nir += [bb]
            continue
        nbb = BB(bb.name+succ.name)
        nbb += bb.nonbr_ins
        nbb += succ.ins
        nir += [nbb]
        removed |= {nbb.name}
        changed = True
    nir.finish()

    return (changed, nir)
def chain_breaker(ir):
    nir = IR()
    changed = False
    for bb in ir.bb:
        print("======%s======" % bb.name)
        if not bb.In and not bb.phi:
            print("No phi, no in, continue")
            nir += [bb]
            continue
        nbb = BB(bb.name)
        #add phi nodes
        varmap = {}
        if len(bb.predecessors) > 1:
            #create phi node to grab the replaced
            #variable from different preds
            print("Generate additional phi")
            for v in bb.In:
                changed = True
                nphi = Phi("%"+v+"."+bb.name)
                for p in bb.predecessors:
                    pp = ir.bbmap[p]
                    if v in pp.In:
                        nphi.set_source(p, "%"+v+"."+p)
                    else :
                        nphi.set_source(p, "%"+v)
                print(nphi)
                nbb += [nphi]
                varmap[v] = Var(v+"."+bb.name)
            print("Rewrite original phi")
            for phi in bb.phi:
                print("%s: %s" % (bb.name, phi))
                for srcbb, v in phi.srcs.items():
                    if v.is_imm:
                        continue
                    sbb = ir.bbmap[srcbb]
                    assert v.is_var
                    if v.val in sbb.In:
                        changed = True
                        print("%s in %s's In, change name to %s" % (v.val, srcbb, v.val+"."+srcbb))
                        phi.set_source(srcbb, "%"+v.val+"."+srcbb)
                    else :
                        print("%s not in %s's In" % (v.val, srcbb))
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
                if v in pred.In:
                    varmap[v] = Var(v+"."+pred.name)
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
                vname = "%"+v
                if v in pred.In:
                    vname += "."+pred.name
                nbb += [Arithm('+', "%"+v+"."+bb.name, vname, 0)]
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

def promote(v, avail_reg, vrmap, rvmap, ret, mem):
    reg = any_reg(avail_reg)
    if v not in ret:
        ret[v] = deque([reg])
    else :
        ret[v].append(reg)
    if reg in rvmap:
        mem |= {rvmap[reg]}
        vrmap[rvmap[reg]] = Cell(0)
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
    mem = set()
    only_pred = None
    if len(bb.predecessors)==1:
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
            mem |= {v}
    #register preference:
    #reg in srcs not used > other reg not used > reg in srcs used > other reg used
    for phi in bb.phi:
        reg = None #reg in srcs not used
        reg2 = None #reg in srcs used
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
                else :
                    reg2 = srcreg
        if not reg:
            if avail_reg:
                reg = avail_reg.pop()
            elif reg2:
                reg = reg2
            else :
                reg = next(iter(all_reg))
        ret[phi.dst] = deque([reg])
        avail_reg -= {reg}
        if reg in rvmap:
            mem |= {rvmap[reg]}
            vrmap[rvmap[reg]] = Cell(0)
        rvmap[reg] = phi.dst
        vrmap[phi.dst] = reg
    if bb.phi:
        mem_phi = set(mem)
    else :
        mem_phi = set()
    print(">>>>>>>>>>>>>>%s<<<<<<<<<<<<<<<<<" % (bb.name))
    _dict_print(vrmap)
    print(bb.In)
    for i in bb.ins:
        if i.is_phi:
            continue
        print(i)
        ds = i.get_dfn()
        u = i.get_used()
        for v in u:
            assert(v in vrmap)
            if v in mem:
                promote(v, avail_reg, vrmap, rvmap, ret, mem)

        dreg = None
        for v in i.last_use:
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
            promote(d, avail_reg, vrmap, rvmap, ret, mem)
    bb.assign_out_reg(vrmap)
    _dict_print(bb.out_reg)
    return (ret, mem_phi)

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
        #allocate bb
        allocation[h], in_mem_phi[h] = allocate_bb(h, ir.bbmap)
        for nbb in h.successors:
            allocated_pred[nbb] += 1
            if allocated_pred[nbb] == total_pred[nbb]:
                queue |= {ir.bbmap[nbb]}
        for dbb in h.dombb:
            allocated_avail[dbb] += 1
            if allocated_avail[dbb] == total_avail[dbb] and dbb not in queue:
                queue2 |= {ir.bbmap[dbb]}
        if not queue:
            #queue empty, add all bb whose availbb is allocated
            queue = queue2
            queue2 = set()
    print(allocation)
    print(in_mem_phi)
    return (False, ir)

    nir = IR()
    for bb in ir.bb:
        #generate new ir with registers
        pass
