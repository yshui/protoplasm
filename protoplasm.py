from transform import apply_all, myhdlr
from pparser import parser
import transform.basic as btf
import transform.machine as mtf
from transform.allocation import allocate
from transform import opt
import sys
import logging
import re
import argparse

ap = argparse.ArgumentParser(description='Proto compiler')
ap.add_argument('input', help='Input file name', type=argparse.FileType('r'))
ap.add_argument('--copypropagation', dest='cp', default="off", choices=['on', 'off'])
ap.add_argument('--constantpropagation', dest='const', default="off", choices=['on', 'off'])
ap.add_argument('--cselimination', dest='cse', default="off", choices=['on', 'off'])
ap.add_argument('--loopmotion', dest='loop', default="off", choices=['on', 'off'])

def const_propagation_pass(ir):
    while True:
        c1, ir = apply_all(ir, opt.const_propagation)
        c2, ir = apply_all(ir, btf.sbr_and_unreachable)
        if not c1 or not c2:
            break

    _, ir = apply_all(ir, btf.prune_unused)
    _, ir = apply_all(ir, btf.jump_block_removal)
    _, ir = apply_all(ir, btf.branch_merge)
    _, ir = apply_all(ir, btf.prune_unused) #after branch merge, some condition variable might become unused
    return ir

def copy_propagation_pass(ir):
    changed, ir = apply_all(ir, opt.copy_propagation)
    _, ir = apply_all(ir, btf.prune_unused)
    _, ir = apply_all(ir, btf.jump_block_removal)
    _, ir = apply_all(ir, btf.branch_merge)
    _, ir = apply_all(ir, btf.prune_unused)
    return (changed, ir)

def cse_pass(ir):
    changed, ir = apply_all(ir, opt.cse)
    _, ir = apply_all(ir, btf.prune_unused)
    return (changed, ir)

if __name__ == "__main__":
    args = ap.parse_args()
    logger = logging.getLogger()
    logger.setLevel(30)
    lhdlr = logging.StreamHandler(stream=sys.stderr)
    logger.addHandler(lhdlr)
    try:
        res = parser.parse(args.input.read(), debug=logger)
    except Exception as e:
        logging.error(e)
        logging.error("Failed to parse the file, abort")
        sys.exit(0)
    logger.setLevel(10)
    logging.info(res)
    wf = res.wellformed()
    logging.info(wf)
    if not wf:
        logging.error("Program is not wellformed")
        sys.exit(0)
    else :
        logging.log(21, "Program is wellformed")
    ir = res.emit()
    logging.info("\n\nFisrt version of IR: ")
    ir.finish()
    logging.info(ir)
    logger.removeHandler(lhdlr)
    logger.addHandler(myhdlr)

    #General transformatino
    #Remove branches whose conditional is a constant number
    _, ir = apply_all(ir, btf.sbr_and_unreachable)
    #Merge chains of blocks
    _, ir = apply_all(ir, btf.block_coalesce)

    #Optimization
    if args.const == "on":
        ir = const_propagation_pass(ir)

    if args.cp == "on" and args.cse == "on":
        changed = True
        while changed:
            changed = False
            c, ir = copy_propagation_pass(ir)
            if c:
                print("Copy changed")
            changed = changed or c
            #cse might make more copy propagation possible
            c, ir = cse_pass(ir)
            if c:
                print("CSE changed")
            changed = changed or c
    elif args.cp == "on":
        _, ir = copy_propagation_pass(ir)
    elif args.cse == "on":
        _, ir = cse_pass(ir)

    if args.loop == "on":
        _, ir = apply_all(ir, opt.loop_motion_all)
    if args.cse == "on":
        _, ir = cse_pass(ir)

    #Merge chains of blocks, again
    _, ir = apply_all(ir, btf.block_coalesce)

    #out-of-SSA preparation
    #Rename variables that 'passthrough' a basic block
    _, ir = apply_all(ir, btf.variable_rename)

    #out-of-SSA
    _, ir = apply_all(ir, allocate)
    #Add instructions to move return value to $v0
    _, ir = apply_all(ir, mtf.return_value)
    #Add instructions for allocating stack space for local variables
    _, ir = apply_all(ir, mtf.local_stack_alloc)
    #Add instructions to save those callee-saved registers
    _, ir = apply_all(ir, mtf.save_registers)
    #Remove basic block which only has a branch instruction
    _, ir = apply_all(ir, btf.jump_block_removal)
    #Replace conditional branch with unconditional branch if both target are the same
    _, ir = apply_all(ir, btf.branch_merge)
    #Merge chains of basic blocks together
    _, ir = apply_all(ir, btf.block_coalesce)
    outf = re.sub(r'\.[^.]*$', '.asm', args.input.name)
    logger.addHandler(lhdlr)
    logging.info("\n\nAfter register allocation:")
    logging.info(ir)
    ir.gencode(outf)
