from parser import parser
from transform import apply_all, myhdlr
import transform.basic as btf
import transform.machine as mtf
from transform.allocation import allocate
import sys
import logging
import re

if __name__ == "__main__":
    f = open(sys.argv[1], "r")
    logger = logging.getLogger()
    logger.setLevel(21)
    lhdlr = logging.StreamHandler(stream=sys.stderr)
    logger.addHandler(lhdlr)
    try:
        res = parser.parse(f.read(), debug=logger)
    except Exception as e:
        logging.error(e)
        logging.error("Failed to parse the file, abort")
        sys.exit(1)
    logging.info(res)
    wf = res.wellformed()
    logging.info(wf)
    if not wf:
        logging.error("Program is not wellformed")
        sys.exit(1)
    else :
        logging.log(21, "Program is wellformed")
    ir = res.emit()
    logging.info("\n\nFisrt version of IR: ")
    ir.finish()
    logging.info(ir)
    logger.removeHandler(lhdlr)
    logger.addHandler(myhdlr)

    #Remove branches whose conditional is a constant number
    _, ir = apply_all(ir, btf.sbr_and_unreachable)
    #Remove unused/unreachable variables
    _, ir = apply_all(ir, btf.prune_unused)
    #Merge chains of blocks
    _, ir = apply_all(ir, btf.block_coalesce)
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
    _, ir = apply_all(ir, mtf.jump_block_removal)
    #Replace conditional branch with unconditional branch if both target are the same
    _, ir = apply_all(ir, mtf.branch_merge)
    #Merge chains of basic blocks together
    _, ir = apply_all(ir, btf.block_coalesce)
    outf = re.sub(r'\.[^.]*$', '.asm', sys.argv[1])
    logger.addHandler(lhdlr)
    logging.info("\n\nAfter register allocation:")
    logging.info(ir)
    ir.gencode(outf)
