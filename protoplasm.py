from parser import parser
from IR.mod import IR
from transform import apply_all
import transform.basic as btf
import transform.machine as mtf
from transform.allocation import allocate
import sys
import logging
import re
import pdb

if __name__ == "__main__":
    f = open(sys.argv[1], "r")
    logger = logging.getLogger()
    logger.setLevel(logging.WARNING)
    lhdlr = logging.StreamHandler(stream=sys.stderr)
    logger.addHandler(lhdlr)
    res = parser.parse(f.read(), debug=logger)
    logger.setLevel(logging.INFO)
    logging.info(res)
    wf = res.wellformed()
    logging.info(wf)
    print(wf)
    if not wf:
        logging.error("Program not wellformed")
        sys.exit(1)
    ir = res.emit()
    logging.info("\n\nFisrt version of IR: ")
    print(ir)
    ir.finish()
    logging.info(ir)
    logger.removeHandler(lhdlr)
    _, ir = apply_all(ir, btf.sbr_and_unreachable)
    _, ir = apply_all(ir, btf.prune_unused)
    _, ir = apply_all(ir, btf.block_coalesce)
    _, ir = apply_all(ir, btf.variable_rename)
    #changed = True
    #while changed:
    _, ir = apply_all(ir, allocate)
    _, ir = apply_all(ir, mtf.return_value)
    _, ir = apply_all(ir, mtf.local_stack_alloc)
    _, ir = apply_all(ir, mtf.save_registers)
    _, ir = apply_all(ir, mtf.jump_block_removal)
    _, ir = apply_all(ir, mtf.branch_merge)
    _, ir = apply_all(ir, btf.block_coalesce)
    outf = re.sub(r'\.[^.]*$', '.asm', sys.argv[1])
    logger.addHandler(lhdlr)
    logging.info("\n\nAfter register allocation:")
    logging.info(ir)
    ir.gencode(outf)
