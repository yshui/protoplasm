from parser import parser
from IR import IR
from ast import VarVer
import transform
import sys
import logging
import re

if __name__ == "__main__":
    f = open(sys.argv[1], "r")
    log = logging.getLogger()
    res = parser.parse(f.read(), debug=log)
    print(res)
    print(res.wellformed(set()))
    ir = IR()
    ir.append_bb(None)
    varv = VarVer()
    res.emit(varv, ir)
    ir.finish()
    print(ir)
    #ir = transform.empty_block_removal(ir)
    ir = transform.block_coalesce(ir)
    ir = transform.chain_breaker(ir)
#    ir.allocate()
#    print(ir)
#    outf = re.sub(r'\.[^.]*$', '.asm', sys.argv[1])
#    ir.gencode(outf)
