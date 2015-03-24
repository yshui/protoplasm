from parser import parser
from IR import IR
from ast import VarVer
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
    print(ir)
    ir.calc_connections()
    ir.calc_avail()
    ir.validate()
    ir.calc_inout()
    print(ir)
    ir.allocate()
    print(ir)
    outf = re.sub(r'\.[^.]*$', '.asm', sys.argv[1])
    ir.gencode(outf)
