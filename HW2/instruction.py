#this class is for IR instructions
class Ins:
    rassigned = False
    mem = -1
    mused = set()
    @property
    def idef(self):
        #return the Def set
        assert not self.rassigned
        return self._def
    @property
    def iused(self):
        #return the Used set
        assert not self.rassigned
        return self.used
    @property
    def iin(self):
        #return the In set
        assert not self.rassigned
        return self._in
    def liveness(self, out):
        #calculate the liveness
        assert not self.rassigned
        self._in = self.used|out-self._def
    def mliveness(self, out):
        #calculate the liveness of memory cells
        if self.opcode == 9 :
            self.mused = out|{self.operands[1]}
        elif self.opcode == 8 :
            self.mused = out-{self.operands[1]}
        else :
            self.mused = out
    def transform(self, vmap):
        #changed the variable name in the instruction
        #used for spilling
        assert not self.rassigned
        self.operands = [vmap[x] if x in vmap else x for x in self.operands]
        self.used = set([vmap[x] if x in vmap else x for x in self.used])
        #vmap should not change _def
        #_in is now invalid
        self._in = None
        return self
    def assign(self, rmap, dummy):
        #assigned registers to this instruction
        #dummy is used when there's no register assign for the target variable
        assert not self.rassigned
        self.rassigned = True
        nopr = []
        for o in self.operands:
            if isinstance(o, str):
                if o not in rmap:
                    print("{0} is not used".format(o))
                    nopr += [dummy]
                else :
                    nopr += [rmap[o]]
            else :
                nopr += [o]
        self.operands = nopr
    def gencode(self, f):
        #Generate the machine code from this IR instruction
        global ins_realname
        opc = self.opcode
        if opc == 0 :
            f.write("li $v0, 5\nsyscall\n")
            f.write("move ${0}, $v0\n".format(self.operands[0]))
        elif opc >= 1 and opc <= 5 :
            f.write("{0} ${1}, ${2},".format(ins_realname[opc],
                                             self.operands[0],
                                             self.operands[1]))
            if isinstance(self.operands[2], str):
                f.write(" ${0}\n".format(self.operands[2]))
            else :
                f.write(" {0}\n".format(self.operands[2]))
        elif opc == 6 :
            if isinstance(self.operands[1], str):
                f.write("move ${0}, ${1}\n".format(self.operands[0], self.operands[1]))
            else :
                f.write("li ${0}, {1}\n".format(self.operands[0], self.operands[1]))
        elif opc == 7 :
            if isinstance(self.operands[0], str):
                f.write("move $a0, ${0}\n".format(self.operands[0]))
            else :
                f.write("li $a0, {0}\n".format(self.operands[0]))
            f.write("li $v0, 1\nsyscall\n")
            f.write("li $v0, 4\nla $a0, nl\nsyscall\n")
        elif opc == 8 :
            assert self.mem >= 0
            f.write("sw ${0}, {1}($sp)\n".format(self.operands[0], self.mem*4))
        elif opc == 9 :
            assert self.mem >= 0
            f.write("lw ${0}, {1}($sp)\n".format(self.operands[0], self.mem*4))

    @property
    def useful(self):
        #Is this instruction a NOP?
        if self.masked:
            return False
        opc = self.opcode
        #if self.operands[0] == "0" and opc != 0 : #target is r0 and not an input
        #    return False
        if opc == 1 or opc == 2 : #ADD, SUB
            if self.operands[0] == self.operands[1] and self.operands[2] == 0 :
                return False
        elif opc == 3 or opc == 4 : #DIV, MUL
            if self.operands[0] == self.operands[1] and self.operands[2] == 1 :
                return False
        elif opc == 6 and self.operands[0] == self.operands[1]: #MOVE
            return False
        return True

    def __str__(self):
        global ins_name
        rst = ins_name[self.opcode]+" "
        for opr in self.operands:
            if isinstance(opr, str) :
                rst += "%"+opr+", "
            else :
                rst += str(opr)+", "
        if (self.opcode == 8 or self.opcode == 9) and self.rassigned:
            if self.mem == -1 :
                rst += "\t#memory location unassigned"
            else :
                rst += "\t#at stack+{0}".format(self.mem*4)
        if self.masked:
            rst += "(masked)"
        return rst
    def __init__(self, opc, opr, rasgned = False):
        self.opcode = opc
        self.operands = opr
        self._in = None
        self.masked = False
        self.loaded = False
        self._def = None
        self.used = None
        self.rassigned = rasgned
        #calculate the def and used set
        if opc != 7 and opc != 8 :
            self._def = set([opr[0]])
        else :
            self._def = set()
        self.used = set()
        #some sanity checks
        if opc == 0 : #INPUT
            assert len(opr) == 1
            assert isinstance(opr[0], str)
        elif opc >= 1 and opc <= 5 : #ADD, SUB, DIV, MUL, MOD
            assert len(opr) == 3
            assert isinstance(opr[0], str) and isinstance(opr[1], str)
            assert isinstance(opr[2], str) or isinstance(opr[2], int)
            self.used |= {opr[1]}
            if isinstance(opr[2], str):
                self.used |= {opr[2]}
        elif opc == 6 : #MOVE
            assert len(opr) == 2
            assert isinstance(opr[0], str)
            assert isinstance(opr[1], int) or isinstance(opr[1], str)
            if isinstance(opr[1], str):
                self.used |= {opr[1]}
        elif opc == 7 : #PRINT
            assert len(opr) == 1
            assert isinstance(opr[0], str) or isinstance(opr[0], int)
            if isinstance(opr[0], str):
                self.used |= {opr[0]}
        elif opc == 8 or opc == 9 : #LOAD, STORE pseudo instruction
            assert len(opr)==2
            assert isinstance(opr[0], str)
            assert isinstance(opr[1], int)
            if opc == 8 : #STORE
                self.used = set([opr[0]])


ins_name = ["INPUT", "ADD", "SUB", "MUL", "DIV", "MOD", "MOVE", "PRINT",
            "STORE", "LOAD"]
ins_realname = ["", "add", "sub", "mul", "div", "rem"]
