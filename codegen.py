#!/usr/bin/env python3

"""Code generation methods for all low-level nodes in the IR.
Codegen functions return a string, consisting of the assembly code they
correspond to. Alternatively, they can return a list where:
 - the first element is the assembly code
 - the second element is extra assembly code to be appended at the end of
   the code of the function they are contained in
This feature can be used only by IR nodes that are contained in a Block, and
is used for adding constant literals."""

from datalayout import *
from ir import *

localconsti = 0


def new_local_const_label():
    global localconsti
    lab = '.const' + repr(localconsti)
    localconsti += 1
    return lab


def new_local_const(val):
    lab = new_local_const_label()
    trail = lab + ':\n\t.word ' + val + '\n'
    return lab, trail


def symbol_codegen(self, regalloc):
    if self.allocinfo is None:
        return ""
    if not isinstance(self.allocinfo, LocalSymbolLayout):
        return '\t.comm ' + self.allocinfo.symname + ', ' + repr(self.allocinfo.bsize) + "\n"
    else:
        return '\t.equ ' + self.allocinfo.symname + ', ' + repr(self.allocinfo.fpreloff) + "\n"


Symbol.codegen = symbol_codegen


def irnode_codegen(self, regalloc):
    res = ['\t' + comment("irnode " + repr(id(self)) + ' type ' + repr(type(self))), '']
    if 'children' in dir(self) and len(self.children):
        for node in self.children:
            try:
                try:
                    labl = node.get_label()
                    res[0] += labl.name + ':\n'
                except Exception:
                    pass
                res = codegen_append(res, node.codegen(regalloc))
            except Exception as e:
                res[0] += "\t" + comment("node " + repr(id(node)) + " did not generate any code")
                res[0] += "\t" + comment("exc: " + repr(e))
    return res


IRNode.codegen = irnode_codegen


def block_codegen(self, regalloc):
    res = [comment('block'), '']
    for sym in self.symtab:
        res = codegen_append(res, sym.codegen(regalloc))

    if self.parent is None:
        res[0] += '\t.global __pl0_start\n'
        res[0] += "__pl0_start:\n"

    res[0] += save_regs(REGS_CALLEESAVE + [REG_FP, REG_LR])
    res[0] += '\tmov ' + get_register_string(REG_FP) + ', ' + get_register_string(REG_SP) + '\n'
    stacksp = self.stackroom + regalloc.spill_room()
    res[0] += '\tsub ' + get_register_string(REG_SP) + ', ' + get_register_string(REG_SP) + ', #' + repr(stacksp) + '\n'

    regalloc.enter_function_body(self)
    try:
        res = codegen_append(res, self.body.codegen(regalloc))
    except Exception:
        pass

    res[0] += '\tmov ' + get_register_string(REG_SP) + ', ' + get_register_string(REG_FP) + '\n'
    res[0] += restore_regs(REGS_CALLEESAVE + [REG_FP, REG_LR])
    res[0] += '\tbx lr\n'

    res[0] = res[0] + res[1]
    res[1] = ''

    try:
        res = codegen_append(res, self.defs.codegen(regalloc))
    except Exception:
        pass

    return res[0] + res[1]


Block.codegen = block_codegen


def deflist_codegen(self, regalloc):
    return ''.join([child.codegen(regalloc) for child in self.children])


DefinitionList.codegen = deflist_codegen


def fun_codegen(self, regalloc):
    res = '\n' + self.symbol.name + ':\n'
    res += self.body.codegen(regalloc)
    return res


FunctionDef.codegen = fun_codegen


def binstat_codegen(self, regalloc):
    res = regalloc.gen_spill_load_if_necessary(self.srca)
    res += regalloc.gen_spill_load_if_necessary(self.srcb)
    ra = regalloc.get_register_for_variable(self.srca)
    rb = regalloc.get_register_for_variable(self.srcb)
    rd = regalloc.get_register_for_variable(self.dest)
    param = ra + ', ' + rb
    if self.op == "plus":
        res += '\tadd ' + rd + ', ' + param + '\n'
    elif self.op == "minus":
        res += '\tsub ' + rd + ', ' + param + '\n'
    elif self.op == "times":
        res += '\tmul ' + rd + ', ' + param + '\n'
    elif self.op == "slash":
        res += '\tdiv ' + rd + ', ' + param + '\n'
    elif self.op == "eql":
        res += '\tcmp ' + param + '\n'
        res += '\tmoveq ' + rd + ', #1\n'
        res += '\tmovne ' + rd + ', #0\n'
    elif self.op == "neq":
        res += '\tcmp ' + param + '\n'
        res += '\tmoveq ' + rd + ', #0\n'
        res += '\tmovne ' + rd + ', #1\n'
    elif self.op == "lss":
        res += '\tcmp ' + param + '\n'
        res += '\tmovlt ' + rd + ', #1\n'
        res += '\tmovge ' + rd + ', #0\n'
    elif self.op == "leq":
        res += '\tcmp ' + param + '\n'
        res += '\tmovle ' + rd + ', #1\n'
        res += '\tmovgt ' + rd + ', #0\n'
    elif self.op == "gtr":
        res += '\tcmp ' + param + '\n'
        res += '\tmovgt ' + rd + ', #1\n'
        res += '\tmovle ' + rd + ', #0\n'
    elif self.op == "geq":
        res += '\tcmp ' + param + '\n'
        res += '\tmovge ' + rd + ', #1\n'
        res += '\tmovlt ' + rd + ', #0\n'
    else:
        raise Exception("operation " + repr(self.op) + " unexpected")
    return res + regalloc.gen_spill_store_if_necessary(self.dest)


BinStat.codegen = binstat_codegen


def print_codegen(self, regalloc):
    res = regalloc.gen_spill_load_if_necessary(self.src)
    rp = regalloc.get_register_for_variable(self.src)
    res += save_regs(REGS_CALLERSAVE)
    res += '\tmov ' + get_register_string(0) + ', ' + rp + '\n'
    res += '\tbl __pl0_print\n'
    res += restore_regs(REGS_CALLERSAVE)
    return res


PrintCommand.codegen = print_codegen


def read_codegen(self, regalloc):
    rd = regalloc.get_register_for_variable(self.dest)

    # punch a hole in the saved registers if one of them is the destination
    # of this "instruction"
    savedregs = list(REGS_CALLERSAVE)
    if regalloc.vartoreg[self.dest] in savedregs:
        savedregs.remove(regalloc.vartoreg[self.dest])

    res = save_regs(savedregs)
    res += '\tbl __pl0_read\n'
    res += '\tmov ' + rd + ', ' + get_register_string(0) + '\n'
    res += restore_regs(savedregs)
    res += regalloc.gen_spill_store_if_necessary(self.dest)
    return res


ReadCommand.codegen = read_codegen


def branch_codegen(self, regalloc):
    targetl = self.target.name
    if not self.returns:
        if self.cond is None:
            return '\tb ' + targetl + '\n'
        else:
            res = regalloc.gen_spill_load_if_necessary(self.cond)
            rcond = regalloc.get_register_for_variable(self.cond)
            res += '\ttst ' + rcond + ', ' + rcond + '\n'
            return res + '\t' + ('beq' if self.negcond else 'bne') + ' ' + targetl + '\n'
    else:
        if self.cond is None:
            res = save_regs(REGS_CALLERSAVE)
            res += '\tbl ' + targetl + '\n'
            res += restore_regs(REGS_CALLERSAVE)
            return res
        else:
            res = regalloc.gen_spill_load_if_necessary(self.cond)
            rcond = regalloc.get_register_for_variable(self.cond)
            res += '\ttst ' + rcond + ', ' + rcond + '\n'
            res += '\t' + ('bne' if self.negcond else 'beq') + ' ' + rcond + ', 1f\n'
            res += save_regs(REGS_CALLERSAVE)
            res += '\tbl ' + targetl + '\n'
            res += restore_regs(REGS_CALLERSAVE)
            res += '1:'
            return res
    return comment('impossible!')


BranchStat.codegen = branch_codegen


def emptystat_codegen(self, regalloc):
    return '\t' + comment('emptystat')


EmptyStat.codegen = emptystat_codegen


def ldptrto_codegen(self, regalloc):
    rd = regalloc.get_register_for_variable(self.dest)
    res = ''
    trail = ''
    ai = self.symbol.allocinfo
    if type(ai) is LocalSymbolLayout:
        off = ai.fpreloff
        if off > 0:
            res = '\tadd ' + rd + ', ' + get_register_string(REG_FP) + ', #' + repr(off) + '\n'
        else:
            res = '\tsub ' + rd + ', ' + get_register_string(REG_FP) + ', #' + repr(-off) + '\n'
    else:
        lab, tmp = new_local_const(ai.symname)
        trail += tmp
        res = '\tldr ' + rd + ', ' + lab + '\n'
    return [res + regalloc.gen_spill_store_if_necessary(self.dest), trail]


LoadPtrToSym.codegen = ldptrto_codegen


def storestat_codegen(self, regalloc):
    res = ''
    trail = ''
    if self.dest.alloct == 'reg':
        res += regalloc.gen_spill_load_if_necessary(self.dest)
        dest = '[' + regalloc.get_register_for_variable(self.dest) + ']'
    else:
        ai = self.dest.allocinfo
        if type(ai) is LocalSymbolLayout:
            dest = '[' + get_register_string(REG_FP) + ', #' + ai.symname + ']'
        else:
            lab, tmp = new_local_const(ai.symname)
            trail += tmp
            res += '\tldr ' + get_register_string(REG_SCRATCH) + ', ' + lab + '\n'
            dest = '[' + get_register_string(REG_SCRATCH) + ']'

    if type(self.dest.stype) is PointerType:
        desttype = self.dest.stype.pointstotype
    else:
        desttype = self.dest.stype
    typeid = ['b', 'h', None, ''][desttype.size // 8 - 1]
    if typeid != '' and 'unsigned' in desttype.qual_list:
        typeid = 's' + type

    res += regalloc.gen_spill_load_if_necessary(self.symbol)
    rsrc = regalloc.get_register_for_variable(self.symbol)
    return [res + '\tstr' + typeid + ' ' + rsrc + ', ' + dest + '\n', trail]


StoreStat.codegen = storestat_codegen


def loadstat_codegen(self, regalloc):
    res = ''
    trail = ''
    if self.symbol.alloct == 'reg':
        res += regalloc.gen_spill_load_if_necessary(self.symbol)
        src = '[' + regalloc.get_register_for_variable(self.symbol) + ']'
    else:
        ai = self.symbol.allocinfo
        if type(ai) is LocalSymbolLayout:
            src = '[' + get_register_string(REG_FP) + ', #' + ai.symname + ']'
        else:
            lab, tmp = new_local_const(ai.symname)
            trail += tmp
            res += '\tldr ' + get_register_string(REG_SCRATCH) + ', ' + lab + '\n'
            src = '[' + get_register_string(REG_SCRATCH) + ']'

    if type(self.symbol.stype) is PointerType:
        desttype = self.symbol.stype.pointstotype
    else:
        desttype = self.symbol.stype
    typeid = ['b', 'h', None, ''][desttype.size // 8 - 1]
    if typeid != '' and 'unsigned' in desttype.qual_list:
        typeid = 's' + type

    rdst = regalloc.get_register_for_variable(self.dest)
    res += '\tldr' + typeid + ' ' + rdst + ', ' + src + '\n'
    res += regalloc.gen_spill_store_if_necessary(self.dest)
    return [res, trail]


LoadStat.codegen = loadstat_codegen


def loadimm_codegen(self, regalloc):
    rd = regalloc.get_register_for_variable(self.dest)
    val = self.val
    if val >= -256 and val < 256:
        if val < 0:
            rv = -val - 1
            op = 'mvn '
        else:
            rv = val
            op = 'mov '
        res = '\t' + op + rd + ', #' + repr(rv) + '\n'
        trail = ''
    else:
        lab, trail = new_local_const(repr(val))
        res = '\tldr ' + rd + ', ' + lab + '\n'
    return [res + regalloc.gen_spill_store_if_necessary(self.dest), trail]


LoadImmStat.codegen = loadimm_codegen


def unarystat_codegen(self, regalloc):
    res = regalloc.gen_spill_load_if_necessary(self.src)
    rs = regalloc.get_register_for_variable(self.src)
    rd = regalloc.get_register_for_variable(self.dest)
    if self.op == 'plus':
        if rs != rd:
            res += '\tmov ' + rd + ', ' + rs + '\n'
    elif self.op == 'minus':
        res += '\tmvn ' + rd + ', ' + rs + '\n'
        res += '\tadd ' + rd + ', ' + rd + ', #1\n'
    elif self.op == 'odd':
        res += '\tand ' + rd + ', ' + rs + ', #1\n'
    else:
        raise Exception("operation " + repr(self.op) + " unexpected")
    res += regalloc.gen_spill_store_if_necessary(self.dest)
    return res


UnaryStat.codegen = unarystat_codegen


def generate_code(program, regalloc):
    res = '\t.text\n'
    res += '\t.arch armv6\n'
    res += '\t.syntax unified\n'
    return res + program.codegen(regalloc)
