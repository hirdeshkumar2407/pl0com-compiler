#!/usr/bin/env python3

"""Helper functions used by the code generator"""

from regalloc import *

REG_FP = 11
REG_SCRATCH = 12
REG_SP = 13
REG_LR = 14
REG_PC = 15

REGS_CALLEESAVE = [4, 5, 6, 7, 8, 9, 10]
REGS_CALLERSAVE = [0, 1, 2, 3]


def get_register_string(regid):
    if regid == REG_LR:
        return 'lr'
    if regid == REG_SP:
        return 'sp'
    return 'r' + repr(regid)


def save_regs(reglist):
    if len(reglist) == 0:
        return ''
    res = '\tpush {'
    for i in range(0, len(reglist)):
        if i > 0:
            res += ', '
        res += get_register_string(reglist[i])
    res += '}\n'
    return res


def restore_regs(reglist):
    if len(reglist) == 0:
        return ''
    res = '\tpop {'
    for i in range(0, len(reglist)):
        if i > 0:
            res += ', '
        res += get_register_string(reglist[i])
    res += '}\n'
    return res


def comment(cont):
    return '@ ' + cont + '\n'


def codegen_append(vec, code):
    if type(code) is list:
        return [vec[0] + code[0], vec[1] + code[1]]
    return [vec[0] + code, vec[1]]


# class RegisterAllocation:


def enter_function_body(self, block):
    self.curfun = block
    self.spillvarloc = dict()
    self.spillvarloctop = -block.stackroom


def gen_spill_load_if_necessary(self, var):
    self.dematerialize_spilled_var_if_necessary(var)
    if not self.materialize_spilled_var_if_necessary(var):
        # not a spilled variable
        return ''
    offs = self.spillvarloctop - self.vartospillframeoffset[var] - 4
    rd = self.get_register_for_variable(var)
    res = '\tldr ' + rd + ', [' + get_register_string(REG_FP) + ', #' + repr(offs) + ']'
    res += '\t' + comment('<<- fill')
    return res


def get_register_for_variable(self, var):
    self.materialize_spilled_var_if_necessary(var)
    res = get_register_string(self.vartoreg[var])
    return res


def gen_spill_store_if_necessary(self, var):
    if not self.materialize_spilled_var_if_necessary(var):
        # not a spilled variable
        return ''
    offs = self.spillvarloctop - self.vartospillframeoffset[var] - 4
    rd = self.get_register_for_variable(var)
    res = '\tstr ' + rd + ', [' + get_register_string(REG_FP) + ', #' + repr(offs) + ']'
    res += '\t' + comment('<<- spill')
    self.dematerialize_spilled_var_if_necessary(var)
    return res


RegisterAllocation.enter_function_body = enter_function_body
RegisterAllocation.gen_spill_load_if_necessary = gen_spill_load_if_necessary
RegisterAllocation.get_register_for_variable = get_register_for_variable
RegisterAllocation.gen_spill_store_if_necessary = gen_spill_store_if_necessary
