#!/usr/bin/env python3

"""PL/0 recursive descent parser adapted from Wikipedia"""

import ir
from logger import logger
from functools import reduce


class Parser:
    def __init__(self, the_lexer):
        self.sym = None
        self.value = None
        self.new_sym = None
        self.new_value = None
        self.the_lexer = the_lexer.tokens()

    def getsym(self):
        """Update sym"""
        try:
            self.sym = self.new_sym
            self.value = self.new_value
            self.new_sym, self.new_value = next(self.the_lexer)
        except StopIteration:
            return 2
        print('getsym:', self.new_sym, self.new_value)
        return 1

    def error(self, msg):
        print('\033[31m', msg, self.new_sym, self.new_value, '\033[39m')

    def accept(self, s):
        print('accepting', s, '==', self.new_sym)
        return self.getsym() if self.new_sym == s else 0

    def expect(self, s):
        print('expecting', s)
        if self.accept(s):
            return 1
        self.error("expect: unexpected symbol")
        return 0

    def array_offset(self, symtab):
        target = symtab.find(self.value)
        offset = None
        if isinstance(target.stype, ir.ArrayType):
            idxes = []
            for i in range(0, len(target.stype.dims)):
                self.expect('lspar')
                idxes.append(self.expression(symtab))
                self.expect('rspar')
            offset = self.linearize_multid_vector(idxes, target, symtab)
        return offset

    @staticmethod
    def linearize_multid_vector(explist, target, symtab):
        offset = None
        for i in range(0, len(target.stype.dims)):
            if i + 1 < len(target.stype.dims):
                planedisp = reduce(lambda x, y: x * y, target.stype.dims[i + 1:])
            else:
                planedisp = 1
            idx = explist[i]
            esize = (target.stype.basetype.size // 8) * planedisp
            planed = ir.BinExpr(children=['times', idx, ir.Const(value=esize, symtab=symtab)], symtab=symtab)
            if offset is None:
                offset = planed
            else:
                offset = ir.BinExpr(children=['plus', offset, planed], symtab=symtab)
        return offset

    @logger
    def factor(self, symtab):
        '''F -> var | const | ( E )'''
        if self.accept('ident'):
            var = symtab.find(self.value)
            offs = self.array_offset(symtab)
            if offs is None:
                return ir.Var(var=var, symtab=symtab)
            else:
                return ir.ArrayElement(var=var, offset=offs, symtab=symtab)
        if self.accept('number'):
            return ir.Const(value=int(self.value), symtab=symtab)
        elif self.accept('lparen'):
            expr = self.expression()
            self.expect('rparen')
            return expr
        else:
            self.error("factor: syntax error")
            self.getsym()

    @logger
    def term(self, symtab):
        expr = self.factor(symtab)
        while self.new_sym in ['times', 'slash']:
            self.getsym()
            op = self.sym
            expr2 = self.factor(symtab)
            expr = ir.BinExpr(children=[op, expr, expr2], symtab=symtab)
        return expr

    @logger
    def expression(self, symtab):
        op = None
        if self.new_sym in ['plus', 'minus']:
            self.getsym()
            op = self.sym
        expr = self.term(symtab)
        if op:
            expr = ir.UnExpr(children=[op, expr], symtab=symtab)
        while self.new_sym in ['plus', 'minus']:
            self.getsym()
            op = self.sym
            expr2 = self.term(symtab)
            expr = ir.BinExpr(children=[op, expr, expr2], symtab=symtab)
        return expr

    @logger
    def condition(self, symtab):
        if self.accept('oddsym'):
            return ir.UnExpr(children=['odd', self.expression(symtab)], symtab=symtab)
        else:
            expr = self.expression(symtab)
            if self.new_sym in ['eql', 'neq', 'lss', 'leq', 'gtr', 'geq']:
                self.getsym()
                print('condition operator', self.sym, self.new_sym)
                op = self.sym
                expr2 = self.expression(symtab)
                return ir.BinExpr(children=[op, expr, expr2], symtab=symtab)
            else:
                self.error("condition: invalid operator")
                self.getsym()

    @logger
    def statement(self, symtab):
        if self.accept('ident'):
            target = symtab.find(self.value)
            offset = self.array_offset(symtab)
            self.expect('becomes')
            expr = self.expression(symtab)
            return ir.AssignStat(target=target, offset=offset, expr=expr, symtab=symtab)

        elif self.accept('callsym'):
            self.expect('ident')
            return ir.CallStat(call_expr=ir.CallExpr(function=symtab.find(self.value), symtab=symtab), symtab=symtab)
        elif self.accept('beginsym'):
            statement_list = ir.StatList(symtab=symtab)
            statement_list.append(self.statement(symtab))
            while self.accept('semicolon'):
                statement_list.append(self.statement(symtab))
            self.expect('endsym')
            statement_list.print_content()
            return statement_list
        elif self.accept('ifsym'):
            cond = self.condition(symtab)
            self.expect('thensym')
            then = self.statement(symtab)
            els = None
            if self.accept('elsesym'):
                els = self.statement(symtab)
            return ir.IfStat(cond=cond, thenpart=then, elsepart=els, symtab=symtab)
        elif self.accept('whilesym'):
            cond = self.condition(symtab)
            self.expect('dosym')
            body = self.statement(symtab)
            return ir.WhileStat(cond=cond, body=body, symtab=symtab)
        elif self.accept('print'):
            exp = self.expression(symtab)
            return ir.PrintStat(exp=exp, symtab=symtab)
        elif self.accept('read'):
            self.expect('ident')
            target = symtab.find(self.value)
            offset = self.array_offset(symtab)
            return ir.AssignStat(target=target, offset=offset, expr=ir.ReadStat(symtab=symtab), symtab=symtab)

    @logger
    def block(self, symtab, alloct='auto'):
        local_vars = ir.SymbolTable()
        defs = ir.DefinitionList()

        while self.accept('constsym') or self.accept('varsym'):
            if self.sym == 'constsym':
                self.constdef(local_vars, alloct)
                while self.accept('comma'):
                    self.constdef(local_vars, alloct)
            else:
                self.vardef(local_vars, alloct)
                while self.accept('comma'):
                    self.vardef(local_vars, alloct)
            self.expect('semicolon')

        while self.accept('procsym'):
            self.expect('ident')
            fname = self.value
            self.expect('semicolon')
            local_vars.append(ir.Symbol(fname, ir.TYPENAMES['function']))
            fbody = self.block(local_vars)
            self.expect('semicolon')
            defs.append(ir.FunctionDef(symbol=local_vars.find(fname), body=fbody))
        stat = self.statement(ir.SymbolTable(symtab[:] + local_vars))
        return ir.Block(gl_sym=symtab, lc_sym=local_vars, defs=defs, body=stat)

    @logger
    def constdef(self, local_vars, alloct='auto'):
        self.expect('ident')
        name = self.value
        self.expect('eql')
        self.expect('number')
        local_vars.append(ir.Symbol(name, ir.TYPENAMES['int'], alloct=alloct), int(self.value))
        while self.accept('comma'):
            self.expect('ident')
            name = self.value
            self.expect('eql')
            self.expect('number')
            local_vars.append(ir.Symbol(name, ir.TYPENAMES['int'], alloct=alloct), int(self.value))

    @logger
    def vardef(self, symtab, alloct='auto'):
        self.expect('ident')
        name = self.value
        size = []
        while self.accept('lspar'):
            self.expect('number')
            size.append(int(self.value))
            self.expect('rspar')

        type = ir.TYPENAMES['int']
        if self.accept('colon'):
            self.accept('ident')
            type = ir.TYPENAMES[self.value]

        if len(size) > 0:
            symtab.append(ir.Symbol(name, ir.ArrayType(None, size, type), alloct=alloct))
        else:
            symtab.append(ir.Symbol(name, type, alloct=alloct))

    @logger
    def program(self):
        """Axiom"""
        global_symtab = ir.SymbolTable()
        self.getsym()
        the_program = self.block(global_symtab, 'global')
        self.expect('period')
        return the_program
