#!/usr/bin/env python3

"""Simple lexer for PL/0 using generators"""

# Tokens can have multiple definitions if needed
TOKEN_DEFS = {
    'lparen': ['('],
    'rparen': [')'],
    'lspar': ['['],
    'rspar': [']'],
    'colon': [':'],
    'times': ['*'],
    'slash': ['/'],
    'plus': ['+'],
    'minus': ['-'],
    'eql': ['='],
    'neq': ['!='],
    'lss': ['<'],
    'leq': ['<='],
    'gtr': ['>'],
    'geq': ['>='],
    'callsym': ['call'],
    'beginsym': ['begin'],
    'semicolon': [';'],
    'endsym': ['end'],
    'ifsym': ['if'],
    'whilesym': ['while'],
    'becomes': [':='],
    'thensym': ['then'],
    'elsesym': ['else'],
    'dosym': ['do'],
    'constsym': ['const'],
    'comma': [','],
    'varsym': ['var'],
    'procsym': ['procedure'],
    'period': ['.'],
    'oddsym': ['odd'],
    'print': ['!', 'print'],
    'read': ['?', 'read'],
    'forsym': ['for'],
    'tosym': ['to']
}


class Lexer:
    """The lexer. Decomposes a string in tokens."""

    def __init__(self, text):
        self.text = text
        self.pos = 0
        self.str_to_token = list([(s, t) for t, ss in TOKEN_DEFS.items() for s in ss])
        self.str_to_token.sort(key=lambda a: -len(a[0]))

    def skip_whitespace(self):
        in_comment = False
        while self.pos < len(self.text) and (self.text[self.pos].isspace() or self.text[self.pos] == '{' or in_comment):
            if self.text[self.pos] == '{' and not in_comment:
                in_comment = True
            elif in_comment and self.text[self.pos] == '}':
                in_comment = False
            self.pos += 1

    def check_symbol(self):
        for s, t in self.str_to_token:
            if self.text[self.pos:self.pos+len(s)].lower() == s:
                self.pos += len(s)
                return t, s
        return None, None

    def check_regex(self, regex):
        import re
        match = re.match(regex, self.text[self.pos:])
        if not match:
            return None
        found = match.group(0)
        self.pos += len(found)
        return found

    def tokens(self):
        """Returns a generator which will produce a stream of (token identifier, token value) pairs."""

        while self.pos < len(self.text):
            self.skip_whitespace()
            t, s = self.check_symbol()
            if s:
                yield t, s
                continue
            t = self.check_regex(r'[0-9]+')
            if t:
                yield 'number', int(t)
                continue
            t = self.check_regex(r'\w+')
            if t:
                yield 'ident', t
                continue
            try : t = self.text[self.pos] 
            except Exception : t='end of file' # at end of file this will fail because self.pos >= len(self.text)
            yield 'illegal', t
            break


# Test support
__test_program = '''VAR x, y, squ;
VAR arr[5]: char;
var multid[5][5]: short;
{ New variables for loop tests }
VAR i, j, k, m, n, p, q, sum, r;

{This is a comment. You can write anything you want in a comment}

PROCEDURE square;
VAR test;
BEGIN
   test := 1234;
   squ := x * x
END;

BEGIN
{ --- Original Code Start --- }
   x := -1;

   read x;
   if x > 100 then begin
      print -x
   end else begin
      print x
   end;

   x := 1;
   WHILE x <= 10 DO
   BEGIN
      CALL square;
      x:=x+1;
      !squ
   END;

   x := 101;
   while x <= 105 do begin
    arr[x-100] := x;
    !arr[x-100];
    x := x + 1
   end;

   x := 1;
   y := 1;
   while x <= 5 do begin
    while y <= 5 do begin
      multid[x][y] := arr[x];
      !multid[x][y];
      x := x + 1;
      y := y + 1
    end
  end;

  { Original for loop }
   for a := 10  to 20 do
   begin
      print a;
   end;
{ --- Original Code End --- }

{ === Added Loop Tests Start === }

  { Test 1: Basic Loop }
    i := 10;
    print 99991; {Marker for start 1}
    for i := 10 to 15 do
    begin
       print i;
    end;
    print 88881; {Marker for end 1}


  { Test 2: Loop with Single Iteration }
    print 99992; {Marker for start 2}
    for j := 5 to 5 do
    begin
       print j;
    end;
    print 88882; {Marker for end 2}


  { Test 3: Loop with Zero Iterations }
    print 99993; {Marker for start 3}
    for k := 10 to 5 do
    begin
       print 77777; { This should NOT print }
       print k;
    end;
    print 88883; {Marker for end 3}


  { Test 4: Loop Unrolling - Exact Multiple (e.g., factor 2) }
    print 99994; {Marker for start 4}
    for m := 1 to 6 do
    begin
        print m;
    end;
    print 88884; {Marker for end 4}


  { Test 5: Loop Unrolling - Remainder (e.g., factor 2) }
    print 99995; {Marker for start 5}
    for n := 1 to 7 do
    begin
        print n;
    end;
    print 88885; {Marker for end 5}


  { Test 6: Loop Unrolling - Fewer Iterations than Factor (e.g., factor 4) }
    print 99996; {Marker for start 6}
    for p := 10 to 12 do
    begin
        print p;
    end;
    print 88886; {Marker for end 6}


  { Test 7: Loop with Calculation Inside }
    sum := 0;
    print 99997; {Marker for start 7}
    for q := 1 to 5 do
    begin
       sum := sum + q;
       print q;
       print sum;
    end;
    print sum; { Print final sum }
    print 88887; {Marker for end 7}


  { Test 8: Loop Using Global Variable }
    x := 100; { Reset global x }
    print 99998; {Marker for start 8}
    for r := 1 to 3 do
    begin
       x := x + r;
       print x;
    end;
    print x; { Print final x }
    print 88888; {Marker for end 8}

{ === Added Loop Tests End === }

END.'''# <<< This is the final END of the main program block


if __name__ == '__main__':
    for t, w in Lexer(__test_program).tokens():
        print(t, w)
