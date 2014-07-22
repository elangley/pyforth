from __future__ import print_function
import sys
import inspect
import contextlib

@contextlib.contextmanager
def redir_stdout(new):
    old = sys.stdout
    sys.stdout = new
    yield
    sys.stdout = old

SPACE = None
class _RUN: pass

def read_word(fil):
    char = ' '
    buffer = []
    delim  = SPACE
    spaces = {' ', '\n', '\t'}
    while char != '':
        char = fil.read(1)
        if char == '':
            yield ''.join(buffer).strip()
            break
        buffer.append(char)
        if delim != SPACE and buffer[-len(delim):] == delim:
            delim = yield ''.join(buffer[:-len(delim)])
            buffer = []
        elif char in spaces:
            delim = yield ''.join(buffer[:-1]).strip()
            if char == '\n':
                yield _RUN
            buffer = []

def skip_run(reader):
    skipped = False
    r = reader.next()
    while r == _RUN:
        skipped = skipped or r == _RUN
        #print(r, end=':')
        r = reader.next()
        #print(r, end=' ')
    #print('out')
    return r, skipped

import collections
import traceback
class SymbolDict(collections.MutableMapping):
    def __init__(self, *args, **kwargs):
        self.ctr = 0
        self.items_ = set()
        self.dct = dict(*args, **kwargs)

    def __getitem__(self, key):
        if self.dct[key] != []:
            return self.dct[key][-1][1]
        else:
            raise KeyError("No such key '%s'" % key)
    def __setitem__(self, key, value):
        self.ctr += 1
        self.items_.add(key)
        self.dct.setdefault(key, []).append((self.ctr, value))
    def __delitem__(self, key):
        state = self.dct[key][-1][0]
        for a in self.dct.keys():
            while self.dct[a] and self.dct[a][-1][0] >= state:
                self.dct[a].pop()
            if self.dct[a] == []: self.dct.pop(a)
    forget = __delitem__
    def __iter__(self):
        return (x for x in self.dct.keys())
    def __len__(self):
        return len(self.dct)

import random

class Reader(object):
    symbols = SymbolDict()

    def rev_pctr(self, stack, rstack):
        num = stack.pop()
        self.program_ctr -= num

    def adv_pctr(self, stack, rstack):
        num = stack.pop()
        self.program_ctr += num

    def adv_pctr0(self, stack, rstack):
        #print('adv0 -->', stack, rstack)
        num = stack.pop()
        cond = stack.pop()
        if cond == 0:
            stack.append(num)
            self.adv_pctr(stack, rstack)

    def save_program_ctr(self):
        self.pcs.append(self.program_ctr)
    def restore_program_ctr(self):
        self.program_ctr = self.pcs.pop()
    def rollback_program(self):
        self.restore_program_ctr()
        del self.program[self.program_ctr:]
    def splice_program(self, words):
        begin = self.peek_saved_program_ctr()
        end = self.program_ctr + 1
        self.program[begin:end] = words
    def peek_saved_program_ctr(self):
        return self.pcs[-1]
    def drop_saved_program_ctr(self):
        return self.pcs.pop()

    def if_(self, stack, rstack=None):
        def if_reader(gen):
            counter = 0
            if_clause = []
            else_clause = []
            cur_clause = if_clause
            for word in gen:
                if word == 'if':
                    cur_clause.extend(if_reader(gen))
                    continue
                elif word == 'else':
                    cur_clause = else_clause
                    continue
                elif word == 'then':
                    else_clause.extend(['nop'])
                    break
                cur_clause.extend(self.expand_word(word))
            if_clause.extend(['%d' % len(else_clause), 'adv'])
            if_clause.insert(0, '%d' % len(if_clause))
            if_clause.insert(1, 'adv0')
            result = if_clause + else_clause
            return result

        ## Below we replace the if statement with a call to lower-level primitives
        ## i.e. if is implemented as a kind of macro.
        self.save_program_ctr()
        self.program_ctr += 1 # since the program counter doesn't update until after the yield
        gen = self.read_word()
        self.splice_program(if_reader(gen))
        self.restore_program_ctr()
        self.program_ctr -= 1 # in order to pick up the beginning of the if statement

    def words(self, stack, rstack=None):
        words = sorted(self.symbols.keys())
        mlen = max(len(x) for x in words)
        c = 80 // (mlen + 2)
        while words:
            head, words = words[:c], words[c:]
            print(' '.join(x.center(mlen) for x in head), file=self.out)

    def forget(self, stack, rstack=None):
        self.program_ctr += 1 # since the program counter doesn't update until after the yield
        name, skipped = skip_run(self.read_word())
        self.symbols.forget(name)
        if skipped: self.inp.append([_RUN])

    def colon(self, stack, rstack=None):
        self.program_ctr += 1 # since the program counter doesn't update until after the yield
        gen = self.read_word()
        name = gen.next()
        word = ' '
        conts = []
        while word != ';':
            word = gen.next()
            if word == _RUN: continue
            conts.append(word)
        conts.pop() # pop off the semicolon

        self.compile(name, filter(None,conts))
        #print(' >name', name, ' >symbols["%s"]' % name, self.symbols[name.lower()])

    def expand_word(self, word):
        if word in self.sym_words:
            outp = [self.expand_word(w) for w in self.sym_words[word][:]]
            return sum(outp, [])
        else:
            return [word]

    def compile(self, name, words):
        if hasattr(words, 'split'): words = words.split()
        self.sym_words[name] = words[:]
        @self.add_symbol(name)
        def newfun(stack, rstack=None):
            self.save_program_ctr()
            self.splice_program(words[:])
            self.program_ctr -= 1
        newfun.__name__ = '_forth_%s' % name
    def prog_print(self, stack, rstack=None):
        print('<%d>' % len(self.program), end=' ', file=self.out)
        for n in self.program:
            print(n, end=' ', file=self.out)
        print(file=self.out)

    def set_pctr(self, v):
        self.program_ctr = v
    def begin_until(self, stack, rstack):
        self.program_ctr += 1 # since the program counter doesn't update until after the yield
        mark = self.program_ctr
        word = ' '
        loop_count = 0
        words = []
        while True:
            word = self.read_word()
            if word == 'begin': loop_count += 1
            elif word == 'until':
                if loop_count == 0: break
                else: loop_count -= 1
            words.append(word)

    def mark_r(self, stack, rstack):
        self.jmpr.append(self.program_ctr-1)
        #print('markr', self.jmpr)
    def jmp_r(self, stack, rstack):
        dst = self.jmpr.pop()
        self.set_pctr(dst)
        #print('jmpr', dst, self.jmpr)
    def jmp_clr(self, stack, rstack):
        self.jmpr.pop()
        #print('clrjmp', self.jmpr)

    def mark(self, stack, rstack):
        self.stack.append(self.program_ctr-1)
    def jmp(self, stack, rstack):
        dst = stack.pop()
        self.set_pctr(dst)

    def __init__(self, out=sys.stdout):
        self.sym_words = SymbolDict()
        self.stack = []
        self.rstack = []
        self.program = []
        self.jmpr = []
        self.pcs = []
        self.mode = 0; # 0 - Normal; 1 - string reading
        self.program_ctr = 0
        self.out = out
        self.add_symbol('words')(self.words)
        self.add_symbol('.p')(self.prog_print)
        self.add_symbol(':')(self.colon)
        self.add_symbol('forget')(self.forget)
        self.add_symbol('if')(self.if_)
        self.add_symbol('jmp')(self.jmp)
        self.add_symbol('rev')(self.rev_pctr)
        self.add_symbol('adv')(self.adv_pctr)
        self.add_symbol('adv0')(self.adv_pctr0)
        self.add_symbol('mark')(self.mark)
        self.add_symbol('markr')(self.mark_r)
        self.add_symbol('jmpr')(self.jmp_r)
        self.add_symbol('clrjmp')(self.jmp_clr)

    def __getword(self):
        while self.inp[-1] == []: self.inp.pop()
        if hasattr(self.inp[-1], 'read'):
            self.inp[-1] = read_word(self.inp[-1])
        if hasattr(self.inp[-1], 'next'):
            result = self.inp[-1].next()
        else:
            result = self.inp[-1].pop(0)
        self.program.append(result)

    def read_word(self):
        while True:
            while self.program_ctr >= len(self.program):
                self.__getword()
            yield self.program[self.program_ctr]
            self.program_ctr += 1

    def read(self, inp, silent=False):
        self.inp = [inp]
        delim = SPACE
        if not silent: print(self.program_ctr, end='? ', file=self.out)
        for word in self.read_word():
            #print('<%s>' % word, end=' ')
            if word == _RUN:
                if not silent:
                    print(' ok', file=self.out)
                    print(self.program_ctr, end='? ', file=self.out)
                continue
            elif word == '."':
                out = []
                word = self.__getword()
                while word != '"':
                    out.append(self.__getword)
                    word = self.__getword()
                print(' '.join(out), file=self.out)
                continue
            elif word == '': continue
            self.stack.append(word)
            self.lookup()
    def lookup(self, sym=None):
        if sym is None:
            sym = self.stack.pop()
        result = None
        if sym.lower() in self.symbols:
            with redir_stdout(self.out):
                result = self.symbols[sym.lower()](self.stack, self.rstack)
        else:
            result = self.numberp(sym)
            if result is None: raise ValueError("Symbol %r not found" % sym)
            else:
                self.stack.append(result)
        return result

    def numberp(self, sym):
        is_valid = -1 # -1 = undecided, 0 = False, 1 = True
        typ = int
        dot_acceptable = False
        if sym == '': is_valid = 0
        elif not (sym.startswith('-') or sym[0].isdigit()): is_valid = 0
        if is_valid == 0: return None
        else:
            for char in sym[1:]:
                if char.isdigit(): dot_acceptable = True
                elif dot_acceptable and char == '.': typ = float
                elif dot_acceptable and char == 'e': typ = float
                else:
                    return None
            else:
                return typ(sym)
    @classmethod
    def add_symbol(cls, name):
        def _i1(func):
            cls.symbols[name.lower()] = func
            return func
        return _i1

@Reader.add_symbol('J')
def J(stack, rstack):
    stack.append(rstack[-3])

@Reader.add_symbol('R@')
def rAt(stack, rstack):
    stack.append(rstack[-1])

@Reader.add_symbol('I')
def I(stack, rstack):
    stack.append(rstack[-1])

@Reader.add_symbol('R>')
def movP(stack, rstack):
    stack.append(rstack.pop())

@Reader.add_symbol('>R')
def movR(stack, rstack):
    rstack.append(stack.pop())

@Reader.add_symbol('2over')
def _2over(stack, rstack=None):
    d, c, b, a = [stack.pop() for _ in range(4)]
    stack.append(a)
    stack.append(b)
    stack.append(c)
    stack.append(d)
    stack.append(a)
    stack.append(b)

@Reader.add_symbol('2dup')
def _2dup(stack, rstack=None):
    b, a = [stack.pop() for _ in range(2)]
    stack.append(a)
    stack.append(b)
    stack.append(a)
    stack.append(b)

@Reader.add_symbol('2swap')
def _2swap(stack, rstack=None):
    d, c, b, a = [stack.pop() for _ in range(4)]
    stack.append(c)
    stack.append(d)
    stack.append(a)
    stack.append(b)

@Reader.add_symbol('.r')
def stack_print(stack, rstack=None):
    print('<%d>' % len(rstack), end=' ')
    for n in rstack:
        print(n, end=' ')
    print()

@Reader.add_symbol('.s')
def stack_print(stack, rstack=None):
    print('<%d>' % len(stack), end=' ')
    for n in stack:
        print(n, end=' ')
    print()

@Reader.add_symbol('drop')
def drop(stack, rstack=None):
    stack.pop()

@Reader.add_symbol('rot')
def rot(stack, rstack=None):
    n1, n2, n3 = stack.pop(), stack.pop(), stack.pop()
    #a,  b,  c
    stack.extend([n2, n1, n3])

@Reader.add_symbol('dup')
def dup(stack, rstack=None):
    a = stack.pop()
    stack.append(a)
    stack.append(a)

@Reader.add_symbol('over')
def over(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(a)
    stack.append(b)
    stack.append(a)

@Reader.add_symbol('swap')
def swap(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(b)
    stack.append(a)

@Reader.add_symbol('%')
def mod(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(a % b)

@Reader.add_symbol('/')
def div(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(a / b)

@Reader.add_symbol('*')
def mul(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(a * b)

@Reader.add_symbol('-')
def min_(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(a - b)

@Reader.add_symbol('+')
def add(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(a + b)

@Reader.add_symbol('and')
def and_(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(a and b)

@Reader.add_symbol('or')
def or_(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(a or b)

@Reader.add_symbol('.')
def period(stack, rstack=None):
    print(stack.pop(), end=' ')

@Reader.add_symbol('emit')
def emit(stack, rstack=None):
    print(chr(stack.pop()), end='')

@Reader.add_symbol('=')
def eql(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(int(a == b))

@Reader.add_symbol('<')
def lt(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(int(a < b))

@Reader.add_symbol('>')
def gt(stack, rstack=None):
    b, a = stack.pop(), stack.pop()
    stack.append(int(a > b))

@Reader.add_symbol('nop')
def nop(*_):
    pass

@Reader.add_symbol('clear')
def clear(stack, rstack):
    del stack[:]
    del rstack[:]

def init_reader():
    reader = Reader()
    reader.compile(*'0= 0 ='.split(None,1))
    reader.compile(*'0> 0 >'.split(None,1))
    reader.compile(*'0< 0 <'.split(None,1))
    reader.compile('cr', ['10', 'emit'])
    reader.compile('2drop', ['drop', 'drop'])
    reader.compile('false', ['0'])
    reader.compile('true', ['-1'])
    reader.compile('invert', ['0=', 'if', 'true', 'else', 'false', 'then'])
    reader.compile('?dup', 'dup if dup then'.split())
    reader.compile('1+', '1 +'.split())
    reader.compile('1-', '1 -'.split())
    reader.compile('2+', '2 +'.split())
    reader.compile('2-', '2 -'.split())
    reader.compile('2*', '2 *'.split())
    reader.compile('2/', '2 /'.split())
    reader.compile('abs', 'dup 0< if -1 * then'.split())
    reader.compile('negate', '-1 *'.split())
    reader.compile('min', '2dup - 0> if swap then drop')
    reader.compile('max', '2dup - 0< if swap then drop')
    reader.compile('*/', 'rot rot * swap /')
    reader.compile('*/mod', 'rot rot * swap /mod')
    reader.compile('/mod1', '2dup % dup 2swap / rot drop')
    reader.compile('mark>r', 'mark >r')
    reader.compile('arrow', '45 emit 45 emit 62 emit')
    reader.compile('loop0', '0= arrow .s if  98 emit cr else 97 emit cr .s r> .s jmp then')
    reader.compile(*'spaces 0 do 32 emit loop'.split(None, 1))
    reader.compile(*'do swap >r >r begin'.split(None, 1))
    reader.compile('rdrop', 'r> drop')
    reader.compile(*'loop r> 1+ r> 2dup >r >r < invert until rdrop rdrop'.split(None, 1))
    reader.compile('begin', 'markr')
    reader.compile('until', 'invert if jmpr else clrjmp then')
    return reader

if __name__ == '__main__':
    import sys
    reader = init_reader()

    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('file', nargs='?')
    args = parser.parse_args()
    if args.file == '-' or args.file == None:
        fil = sys.stdin
        reader.read(sys.stdin)
    else:
        with open(args.file) as f:
            reader.read(f, silent=True)
