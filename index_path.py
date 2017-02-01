#!/usr/local/bin/python3
from z3 import *

fp = Fixedpoint()
args = {
    'fixedpoint.pdr.farkas': True,
    'fixedpoint.datalog.generate_explanations': True
}
set_option(**args)

bvsort = BitVecSort(8)
index = BitVec('index', bvsort)
index_next = BitVec('index_next', bvsort)

fp.declare_var(index, index_next)

rels = {}

for c in ['A', 'H', 'SF', 'B']:
    f = Function(c, bvsort, BoolSort())
    rels[c] = f
    fp.register_relation(f)

ghsf = And(index == 255)
ghb = And(Not(ghsf), index == 254)
gsfh = And(index == 255)

dec_index = index_next == index - 1
copy_index = index_next == index

# Relations
fp.rule(rels['SF'](index_next), And(rels['H'](index), ghsf, copy_index))
fp.rule(rels['B'](index_next), And(rels['H'](index), ghb, copy_index))
fp.rule(rels['H'](index_next), And(rels['SF'](index), gsfh, dec_index))
fp.rule(rels['H'](index), rels['A'](index))

fp.fact(rels['A'](index))

#print(fp)

print(fp.query(rels['B'](index)))
print(fp.get_answer())

# doesn't work -> query A -> SF -> B
print(fp.query(rels['SF'](index), rels['B'](index)))
print(fp.get_answer())

# work -> query A -> SF
print(fp.query(rels['SF'](index)))
print(fp.get_answer())

