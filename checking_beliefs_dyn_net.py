#!/usr/local/bin/python3
from z3 import *

fp = Fixedpoint()

dst = BitVec('dst', 3)
src = BitVec('src', 3)
dst_next = BitVec('dst_next', 3)
src_next = BitVec('src_next', 3)

fp.declare_var(dst, src, dst_next, src_next)

rels = {}

for c in ['A', 'R1', 'R2', 'R3', 'B', 'D']:
    f = Function(c, BitVecSort(3), BitVecSort(3), BoolSort())
    rels[c] = f
    fp.register_relation(f)
    fp.set_predicate_representation(f, 'doc')

# Guards
g12 = And(Extract(2, 1, dst) == 0b10, Extract(2, 1, dst) == 0b01)
g13 = And(Not(g12), Extract(2, 2, dst) == 0b1)
g2b = Extract(2, 1, dst) == 0b10
g3d = Extract(2, 2, src) == 0b1
g32 = And(Not(g3d), Extract(2, 2, dst) == 0b1)
ld = And(src_next == src, dst_next == dst)
set0 = And(src_next == src, dst_next == dst & 0b101)

# Relations
fp.rule(rels['R1'](dst_next, src_next), And(rels['R2'](dst, src), g12, ld))
fp.rule(rels['R1'](dst_next, src_next), And(rels['R3'](dst, src), g13, ld))
fp.rule(rels['R2'](dst_next, src_next), And(rels['B'](dst, src), g2b, ld))
fp.rule(rels['R3'](dst_next, src_next), And(rels['D'](dst, src), g3d, ld))
fp.rule(rels['R3'](dst_next, src_next), And(rels['R2'](dst, src), g32, set0))
fp.rule(rels['A'](dst, src), rels['R1'](dst, src))

# Starting Point
fp.fact(rels['B'](dst, src))

if fp.query(rels['A'](dst, src), rels['R3'](dst, src)):
    print(fp.get_answer())
