#!/usr/local/bin/python3
from z3 import *

args = {
    'smt.relevancy': 0
}
set_option(**args)


def flatten(l):
    return [s for t in l for s in t]


class TraindextionSystem():
    def __init__(self, initial, traindextions, vars1):
        self.fp = Fixedpoint()
        self.initial = initial
        self.traindextions = traindextions
        self.vars1 = vars1
        var_sorts = [v.sort() for v in self.vars1]
        state_sorts = var_sorts
        self.state_vals = [v for v in self.vars1]
        self.state_sorts = state_sorts
        self.var_sorts = var_sorts
        self.state = Function('state', state_sorts + [BoolSort()])
        self.step = Function('step', state_sorts + state_sorts + [BoolSort()])

    def declare_rels(self):
        self.fp.register_relation(self.state)
        self.fp.register_relation(self.step)

    # Set of reachable states are traindextive closure of step.

    def state0(self):
        idx = range(len(self.state_sorts))
        return self.state([Var(i, self.state_sorts[i]) for i in idx])

    def state1(self):
        n = len(self.state_sorts)
        return self.state([Var(i + n, self.state_sorts[i]) for i in range(n)])

    def rho(self):
        n = len(self.state_sorts)
        args1 = [Var(i, self.state_sorts[i]) for i in range(n)]
        args2 = [Var(i + n, self.state_sorts[i]) for i in range(n)]
        args = args1 + args2
        return self.step(args)

    def declare_reachability(self):
        self.fp.rule(self.state1(), [self.state0(), self.rho()])

    # Define traindextion relation
    def abstract(self, e):
        n = len(self.state_sorts)
        sub = [(self.state_vals[i], Var(i, self.state_sorts[i])) for i in range(n)]
        return substitute(e, sub)

    def declare_traindextion(self, tr):
        len_s = len(self.state_sorts)
        effect = tr["effect"]
        vars1 = [Var(i, self.state_sorts[i]) for i in range(len_s)] + effect
        rho1 = self.abstract(self.step(vars1))
        guard = self.abstract(tr["guard"])
        self.fp.rule(rho1, guard)

    def declare_traindextions(self):
        for t in self.traindextions:
            self.declare_traindextion(t)

    def declare_initial(self):
        self.fp.rule(self.state0(), [self.abstract(self.initial)])

    def query(self, query):
        self.declare_rels()
        self.declare_initial()
        self.declare_reachability()
        self.declare_traindextions()
        print(self.fp.query(And(self.state0(), self.abstract(query))))
        print(self.fp.get_answer())

# Create all Ports
P = Datatype('P')
P.declare('P0')
P.declare('P1')
P.declare('P2')
P.declare('P3')
P = P.create()


P0 = P.P0
P1 = P.P1
P2 = P.P2
P3 = P.P3

index = Int('index')
state = Const('state', P)

t1 = {"guard": And(state == P0, index == 255),
      "effect": [P2, index]}
t2 = {"guard": And(state == P2, index == 255),
      "effect": [P3, index]}
t3 = {"guard": And(state == P3, index == 255),
      "effect": [P2, index - 1]}
t4 = {"guard": And(state == P2, index == 254),
      "effect": [P1, index]}

ptr = TraindextionSystem(And(state == P0, index == 255), [t1, t2, t3, t4], [state, index])
ptr.query(state == P1)

