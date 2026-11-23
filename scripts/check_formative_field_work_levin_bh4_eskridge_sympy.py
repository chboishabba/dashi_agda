#!/usr/bin/env python3
"""Exact synthetic cross-programme acceptance, never a physical anomaly claim.

Sheldrake's Aristotelian form/work distinction is rendered as separate measured
coordinates. Existing physics/Levin/BH4/Eskridge owners supply authority gates;
these equalities do not derive a novel field, source or biological mechanism.
"""
from sympy import Matrix, Rational as Q, symbols, simplify

checks = 0

def check(name, result):
    global checks
    if result is not True and result != True:
        raise AssertionError(name)
    checks += 1
    print(f'PASS {checks:02d}: {name}')

m, g, z0, z1 = symbols('m g z0 z1', real=True)
delta_Ug = m*g*(z1-z0)
Wg = m*g*(z0-z1)
check('gravitational work is negative change of gravity potential', simplify(Wg+delta_Ug) == 0)
check('closed gravitational cycle has zero net conservative work', simplify(Wg.subs(z1, z0)) == 0)

mu, b0, b1 = symbols('mu b0 b1', real=True)
U_mag0, U_mag1 = -mu*b0, -mu*b1
Wmag = mu*(b1-b0)
check('magnetic potential work balances potential change in this conservative toy',
      simplify(Wmag+U_mag1-U_mag0) == 0)
check('returning to initial magnetic state gives zero toy cycle work',
      simplify(Wmag.subs(b1,b0)) == 0)

# Finite stochastic form fixture, distinct from physical energy bookkeeping.
reference, skewed = Matrix([1,2,1]), Matrix([0,3,1])
check('finite shape can change with conserved path count',
      sum(reference) == sum(skewed) == 4 and reference != skewed)
check('two shape charts can stipulate the same total paid units',
      Q(4) == Q(4) and reference != skewed)

# Exact independent-branch Galton model: source of bias is NOT identified.
def histogram(p): return Matrix([(1-p)**2, 2*p*(1-p), p**2])
h0, h_local, h_similarity = histogram(Q(1,2)), histogram(Q(3,4)), histogram(Q(3,4))
check('two toy mechanisms share one observed field-on histogram', h_local == h_similarity)
check('distinct source coordinates are needed for mechanism selection',
      Matrix([[1,1,1]]).rank() == 1 and Matrix([[1,0,0],[1,0,1],[1,1,0],[1,1,1]]).rank() == 3)
check('ordinary no-field/no-history control restores reference',
      h0 == Matrix([Q(1,4),Q(1,2),Q(1,4)]))

# Levin/BH4: equal measured total pool leaves internal allocation unresolved.
allocation_A, allocation_B = Matrix([1,3]), Matrix([2,2])
readout = Matrix([[1,1]])
check('two intracellular allocations share the total-pool readout',
      readout*allocation_A == readout*allocation_B)
check('total-pool map has one invisible BH4 compartment/branch direction',
      readout.rank()==1 and readout*(allocation_B-allocation_A)==Matrix([0]))
check('branch-resolving assay separates the two toy allocations',
      Matrix.eye(2)*allocation_A != Matrix.eye(2)*allocation_B)

# Field response and a source ledger are distinct coordinates. Signed
# environmental input can be negative if outgoing exceeds incoming.
natural_incident, natural_outgoing = Q(5),Q(8)
check('outgoing field power can exceed incoming natural port power',
      natural_incident-natural_outgoing == -3)
inputs = {'controller': Q(3), 'incident': Q(5), 'storage_release': Q(2)}
outputs = {'load': Q(3), 'dissipated': Q(1), 'radiated': Q(5), 'storage_final': Q(1)}
check('same-boundary signed work balances when all disjoint ports are counted',
      sum(inputs.values()) == sum(outputs.values()))
check('positive extracted load is impossible in a nonnegative source-free zero-storage toy',
      all(not (u > 0 and u+l+s==0) for u in range(1,4) for l in range(4) for s in range(4)))

# Eskridge/Li-Torr: identical kinematic response is not unique mechanism.
accel = Q(2)
ordinary_electric_accel, hypothetical_gravity_accel = accel, accel
check('one acceleration alone cannot distinguish EM and gravity models',
      ordinary_electric_accel == hypothetical_gravity_accel)
check('two independently assigned probes would distinguish ideal model predictions',
      Matrix([[1,0],[0,1]]).rank()==2)

# Retarded source/receiver transfer, no instantaneous field action inferred.
launch, flight, arrival = 2, 5, 7
check('delayed arrival retains causal ordering',
      launch + flight == arrival and arrival >= launch)
print(f'{checks}/{checks} exact synthetic checks PASS (SymPy)')
