# Millennium residual descent classifier

This tranche imports the observer/descent lesson from the literal RH work into
BSD, Hodge and P-versus-NP without promoting any conjecture.

The shared residual taxonomy is:

```text
representation/descent wall
missing-information/repair wall
domain-theorem wall
coverage wall
```

The key no-promotion law is that postcomposition cannot recover a
consumer-relevant distinction already collapsed by an observer.

## Hodge

The existing `HodgeConjectureAtCodimension` is now shown to be equivalent to
a `HodgeCycleClassReopening`:

```text
RationalHodgeClass
  -> Cycle
  -> cycleClass(reopened class) = original class
```

This is an exact reframing, not a new algebraicity theorem.  It identifies the
literal Hodge obligation as a reopening/lifting problem through the cycle-class
observer.

Current cut:

```text
H1 representation/cohomology substrate
H2 algebraic reopening/lift
H3 overlap/gluing descent
H4 global coverage of all rational Hodge classes
```

## Birch--Swinnerton-Dyer

The rank conjecture is compiled into a two-observer weld over one elliptic
curve:

```text
analytic observer   -> analyticRank
arithmetic observer -> freeRank
required weld       -> equality
```

The compiler is reversible: an existing BSD rank conjecture gives the weld,
and the weld gives the BSD rank conjecture.  No unconditional weld is
manufactured.

Current cut:

```text
B1 local-factor -> global-L same-object construction
B2 analytic continuation / functional equation
B3 analytic-rank <-> Mordell--Weil-rank weld
B4 leading-term invariant coverage / identification
```

## P versus NP

`UniformObserverNonDescent` formalises the negative proof grammar:

```text
for every candidate observer o
  produce x,y with
    o(x) = o(y)
    consumer(x) != consumer(y)

=> no candidate observer factors the consumer
```

A separate theorem proves the collision survives arbitrary downstream
postcomposition/recharting.

This is deliberately weaker than P != NP.  The still-unpaid meta-obligation is
that the candidate family faithfully covers every deterministic polynomial-time
classical algorithm/representation relevant to the selected NP-complete
consumer.

Current cut:

```text
P1 exact classical computation/witness representation
P2 polynomial consumer-sufficient recovery
   OR uniform non-descent obstruction
P3 cost-model adequacy / same-object execution semantics
P4 NP-complete / Cook--Levin coverage
```

## Authority boundary

The tranche records as false:

```text
Hodge algebraic lift constructed
BSD rank weld constructed unconditionally
all polynomial algorithms covered by obstruction family
any of the three Millennium problems solved here
```

Source-written only in this connector session; no fresh Agda/kernel receipt is
claimed.


## 2026-09-19 payable-formalisation continuation

The branch is now stacked directly on the canonical #999 observer/descent/gluing
spine rather than on master.  The following requested debts are source-written:

- cost-aware decision factorisation, including explicit observer and downstream
  polynomial-time obligations;
- a sized polynomial-classical observer carrier with representation-size,
  construction-cost and recovery-cost polynomial envelopes;
- exact binary decision-to-search self-reduction;
- a finite-variable Boolean SAT instantiation with restriction correctness,
  satisfiability splitting, solution lifting and exactly one SAT decision query
  per remaining variable;
- a prime-indexed elliptic local-data carrier with explicit good,
  multiplicative-bad and additive-bad branches, plus a theorem identifying every
  finite good-prime local factor as a restriction of that global family;
- a projective-space hyperplane-power reopening compiler: one-dimensional
  H^(p,p) spanning plus an algebraic hyperplane-power cycle compiles to the
  literal HodgeConjectureAtCodimension.

The remaining known-mathematics/formalisation min-cuts are now sharper:

```text
P-vs-NP / Cook-Levin
  arbitrary Configuration : Set
    -> missing finite tape/state/configuration encoding
    -> Boolean cell variables / clauses / polynomial bit size
  (run <-> finite tableau is already paid)

Hodge / CP^n
  finite hyperplane-power basis pattern                    PAID
  hyperplane-power spanning -> literal reopening compiler PAID
  actual CP^n geometric carrier                           OPEN
  singular/de Rham same-object identification             OPEN
  actual hyperplane cycle-class theorem                   OPEN

BSD
  finite Euler algebra / finite Dirichlet multiplicativity PAID
  checked small-prime Frobenius rows                        PAID
  all-prime good/bad local-data carrier                     PAID
  actual all-prime arithmetic inhabitant                    OPEN
  Q*/Q*^2 and Q_v global 2-descent realization              OPEN
  infinite Dirichlet/Euler convergence                      OPEN
  actual modular Mellin realization                         OPEN
```

These are not promoted to the Millennium conclusions.  The irreducible walls
remain general BSD rank/leading-term-Sha, general Hodge algebraicity, and either
a polynomial classical algorithm for an NP-complete language or a genuine
uniform lower bound excluding all such algorithms.
