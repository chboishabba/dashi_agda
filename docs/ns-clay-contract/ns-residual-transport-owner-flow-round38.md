# NS Round 38 — residual transport, evidence-indexed HH-bad charge, and orbit fibres

Round 38 implements the concrete highest-alpha consequences of the Round-37 shortest cut rather than adding another terminal wrapper.  The tranche tests the proposed coarse/detail unification directly against the existing NS carriers.

The outcome is a sharper frontier:

- HH-good stretching is proved to descend through the source-vorticity quotient modulo the target vorticity line, with `w cross v` as the division-free residual;
- the finite zero-mass PV operator is proved to annihilate the coarse constant projector and factor through projector detail;
- `Com` is proved to be exactly the oriented odd part of a `Z2`-graded transport;
- HH-bad viscous allocation is made exact on a finite evidence-indexed bad mask, removing an artificial same-object allocation ambiguity;
- occupation and crossing costs are packaged as two distinct finite controls;
- a physically witnessed pre-tax cancellation edge is proved to conserve signed production while reducing positive tax by its transfer amount;
- the physical triad energy-leg action is proved cutoff-stable and the generic finite orbit-fibre pushforward theorem is closed.

None of these finite/algebraic results is promoted to an unconditional periodic Navier--Stokes regularity theorem.

## 1. HH-good depends only on the vorticity-line residual

Define the division-free line residual

```text
delta_v(w) = w cross v.
```

For every scalar `alpha`, Round 38 proves

```text
delta_v(w + alpha v) = delta_v(w).
```

The corrected Round-37 strain action already satisfies

```text
v . S_theta(w) v
  = -(theta . v) theta . (w cross v).
```

Therefore Round 38 proves the stronger quotient statement

```text
v . S_theta(w + alpha v) v
  = v . S_theta(w) v.
```

`SameModuloTargetLine` records this as a proof-bearing relation: if two source vorticities differ by a vector parallel to the target, both `lineResidual` and the stretching scalar agree exactly.  No division by `|v|^2` and no choice of orientation for the target line is required.

For an explicit orthogonal decomposition

```text
w = d + alpha v,
v . d = 0,
```

Lagrange's identity gives

```text
|w cross v|^2 = |v|^2 |d|^2.
```

Combining that with the existing pointwise directional-depletion theorem gives, for unit `theta`,

```text
|v . S_theta(w) v|^2
  <= |v|^4 |d|^2.
```

Thus the source component parallel to the target line is exactly invisible to stretching; the remaining physical HH-good theorem is an estimate on the transported detail.

Sources recorded in the Agda headers:

- Peter Constantin and Charles Fefferman, *Direction of Vorticity and the Problem of Global Regularity for the Navier--Stokes Equations*, DOI `10.1512/iumj.1993.42.42034`.
- Peter Constantin, Charles Fefferman and Andrew J. Majda, *Geometric Constraints on Potentially Singular Solutions for the 3-D Euler Equations*, DOI `10.1080/03605309608821197`.

## 2. Finite PV is literally a detail operator

Round 37 proved, for a zero-mass weighted projector kernel,

```text
sum_y K_y Pi_y
  = sum_y K_y (Pi_y - Pi_x).
```

Round 38 separates the two facts hidden in that equality.  If the coarse field is the constant projector `Pi_x`, then

```text
K Pi_x = Pi_x sum_y K_y = 0.
```

Consequently

```text
K Pi = K (Pi - Pi_x).
```

`FinitePVDetailFactorization` stores both the annihilation theorem and the detail factorization as proof evidence.  This is the finite exact version of

```text
K P_x = 0,
K = K Q_x
```

on the directional projector field.

The literal periodic torus strain-kernel realization, principal-value zero-mass theorem, singular-kernel bound and shell-localized owner estimate remain open.  The new result identifies exactly what that physical theorem has to preserve: the periodic operator must realize this detail factorization rather than merely have a numerically similar scalar envelope.

The additional increment context cites Peter Constantin, Weinan E and Edriss S. Titi, *Onsager's Conjecture on the Energy Conservation for Solutions of Euler's Equation*, DOI `10.1007/BF02099744`.

## 3. `Com` is the odd part of a `Z2`-graded transport

With complementary projections `P,Q`, define

```text
Gamma = P - Q,
Gamma^2 = I.
```

For

```text
T = [[a,b],[c,d]],
```

Round 38 defines

```text
T_even = [[a,0],[0,d]],
T_odd  = [[0,b],[c,0]]
```

and proves

```text
T = T_even + T_odd,
[Gamma,T] = 2 [P,T],
[P,T_even] = 0,
[P,T_odd] = [P,T].
```

It also proves that applying the odd transport is exactly the sum of the two existing cross-channel maps.  Hence the physical A1 realization can discard diagonal transport before the Gram/Cotlar theorem is invoked.

The still-open theorem is now more precise:

```text
physicalOddTransportGramRealization
```

must identify the literal shell odd transport with the Round-35 pair-product Gram cells uniformly in cutoff.  No new diagonal estimate is required.

Source: Tosio Kato and Gustavo Ponce, *Commutator Estimates and the Euler and Navier--Stokes Equations*, DOI `10.1002/cpa.3160410704`.

## 4. HH-bad viscous ownership is exact under an evidence-indexed restriction

Round 37 showed that full shell viscosity already has sufficient scale:

```text
E_bad (nu lambda_q) <= E_bad nu lambda_q^2.
```

The open issue was whether an independently introduced HH-bad charge belonged to the same physical shell/state/bad interval.  Round 38 removes that artificial ambiguity at the finite trajectory level.

Each sample now contains

```text
isBad : Bool,
shellEnergy : Q,
0 <= shellEnergy.
```

Define

```text
E_bad(sample) = if isBad then shellEnergy else 0,
C_bad(sample) = E_bad(sample) nu lambda_q^2.
```

The finite sum satisfies exactly

```text
sum C_bad
  = (sum E_bad) nu lambda_q^2.
```

The aggregate therefore constructs the existing Round-37 full-shell viscous-charge cell directly, and inherits

```text
(sum E_bad) (nu lambda_q) <= sum C_bad
```

and

```text
(sum E_bad) nu
  <= (sum C_bad) lambda_q^-1.
```

So finite HH-bad allocation no longer requires a separately supplied `chargeContainsFullShellViscosity` witness.  The genuine physical seam is now:

1. identify the actual trajectory's evidence-indexed HH-bad predicate with the finite mask;
2. prove the actual HH-bad gain against the restricted charge;
3. pass the restriction through the real-time/continuum limit;
4. separately prove Luo's upper critical-smallness condition.

The last condition is not implied by the lower coercivity theorem.

Sources: Xiaoyutao Luo, DOI `10.1007/s00021-019-0411-z`, arXiv DOI `10.48550/arXiv.1803.05569`; Hajer Bahouri, Jean-Yves Chemin and Raphael Danchin, DOI `10.1007/978-3-642-16830-7`.

## 5. HH-bad occupation and crossings are two different controls

For bad samples with defect at least `theta`, Round 38 proves

```text
repeatedCost theta badSamples
  <= sum realizedDefect.
```

If the latter is controlled by an integrated defect charge, then occupation cost is controlled by that integral.

Independently, Round 37 already proved that hysteretic crossings with minimum jump `delta` satisfy

```text
repeatedCost delta crossings
  <= positiveVariation.
```

`HHBadTwoCoordinateControl` packages both inequalities without conflating them.  This is the finite precursor of the proposed BV/layer-cake picture: duration/occupation and transition count are different coordinates of the bad set.

The physical integrated-defect and positive-variation estimates remain open.

## 6. A proved cancellation edge can improve the positive tax

For a nonnegative owner balance `L`, nonpositive owner balance `R`, and a physically justified transfer `tau` satisfying

```text
0 <= tau <= L,
tau <= -R,
```

define

```text
L' = L - tau,
R' = R + tau.
```

Round 38 proves exactly

```text
L' + R' = L + R,
0 <= L',
R' <= 0,
L = L' + tau.
```

Thus the signed total is conserved while the positive tax drops by exactly `tau`.

`PhysicalCancellationEdge` names source and target in the repository's literal nine-owner `TaxOwner` type and requires an explicit physical identity witnessing that the edge is permitted.  This is a local theorem for a genuine network optimizer; `physicalNineOwnerCancellationNetworkConstructed` remains false until actual cross-owner identities and capacities are proved.

This matters only upstream of the final positive tax.  No hidden cancellation is used to evade the final strict viscosity absorption theorem.

## 7. F4 orbit action and fibre pushforward

For every physical triad incidence, Round 38 proves the existing `pEnergyLeg` and `qEnergyLeg` maps are involutive on their physical lattice labels.  More importantly, they preserve the literal cutoff carrier:

```text
tau in cutoff => pEnergyLeg(tau) in cutoff,
tau in cutoff => qEnergyLeg(tau) in cutoff.
```

For an incidence already present in `physicalTriadEnumeration N`, enumeration completeness therefore produces listed representatives of both companion energy legs.

A separate proof-relevant finite theorem proves that if a finite incidence list is exactly the flattening of its actual fibres, then

```text
sum_{i in incidences} F(i)
  = sum_{fibre} sum_{i in fibre} F(i).
```

No division by `|S3 x C2|` appears, so stabilizers and degenerate packets are handled by the actual fibres rather than a free-action assumption.

This advances but does not finish F4.  The remaining theorem is the concrete construction

```text
literalGalerkinOrbitFibrePartition
```

identifying the actual Galerkin nonlinear-power incidence list, with its exact multiplicity convention, with these physical orbit fibres.  Once that partition is built, the already-proved per-triad three-leg cancellation can be pushed through the fibre theorem.

Sources: Jean Leray, DOI `10.1007/BF02547354`; Roger Temam, DOI `10.1090/chel/343`.

## 8. Why no generic `ResidualGramFamily` was added

The coarse/detail pattern is now real in both `Com` and HH-good, but Round 38 deliberately does **not** add the proposed generic residual-transport abstraction.  The physical periodic PV owner estimate and the physical odd-transport Gram realization are still open.  Building a common abstraction before either physical estimate works would move symbols rather than close mathematics.

The proof-engineering boundary therefore remains:

```text
literal physical carrier
  -> CanonicalAnalyticPhysicalLeaves
  -> analytic reducers / continuation.
```

New abstraction above that boundary is justified only if it removes a concrete duplication in a proved physical construction.

## Revised highest-alpha frontier

The next frontier after Round 38 is narrower:

1. **A3/A4 — literal periodic PV detail realization.**  Construct the torus strain kernel/PV operator on the physical solution, prove its zero-mass/detail factorization, then integrate the already-proved `|v|^4 |detail|^2` depletion with uniform shell constants to obtain `physicalHHGoodOwnerEstimate`.
2. **A6/A8 — physical restricted HH-bad gain.**  Identify the trajectory bad mask, prove the gain against the restricted viscous charge, prove the separate Luo upper critical-smallness estimate, and close the integrated-defect/positive-variation controls if dynamic switching is used.
3. **A1/A2 — physical odd-transport Gram realization.**  Identify the literal shell odd transport with the two Round-35 Gram/Cotlar pair products.  The even transport is now algebraically irrelevant.
4. **F4 — literal Galerkin orbit-fibre partition.**  Construct the actual incidence-to-packet partition and use the finite pushforward plus existing three-leg cancellation.
5. **Owner reserve.**  Instantiate the remaining physical owners, use only proved cancellation edges before taxation, and run the certified reserve optimizer.  A rigorously certified minimum `sum eta >= 1` remains a falsification of this owner architecture rather than a tuning failure.

Only after those physical producers close should the downstream `CanonicalAnalyticPhysicalLeaves`, maximal-time contradiction, finite/infinite promotion and submission audit be treated as the critical path.
