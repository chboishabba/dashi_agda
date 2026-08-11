# NS Round 38 — residual transport, evidence-indexed HH-bad charge, and incidence permutations

Round 38 implements the concrete highest-alpha consequences of the Round-37 shortest cut rather than adding another terminal wrapper. The tranche tests the proposed coarse/detail unification directly against the existing NS carriers.

The outcome is a sharper frontier:

- HH-good stretching descends through the source-vorticity quotient modulo the target vorticity line, with `w cross v` as the division-free residual;
- a finite zero-mass PV operator annihilates the coarse constant projector and factors through projector detail;
- periodic kernel zero mass is reduced to the already-formalized zero-Fourier-mode criterion, so it is not an independent assumption once the literal strain-kernel realization exists;
- `Com` is exactly the oriented odd part of a `Z2`-graded transport;
- HH-bad viscous allocation is exact on a finite evidence-indexed bad mask;
- occupation and crossing costs are retained as two distinct finite controls;
- a physically witnessed pre-tax cancellation edge conserves signed production while reducing positive tax by its transfer amount;
- the physical triad energy-leg action is cutoff-stable, and the raw ordered physical-incidence nonlinear power is proved zero by three exact enumeration permutations and the existing three-leg cancellation.

None of these finite/algebraic results is promoted to unconditional periodic Navier--Stokes regularity.

## 1. HH-good depends only on the vorticity-line residual

Define

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

Hence

```text
v . S_theta(w + alpha v) v
  = v . S_theta(w) v.
```

`SameModuloTargetLine` records this as a proof-bearing quotient relation. No division by `|v|^2` and no orientation choice for the target line is required.

For an orthogonal decomposition

```text
w = d + alpha v,
v . d = 0,
```

Lagrange's identity gives exactly

```text
|w cross v|^2 = |v|^2 |d|^2.
```

Combining that with the existing pointwise directional-depletion theorem gives, for unit `theta`,

```text
|v . S_theta(w) v|^2
  <= |v|^4 |d|^2.
```

Thus the source component parallel to the target line is exactly invisible to stretching. The remaining HH-good theorem is an analytic estimate on the transported detail.

Sources:

- Peter Constantin and Charles Fefferman, *Direction of Vorticity and the Problem of Global Regularity for the Navier--Stokes Equations*, DOI `10.1512/iumj.1993.42.42034`.
- Peter Constantin, Charles Fefferman and Andrew J. Majda, *Geometric Constraints on Potentially Singular Solutions for the 3-D Euler Equations*, DOI `10.1080/03605309608821197`.

## 2. PV cancellation is a detail factorization, and periodic zero mass has a Fourier criterion

Round 37 proved

```text
sum_y K_y Pi_y
  = sum_y K_y (Pi_y - Pi_x)
```

for a zero-mass finite weighted projector kernel. Round 38 separates the two facts:

```text
K Pi_x = Pi_x sum_y K_y = 0,
K Pi = K (Pi - Pi_x).
```

`FinitePVDetailFactorization` therefore gives the exact finite `K P_x = 0`, `K = K Q_x` skeleton.

The repository already has exact periodic character/multiplier integration with

```text
Khat(0) = integral K.
```

Round 38 packages the consequence

```text
Khat(0) = 0  =>  integral K = 0
```

as `zeroModeMultiplierForcesKernelMassZero`, and specializes the shape as `periodicStrainKernelMassZeroFromFourierCriterion`.

This removes one artificial A3 obligation: once the physical torus strain kernel is realized by the existing periodic character carrier and its literal zero-mode multiplier is proved, zero mass follows. Still open are the same-object strain-kernel realization, the principal-value/singular-kernel estimate, shell localization, and the owner coefficient.

Additional source: Peter Constantin, Weinan E and Edriss S. Titi, *Onsager's Conjecture on the Energy Conservation for Solutions of Euler's Equation*, DOI `10.1007/BF02099744`.

## 3. `Com` is the odd part of a `Z2`-graded transport

With complementary projections `P,Q`, define

```text
Gamma = P - Q,
Gamma^2 = I.
```

For `T=[[a,b],[c,d]]`, Round 38 defines

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

Thus A1 only needs the literal shell odd transport realized by the existing Round-35 pair-product Gram/Cotlar cells. No diagonal estimate survives.

Source: Tosio Kato and Gustavo Ponce, *Commutator Estimates and the Euler and Navier--Stokes Equations*, DOI `10.1002/cpa.3160410704`.

## 4. HH-bad dissipation is restricted by evidence, not allocated afterward

For each finite trajectory sample define

```text
E_bad(sample) = if isBad then shellEnergy else 0,
C_bad(sample) = E_bad(sample) nu lambda_q^2.
```

Round 38 proves

```text
sum C_bad
  = (sum E_bad) nu lambda_q^2
```

exactly. The aggregate therefore instantiates the Round-37 full-shell charge and inherits

```text
(sum E_bad) (nu lambda_q) <= sum C_bad
```

and

```text
(sum E_bad) nu
  <= (sum C_bad) lambda_q^-1.
```

Finite same-object allocation is now true by construction. The real A6/A8 seams are: identify the actual trajectory bad predicate with this evidence mask, prove the physical bad gain against the restricted charge, pass the restriction through real time/continuum, and separately prove Luo's upper critical-smallness condition.

Sources: Xiaoyutao Luo, DOI `10.1007/s00021-019-0411-z`, arXiv DOI `10.48550/arXiv.1803.05569`; Hajer Bahouri, Jean-Yves Chemin and Raphael Danchin, DOI `10.1007/978-3-642-16830-7`.

## 5. Occupation and crossings form a two-coordinate bad-region control

For bad samples with defect at least `theta`, Round 38 proves

```text
repeatedCost theta badSamples
  <= sum realizedDefect.
```

If the latter is charged to an integrated defect quantity, occupation cost is controlled by that integral. Independently, Round 37 already proved

```text
repeatedCost delta crossings
  <= positiveVariation
```

for hysteretic good-to-bad entrances. `HHBadTwoCoordinateControl` packages both without identifying duration with transition count. The continuum BV/layer-cake realization remains open.

## 6. A proved cancellation edge reduces the pre-tax positive mass exactly

For balances `L>=0`, `R<=0` and a physically justified transfer `tau` satisfying

```text
0 <= tau <= L,
tau <= -R,
```

define

```text
L' = L - tau,
R' = R + tau.
```

Round 38 proves

```text
L' + R' = L + R,
0 <= L',
R' <= 0,
L = L' + tau.
```

`PhysicalCancellationEdge` names source and target in the literal nine-owner `TaxOwner` type and requires a physical identity for that edge. So a proved edge can improve the reserve before the positive tax, but arbitrary cross-owner reallocation is impossible by type. The actual nine-owner cancellation network remains open.

## 7. F4: exact permutations give a factor-six global incidence cancellation

The two energy-leg maps used by the exact three-leg cancellation are now proved involutive on the proof-bearing physical incidences and cutoff-stable. Round 38 then upgrades them, together with `swapTriad`, to exact list permutations of the complete duplicate-free physical cutoff enumeration:

```text
map pEnergyLeg physicalTriadEnumeration_N
  <~> physicalTriadEnumeration_N,

map qEnergyLeg physicalTriadEnumeration_N
  <~> physicalTriadEnumeration_N,

map swapTriad physicalTriadEnumeration_N
  <~> physicalTriadEnumeration_N.
```

The proof reuses the Round-35 K-free `Unique`/membership-to-permutation machinery; no proof irrelevance or free group action is introduced.

Let `Ordered(tau)` be the raw ordered signed physical incidence power and `Pair(tau)` the existing symmetrized ordered-pair power. Existing local algebra gives

```text
Pair(tau) = Ordered(tau) + Ordered(swap tau).
```

Permutation invariance therefore gives

```text
sum Pair = 2 sum Ordered.
```

Likewise the `pEnergyLeg` and `qEnergyLeg` permutations give

```text
sum threeLegPower
  = 3 sum Pair
  = 6 sum Ordered.
```

But Round 37 already proved every `threeLegPower(tau)=0`, hence

```text
sum threeLegPower = 0.
```

Over the rational carrier, multiplication by `1/6` yields the new theorem

```text
literalOrderedGalerkinIncidencePowerZero :
  sum_{tau in physicalTriadEnumeration_N} Ordered(tau) = 0.
```

This is stronger than the earlier orbit-fibre skeleton and automatically handles stabilizers because it works with actual list permutations. The only remaining F4 same-object seam is now

```text
literalConvectionPairingEqualsOrderedIncidenceFold
```

including the exact Fourier normalization/multiplicity convention. No additional nonlinear cancellation theorem is needed after that equality.

Sources: Jean Leray, DOI `10.1007/BF02547354`; Roger Temam, DOI `10.1090/chel/343`.

## 8. Why no generic `ResidualGramFamily` was added

The common residual-transport pattern is now real in both `Com` and HH-good, but the physical periodic PV estimate and physical odd-transport Gram realization are still open. A generic abstraction before either works would move symbols rather than close mathematics. Round 38 therefore deliberately leaves that abstraction out.

The proof-engineering boundary remains

```text
literal physical carrier
  -> CanonicalAnalyticPhysicalLeaves
  -> analytic reducers / continuation.
```

## Revised highest-alpha frontier

1. **A3/A4 — literal periodic PV detail realization:** realize the torus strain kernel on the physical solution, prove its zero-mode multiplier and hence zero mass, identify the PV/detail representation, then integrate the exact `|v|^4 |detail|^2` depletion with uniform shell constants to obtain `physicalHHGoodOwnerEstimate`.
2. **A6/A8 — physical restricted HH-bad gain:** identify the trajectory bad mask, prove gain against the restricted viscous charge, prove the separate Luo upper critical-smallness estimate, and close integrated-defect/positive-variation bounds if switching is used.
3. **A1/A2 — physical odd-transport Gram realization:** identify the literal shell odd transport with the two Round-35 Gram/Cotlar pair products. The even transport is algebraically irrelevant.
4. **F4 — one same-object equality remains:** prove the actual Galerkin convection/energy pairing equals the now-cancelled ordered physical-incidence fold.
5. **Owner reserve:** instantiate remaining physical owners, use only proved cancellation edges before taxation, and run the certified reserve optimizer. A certified minimum `sum eta >= 1` remains a falsification of this owner architecture.

Only after these physical producers close should the downstream `CanonicalAnalyticPhysicalLeaves`, maximal-time contradiction, continuum promotion and submission audit become the critical path.
