# NS Round 38 — residual transport, evidence-indexed HH-bad charge, and incidence permutations

Round 38 implements the concrete highest-alpha consequences of the Round-37 shortest cut. It deliberately avoids another terminal wrapper: every new module either proves finite algebra needed by a physical producer, proves an exact same-carrier identification, or narrows an analytic theorem by removing a false extra obligation.

No result in this tranche is promoted to unconditional periodic Navier--Stokes regularity.

## 1. HH-good: the local physical smallness is now inside the literal strain scalar

For source vorticity `w` and target vorticity `v`, define the division-free target-line residual

```text
delta_v(w) = w cross v.
```

Round 38 proves for every scalar `alpha`

```text
delta_v(w + alpha v) = delta_v(w)
```

and, using the corrected Round-37 strain action,

```text
v . S_theta(w + alpha v) v
  = v . S_theta(w) v.
```

Thus stretching descends exactly through the source quotient modulo the target vorticity line. The discarded parallel component is not merely small; it is invisible.

For an orthogonal decomposition

```text
w = d + alpha v,
v . d = 0,
```

Lagrange's identity gives

```text
|w cross v|^2 = |v|^2 |d|^2,
```

hence, for unit separation direction `theta`,

```text
|v . S_theta(w) v|^2 <= |v|^4 |d|^2.
```

The next module connects this to the repository's actual amplitude-weighted physical vorticity pair. If

```text
omega_s = a xi,
omega_t = b eta,
|xi|=|eta|=1,
Theta(xi,eta) <= delta,
```

then the existing physical defect identity yields

```text
|omega_s cross omega_t|^2 = a^2 b^2 Theta,
|omega_t|^2 = b^2,
```

and Round 38 proves

```text
|omega_t . S_theta(omega_s) omega_t|^2
  <= delta * a^2 * b^4.
```

So neither the directional factor nor the good-set small parameter remains an A3/A4 mystery. The remaining work is periodic PV/shell/time integration of an already-thresholded physical nonlinear quantity.

Sources recorded in the Agda headers:

- Peter Constantin and Charles Fefferman, *Direction of Vorticity and the Problem of Global Regularity for the Navier--Stokes Equations*, DOI `10.1512/iumj.1993.42.42034`.
- Peter Constantin, Charles Fefferman and Andrew J. Majda, *Geometric Constraints on Potentially Singular Solutions for the 3-D Euler Equations*, DOI `10.1080/03605309608821197`.
- Xiaoyutao Luo, *A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal Localization*, DOI `10.1007/s00021-019-0411-z`, arXiv DOI `10.48550/arXiv.1803.05569`.

## 2. The nonzero Fourier strain multiplier is now derived from Biot--Savart

Round 37's corrected angular symbol is no longer left disconnected from the repository's exact Biot--Savart velocity. For every nonzero projection mode,

```text
u_k = |k|^-2 (k cross omega_k)
```

under the repository's absorbed Fourier phase convention. Round 38 defines the symmetric strain multiplier directly from that velocity,

```text
S_k(omega)
  = -1/2 [ k tensor u_k + u_k tensor k ],
```

and proves

```text
S_k(omega)
  = |k|^-2 S_ang,k(omega).
```

Consequently

```text
v . S_k(omega) v
  = - |k|^-2 (k . v) k . (omega cross v).
```

This closes the nonzero modewise strain-multiplier identification. The zero mode is intentionally not smuggled through `ProjectionMode`; the total periodic multiplier must assign zero there explicitly.

Sources:

- J. Thomas Beale, Tosio Kato and Andrew Majda, *Remarks on the Breakdown of Smooth Solutions for the 3-D Euler Equations*, DOI `10.1007/BF01240221`.
- Constantin--Fefferman, DOI `10.1512/iumj.1993.42.42034`.

## 3. PV cancellation is literally a detail factorization

For the finite projector kernel, Round 37 proved

```text
sum_y K_y Pi_y
  = sum_y K_y (Pi_y - Pi_x)
```

under zero mass. Round 38 separates the two structural facts:

```text
K Pi_x = 0,
K Pi = K (Pi - Pi_x).
```

This is the exact finite `K P_x = 0`, `K = K Q_x` skeleton proposed by the residual-transport picture.

The existing periodic character/multiplier machinery already proves

```text
Khat(0) = integral K.
```

Round 38 therefore proves the reusable criterion

```text
Khat(0)=0  =>  integral K=0.
```

Hence zero mass is no longer an independent analytic hypothesis once the literal torus strain kernel is realized in that character carrier and its zero Fourier mode is identified.

What remains genuinely physical is:

```text
literal periodic strain-kernel/character realization
  -> total multiplier with zero mode = 0
  -> principal-value/detail representation
  -> singular-kernel estimate
  -> shell/time localization
  -> physicalHHGoodOwnerEstimate.
```

Additional source: Peter Constantin, Weinan E and Edriss S. Titi, *Onsager's Conjecture on the Energy Conservation for Solutions of Euler's Equation*, DOI `10.1007/BF02099744`.

## 4. `Com` is exactly the odd part of a `Z2`-graded transport

With complementary projections `P,Q`, Round 38 defines

```text
Gamma = P - Q,
Gamma^2 = I,
```

and for `T=[[a,b],[c,d]]`

```text
T_even = [[a,0],[0,d]],
T_odd  = [[0,b],[c,0]].
```

It proves

```text
T = T_even + T_odd,
[Gamma,T] = 2[P,T],
[P,T_even] = 0,
[P,T_odd] = [P,T].
```

Thus the physical A1 theorem only needs to identify the literal shell odd transport with the existing Round-35 pair-product Gram/Cotlar cells. Diagonal transport is mathematically irrelevant before estimation.

Source: Tosio Kato and Gustavo Ponce, *Commutator Estimates and the Euler and Navier--Stokes Equations*, DOI `10.1002/cpa.3160410704`.

## 5. HH-bad dissipation is restricted by evidence instead of allocated afterward

For each finite bad/good trajectory sample define

```text
E_bad(sample) = if isBad then shellEnergy else 0,
C_bad(sample) = E_bad(sample) nu lambda_q^2.
```

Round 38 proves exactly

```text
sum C_bad = (sum E_bad) nu lambda_q^2.
```

The restricted aggregate therefore inherits the Round-37 shell coercivity:

```text
(sum E_bad) (nu lambda_q) <= sum C_bad,
(sum E_bad) nu <= (sum C_bad) lambda_q^-1.
```

Finite same-object allocation is no longer a separate theorem: it is true by construction. The remaining physical HH-bad obligations are now only

```text
actual trajectory bad predicate = restricted mask,
physical bad gain <= allowed restricted charge,
real-time/continuum restriction transport,
Luo upper critical-smallness,
```

plus switching estimates if the hysteretic route is used.

Sources: Luo, DOI `10.1007/s00021-019-0411-z`; Bahouri--Chemin--Danchin, DOI `10.1007/978-3-642-16830-7`.

## 6. Occupation and crossings are two different coordinates of the bad region

For bad samples whose defect is at least `theta`, Round 38 proves

```text
repeatedCost theta badSamples
  <= sum realizedDefect
  <= integratedDefect.
```

Separately, the existing hysteretic theorem gives

```text
repeatedCost delta crossings
  <= positiveVariation.
```

`HHBadTwoCoordinateControl` keeps occupation/duration and transition count distinct. The continuum BV/layer-cake interpretation remains a real analytic theorem rather than a datatype assumption.

## 7. A proved cancellation edge reduces the pre-tax positive mass exactly

For `L>=0`, `R<=0`, and a physically justified transfer `tau` with

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

So signed production is conserved while the positive tax drops by exactly `tau`. `PhysicalCancellationEdge` also names its source and target in the literal nine-owner `TaxOwner` type and requires a physical edge identity. Arbitrary reallocation is therefore not licensed.

A full nine-owner cancellation network remains deliberately open until actual cross-owner physical identities/capacities are proved. Only then is a network/LP optimizer mathematically meaningful.

## 8. F4: the two mode carriers and the conjugate-output convention now agree exactly

The direct finite convolution code and the physical Complex3 code used two integer mode records. Round 38 defines exact conversions

```text
FourierMode <-> LatticeMode3
```

and proves both round trips, addition compatibility and negation compatibility.

Every physical incidence

```text
p + q = k
```

is mapped to the direct zero-sum convention

```text
(p, q, -k).
```

Round 38 proves

```text
p + q - k = 0
```

coordinatewise and then proves the direct convolution Boolean

```text
zeroSum? (p,q,-k) = true.
```

Thus `resonantTriadConstraint` and `conjugateOutputModeConvention` no longer hide a carrier mismatch between the two finite routes.

Sources: Bahouri--Chemin--Danchin, DOI `10.1007/978-3-642-16830-7`; Leray, DOI `10.1007/BF02547354`.

## 9. F4: exact enumeration permutations give factor-six cancellation

The `pEnergyLeg`, `qEnergyLeg`, and `swapTriad` maps are proved exact involutions on proof-bearing physical incidences and exact permutations of the complete duplicate-free physical cutoff enumeration.

Let `Ordered(tau)` be the raw ordered signed physical incidence power and `Pair(tau)` the existing symmetrized ordered-pair power. Existing local algebra gives

```text
Pair(tau) = Ordered(tau) + Ordered(swap tau).
```

Permutation invariance gives

```text
sum Pair = 2 sum Ordered.
```

The two energy-leg permutations similarly give

```text
sum threeLegPower
  = 3 sum Pair
  = 6 sum Ordered.
```

Round 37 already proved every `threeLegPower(tau)=0`, so over the rational carrier Round 38 derives

```text
literalOrderedGalerkinIncidencePowerZero :
  sum_{tau in physicalTriadEnumeration_N} Ordered(tau) = 0.
```

No orbit-cardinality division and no free-action assumption is used; stabilizers are harmless because the theorem is about actual list permutations.

The remaining F4 same-object work is now narrower than the stale marker suggests. It must identify the literal projected convection/energy pairing with this already-cancelled ordered incidence fold, including exact shell partition and normalization. In particular the repository's pair-symmetrized coefficient convention must be audited against the ordered convolution convention rather than silently equated.

Sources: Leray, DOI `10.1007/BF02547354`; Roger Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, DOI `10.1090/chel/343`.

## 10. Why no generic `ResidualGramFamily` was added

The common shape

```text
A_i = C_i Q_i
```

is now genuine in both HH-good and `Com`. But neither the physical periodic PV owner estimate nor the physical odd-transport Gram realization is closed. Building a common abstraction before either physical theorem works would move symbols rather than close mathematics.

The proof-engineering boundary remains

```text
literal physical carrier
  -> CanonicalAnalyticPhysicalLeaves
  -> analytic reducers / continuation.
```

## Revised highest-alpha frontier after Round 38

1. **A3/A4 — periodic PV realization and integration.** The nonzero Fourier strain multiplier, residual quotient, good-threshold nonlinear smallness, finite detail factorization and zero-mode-to-zero-mass criterion are all closed. Remaining: actual torus strain-kernel character realization, zero-mode assignment, PV/CZ bound, shell/time localization, then `physicalHHGoodOwnerEstimate`.
2. **A6/A8 — physical restricted HH-bad gain.** Remaining: trajectory-mask identification, restricted-gain estimate, Luo upper critical-smallness, and integrated-defect/positive-variation bounds if switching is used.
3. **A1/A2 — physical odd-transport Gram realization.** Remaining: identify the literal shell odd transport with the two Round-35 Gram/Cotlar pair products. No diagonal estimate remains.
4. **F4 — same-object shell/normalization equality.** Carrier conversion, conjugate output, global ordered-incidence cancellation and multiplicity permutations are closed. Remaining: actual projected convection/energy pairing equals the ordered incidence fold with the correct shell partition and normalization.
5. **Owner reserve.** Instantiate the remaining physical owners, admit only proved cancellation edges before taxation, and run the certified reserve optimizer. A certified minimum `sum eta >= 1` falsifies this owner architecture rather than merely showing poor tuning.
6. Only after these producers close should `CanonicalAnalyticPhysicalLeaves`, maximal-time contradiction, continuum promotion and submission audit become critical-path work.
