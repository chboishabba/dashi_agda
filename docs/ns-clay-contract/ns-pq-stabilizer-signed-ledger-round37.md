# NS Round 37 — P/Q channels, line geometry, and scale-compatible HH-bad coercivity

Round 37 implements the quotient/stabilizer continuation as concrete Navier–Stokes mathematics rather than another terminal wrapper.  It also changes the shortest-path frontier in two useful ways: a direction-only absolute HH-bad floor is ruled out by scaling, while the local HH-good geometric depletion factor is now proved directly in the corrected strain action.

## 1. `Com` is exactly a P/Q cross-channel defect

On the exact rational split carrier

```text
P(x,y) = (x,0)
Q(x,y) = (0,y)
T(x,y) = (a x + b y, c x + d y)
```

Round 37 proves

```text
P^2=P, Q^2=Q, P+Q=I, PQ=QP=0,
[P,T]=PT-TP=PTQ-QTP,
[P,T](x,y)=(b y,-c x),
||[P,T](x,y)||^2=b^2 y^2+c^2 x^2.
```

The diagonal blocks disappear before any norm estimate.  The exact involution

```text
J(x,y)=(y,x)
```

satisfies `J^2=I`, `JPJ=Q`, `JQJ=P`; conjugation swaps the two cross channels.  Therefore A1 is now sharply a **physical cross-channel realization** problem: identify literal shell `P_q T Q_q` and `Q_q T P_q` maps with the Round-35 Gram/Cotlar products and prove their half-dyadic decay.

## 2. HH-good lives on the unoriented vorticity-line quotient

For a unit direction `xi`, let

```text
Pi_xi = xi tensor xi.
```

Round 37 proves

```text
Pi_(-xi)=Pi_xi,
||Pi_xi-Pi_eta||_F^2
  = 2(1-(xi dot eta)^2)
  = (1+xi dot eta)||xi-eta||^2.
```

The repository's existing Constantin–Fefferman/Luo defect is

```text
Theta(xi,eta)=1-(xi dot eta)^2=|xi cross eta|^2,
0<=Theta<=1.
```

The new bridge therefore gives exactly

```text
||Pi_xi-Pi_eta||_F^2 = 2 Theta(xi,eta),
0 <= ||Pi_xi-Pi_eta||_F^2 <= 2.
```

So the stabilizer/projector proposal is not an extra tunable coherence quantity.  It is the existing directional defect expressed on the correct `xi ~ -xi` quotient.

A literal two-element representative action now realizes that quotient: flipping a unit representative twice returns it, the line projector is invariant on every orbit, and the projector defect is invariant under independent flips of either representative.

The physical amplitudes are retained.  For

```text
omega_x=a xi,
omega_y=b eta,
```

Round 37 proves

```text
a^2 b^2 ||Pi_xi-Pi_eta||_F^2
  = 2 |omega_x cross omega_y|^2.
```

### 2a. The actual corrected strain action contains the same defect

The repository's corrected angular strain symbol is

```text
S_theta(w)
  = -1/2 [theta tensor (theta cross w)
          + (theta cross w) tensor theta].
```

Round 37 now proves the exact scalar factorization

```text
v dot S_theta(w) v
  = -(theta dot v) ((theta cross w) dot v)
  = -(theta dot v) (theta dot (w cross v)).
```

Thus the vorticity-misalignment factor `w cross v` is present **before** taking an absolute value or introducing the singular kernel.  Parallel source and target vorticities kill the cross-mode stretching contribution exactly.

Using the already checked Lagrange identity twice gives the first genuine pointwise depletion estimate.  For unit `theta`,

```text
|v dot S_theta(w) v|^2
  <= |v|^2 |w cross v|^2.
```

This is the key Round-37 HH-good advance: the missing A3/A4 mathematics has moved past local strain geometry.  What remains is the periodic principal-value kernel, shell/time localization, and retention of a sufficiently small owner coefficient.

### 2b. Finite PV subtraction is exact

For a weighted line-projector kernel with zero total mass,

```text
sum_y K_y = 0,
```

we prove matrixwise

```text
sum_y K_y Pi_y
  = sum_y K_y (Pi_y-Pi_x).
```

The surviving analytic chain is therefore

```text
literal torus strain PV cancellation
 -> projector/directional increments
 -> exact strain misalignment factor
 -> shell-localized integral estimate
 -> physical HH-good owner coefficient.
```

## 3. Direction-only absolute HH-bad floors fail by scaling

Round 36 observed that a genuine floor

```text
Gamma_q = nu lambda_q,
occupation_q Gamma_q <= charge_q
```

would imply the desired inverse-shell charging

```text
occupation_q nu <= charge_q lambda_q^-1.
```

The Round-37 scaling experiment tests whether `Gamma_q` can arise merely from scale-invariant direction/stabilizer badness.  In that carrier, the bad-direction evidence survives amplitude rescaling while quadratic dissipation obeys

```text
D(s a)=s^2D(a),
D(a/2)=(1/4)D(a).
```

Closure under zero amplitude makes `D=0`, so any uniform amplitude-independent floor inferred from that geometry alone must obey

```text
floor <= 0.
```

This is a narrow but real no-go theorem.  A positive absolute dissipation quantum cannot be generated solely by scale-invariant directional mismatch.

## 4. Energy-normalized HH-bad coercivity survives the no-go

The viable scale-compatible statement is

```text
E_bad (nu_eff lambda_q) <= C_bad,
```

where `E_bad` is energy-weighted bad occupation and `C_bad` its localized dissipation charge.  Round 37 constructs the Round-36 floor cell from this inequality and derives

```text
E_bad nu_eff <= C_bad lambda_q^-1.
```

Simultaneous nonnegative rescaling of `E_bad` and `C_bad` preserves the coercivity inequality.

### 4a. Full shell viscosity already supplies the elementary coercive rate

For `lambda_q=2^q`, Round 37 proves

```text
1 <= lambda_q <= lambda_q^2.
```

Therefore

```text
C_full = E_bad nu_eff lambda_q^2
```

automatically satisfies

```text
E_bad(nu_eff lambda_q) <= C_full
```

and the inverse-shell consequence follows.

So A6 is **not** an unknown Bernstein/Poincaré inequality.  The hard theorem is the physical same-object allocation: prove that the HH-bad owner charge contains the required share of literal shell viscous dissipation and that its actual bad gain/occupation is represented by the same `E_bad`.  This must remain separate from the older Luo *upper* critical-smallness theorem `lambda_q D_q <= (eta/2)nu`; the lower coercivity result does not supply that upper smallness estimate.

## 5. Hysteretic crossing cost is exact

For a finite bad-entry list with minimum jump `delta`, Round 37 proves

```text
repeatedCost delta crossings
 <= sum realized crossing jumps.
```

If those jumps are charged to positive defect variation,

```text
repeatedCost delta crossings <= positiveVariation.
```

The remaining A8 step is now physical: every actual HH-bad entrance must instantiate the hysteretic jump and the resulting positive variation must be bounded uniformly in cutoff.

## 6. Signed owner information is retained before positive taxation

For one owner,

```text
Delta = production - cancellation.
```

An internal transfer `tau` credited to one owner and debited from another satisfies exactly

```text
((A+tau)-B)+(C-(D+tau))=(A-B)+(C-D).
```

The final nine-owner theorem still uses admissible positive production.  This preledger merely prevents exact cancellation from being destroyed before it has been analysed; it does not use hidden cancellation to evade the final viscosity estimate.

## 7. The shell budget is now a literal inverse-system skeleton

From the Round-36 identities

```text
I_Q+B_Q=eta,
B_(Q+n)=B_Q 2^-n,
```

Round 37 proves

```text
I_(Q+n)-I_Q=B_Q(1-2^-n),
(I_(Q+n)-I_Q)+B_(Q+n)=B_Q.
```

With the bonding map

```text
pi(I,B)=(I-B,2B),
```

canonical shadows satisfy

```text
pi(L_(Q+1))=L_Q.
```

The analytic inverse-limit step still requires boundary vanishing and compactness.

## 8. Reserve optimization is constructive and falsifiable

A `CertifiedEtaMinimizer` is an actual feasible owner allocation whose `etaTotal` is no larger than every feasible competitor.  Round 37 proves it maximizes the reserve `1-etaTotal`.

Hence

```text
etaTotal(minimizer) < 1
```

certifies strict reserve, while

```text
1 <= etaTotal(minimizer)
```

proves no feasible allocation has strict reserve.  Equality at one is a genuine critical obstruction rather than a tuning failure.

## 9. F4 is narrower than its stale status marker

The repository already has physical `C^3` three-leg cancellation from resonance, Fourier reality and divergence-free transversality, plus literal duplicate-free cutoff triad enumeration.  Round 37 specializes this to the exact rational carrier and proves

```text
threeLegPower(tau)=0
```

for every physical triad, hence

```text
sum_{tau in physicalTriadEnumeration N} threeLegPower(tau)=0.
```

A repository audit also confirms that `NSTriadKNFiniteComplexFourierDynamics` derives zero-sum modal-transfer conservation from local complex algebra via `physicalSixTermComplexFactorizationFromLocalAlgebra` and `physicalModalTriadTransferConservationFromLocalAlgebra`.  The actual F4 frontier is therefore the global same-object/multiplicity equality between Galerkin nonlinear power and the enumerated fold, plus concrete authority wiring.

## 10. Classification stays attached to its witness

`ClassifiedAt` and `HHBadAt` store property evidence indexed by the state and relevant shell/time index.  Forgetting classification returns the same ambient state; moving to another classification requires an explicit predicate implication.  This prevents selected-subclass theorems from silently becoming identities of the final carrier.

## Revised shortest high-alpha frontier

1. **A3/A4 periodic PV integration:** local geometric depletion is now proved.  Realize the literal torus strain kernel with PV cancellation, integrate/shell-localize `|v|^2|w cross v|^2`, and obtain a physical HH-good coefficient small enough for the owner budget.
2. **A6 HH-bad localization/allocation:** connect actual bad energy/gain to the energy-weighted coercivity carrier and assign enough literal shell viscous charge; separately prove the Luo critical upper-smallness estimate where required.
3. **A1 Com operator realization:** identify literal `P_q T Q_q` and `Q_q T P_q` with the existing Gram/Cotlar pair products and prove half-dyadic decay uniformly in cutoff.

In parallel remain the F4 global fold equality, Bishop-state codec and real Picard–Lindelöf authority, time integration/global finite flow, physical nine-owner coefficients with strict total eta, and the cutoff/compactness/continuation tail.

No theorem in this round is promoted to unconditional Navier–Stokes regularity.