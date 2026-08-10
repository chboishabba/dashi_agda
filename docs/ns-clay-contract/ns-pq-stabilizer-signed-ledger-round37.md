# NS Round 37 — P/Q channels, line-projector geometry, and scale-compatible HH-bad coercivity

Round 37 takes the shortest-path cut after Round 36 and tests the quotient/stabilizer proposals as concrete mathematics.  The main outcome is not merely additional structure: one proposed HH-bad interpretation is ruled out by scaling, its viable energy-weighted replacement is identified, the easy part of that replacement is discharged by ordinary shell viscosity, and the HH-good stabilizer language is proved to be exactly the repository's existing directional defect on the correct unoriented quotient.

## 1. Com lives entirely in the P/Q cross channels

On the exact rational split carrier

```text
P(x,y) = (x,0)
Q(x,y) = (0,y)
T(x,y) = (a x + b y, c x + d y)
```

we prove

```text
P^2 = P
Q^2 = Q
P + Q = I
PQ = QP = 0
```

and, crucially,

```text
[P,T] = PT - TP = PTQ - QTP.
```

In coordinates,

```text
[P,T](x,y) = (b y, -c x),
```

so

```text
||[P,T](x,y)||^2 = b^2 y^2 + c^2 x^2.
```

The diagonal coefficients `a,d` disappear exactly.  Therefore the physical A1 theorem should be phrased as a shell cross-channel realization: identify the literal coarse→fine and fine→coarse maps with the already controlled Round-35 Gram/Cotlar products.  There is no reason to spend more effort bounding diagonal pieces of the commutator; they cancel before estimation.

The quotient-inspired involution is also exact:

```text
J(x,y) = (y,x)
J^2 = I
JPJ = Q
JQJ = P.
```

Conjugating transport by `J` swaps the two diagonal blocks and the two cross-channel coefficients.  This gives the proposed P/Q/J layer a literal finite NS carrier rather than only an analogy.

## 2. HH-good stabilizer mismatch is exactly the existing directional defect

For a unit direction `xi`, define the orientation-free line projector

```text
Pi_xi = xi tensor xi.
```

Round 37 proves

```text
Pi_(-xi) = Pi_xi,
```

and for unit `xi,eta`,

```text
||Pi_xi - Pi_eta||_F^2
  = 2 (1 - (xi dot eta)^2)
  = (1 + xi dot eta) ||xi - eta||^2.
```

The repository already defines the Luo/Constantin--Fefferman directional defect

```text
Theta(xi,eta) = 1 - (xi dot eta)^2
               = |xi cross eta|^2,
0 <= Theta <= 1.
```

The new bridge proves exactly

```text
||Pi_xi - Pi_eta||_F^2 = 2 Theta(xi,eta),
```

hence the projector/stabilizer defect lies in `[0,2]` and is not a new free parameter.  It is the same directional coherence invariant expressed on the correct unoriented line quotient.  This is useful because Round 36 already ruled out Fourier wave-vector angle as the HH-good smallness source.

The physical amplitude weights are preserved as well.  Combining the projector identity with the existing physical vorticity theorem gives

```text
omega_x = a xi,
omega_y = b eta

=>

a^2 b^2 ||Pi_xi-Pi_eta||_F^2
  = 2 |omega_x cross omega_y|^2.
```

Thus the projector formulation is not merely normalized angular language: it is exactly compatible with the amplitude-weighted interaction that must enter the strain estimate.

The orientation quotient itself is now literal.  A two-element action changes a unit representative by `xi -> -xi`; applying it twice returns the original vector, the rank-one projector is invariant on every such orbit, and the projector defect is invariant under independent sign changes of either representative.  This gives the quotient proposal a concrete NS realization as the vorticity-line `C2` quotient.

A finite principal-value skeleton is also exact.  For weighted line projectors with zero kernel mass,

```text
sum_y K_y = 0,
```

we prove coordinatewise and matrixwise

```text
sum_y K_y Pi_y
  = sum_y K_y (Pi_y - Pi_x).
```

Thus the surviving A3/A4 chain is now sharply typed:

```text
literal periodic strain kernel zero-mass/PV cancellation
  -> amplitude-weighted projector increments
  -> existing Theta directional defect
  -> explicit cross-fibre strain term
  -> HH-good owner estimate.
```

The first and last analytic arrows remain physical theorems; the finite cancellation/projector geometry in the middle is closed.

## 3. Direction-only HH-bad absolute floors fail by amplitude scaling

Round 36 showed that a floor of the form

```text
Gamma_q = nu lambda_q
occupation_q Gamma_q <= charge_q
```

would yield exactly

```text
occupation_q nu <= charge_q lambda_q^-1.
```

The stabilizer proposal suggested deriving an absolute floor merely from being outside an alignment-compatible stratum.  Round 37 tests that scale-invariant formulation and proves that it cannot work when dissipation is quadratic.

A direction-only bad witness keeps its direction and bad-geometry evidence when its amplitude is rescaled.  If

```text
D(a) = W a^2,
```

then exactly

```text
D(s a) = s^2 D(a),
D(a/2) = (1/4) D(a).
```

In the tested direction-only carrier, setting amplitude to zero preserves the geometric classification but makes `D=0`.  Consequently any uniform amplitude-independent absolute floor inferred from that classification alone must satisfy

```text
floor <= 0.
```

The conclusion is deliberately narrow but decisive: a positive HH-bad dissipation quantum cannot come from scale-invariant direction/stabilizer mismatch alone.  The theorem does not rule out an energy-normalized coercivity ratio, an amplitude-weighted occupation, or another scale-breaking physical hypothesis.

## 4. The viable HH-bad quantity is energy-weighted coercivity

Let `E_bad` be bad-shell energy occupation and `C_bad` its localized dissipation charge.  The scale-compatible target is

```text
E_bad (nu_eff lambda_q) <= C_bad,
```

which is the division-free form of

```text
C_bad / E_bad >= nu_eff lambda_q
```

when `E_bad` is nonzero.

Round 37 packages this as `BadEnergyCoercivityCell`, constructs the Round-36 floor cell with

```text
occupation = E_bad,
floor      = nu_eff lambda_q,
charge     = C_bad,
```

and therefore derives

```text
E_bad nu_eff <= C_bad lambda_q^-1.
```

Simultaneous nonnegative rescaling of `E_bad` and `C_bad` preserves the coercivity inequality.  This repairs the scale defect of an absolute direction-only floor.

### 4a. The elementary shell-coercivity part is already closed

The new audit then asks whether even this normalized inequality is genuinely difficult.  For the exact dyadic scale `lambda_q=2^q`, Round 37 proves

```text
1 <= lambda_q <= lambda_q^2.
```

Hence the full shell viscous charge

```text
C_full = E_bad nu_eff lambda_q^2
```

automatically obeys

```text
E_bad (nu_eff lambda_q) <= C_full,
```

and therefore produces the same inverse-shell charging theorem.

This is an important narrowing of A6.  **Ordinary shell viscosity already supplies the normalized coercive rate if the HH-bad owner is allowed to charge the corresponding full shell dissipation.**  The hard physical theorem is therefore not `lambda_q <= lambda_q^2` in disguise.  It is the same-object localization/allocation statement showing that the actual HH-bad owner charge contains the required share of shell viscosity and that the physical bad gain/occupation is linked to the same `E_bad` quantity.  Separately, the older Luo critical-absorption route still requires its upper smallness condition on the localized defect/dissipation quantity; the lower coercivity statement here does not prove that upper smallness estimate.

## 5. The crossing/variation mechanism is now an exact finite theorem

Each bad entrance may carry a minimum hysteretic jump `delta`.  For the actual finite crossing list, Round 37 proves

```text
repeatedCost delta crossings
  <= sum realized crossing jumps.
```

If those jumps are charged to positive directional-defect variation, then

```text
repeatedCost delta crossings
  <= positiveVariation.
```

`repeatedCost` is the constructive version of `N_bad * delta`; no informal Nat-to-real multiplication is needed.  The remaining A8 theorem is the physical instantiation: show that every actual HH-bad entrance pays the hysteretic jump and prove the cutoff-uniform positive-variation bound.

## 6. Signed owner information is retained before the positive tax

For each owner define the fine signed balance

```text
Delta = production - cancellation.
```

Reversing production/cancellation negates `Delta`.  An internal transfer `tau` credited to one owner and debited from another obeys exactly

```text
((A+tau)-B) + (C-(D+tau))
  = (A-B) + (C-D).
```

The final nine-owner theorem still bounds admissible positive production; Round 37 does not use hidden cross-owner cancellation to evade viscosity absorption.  It simply prevents exact signed cancellation from being destroyed before one has proved whether it is available.  This is particularly relevant for `Com` and HH-good, where cancellation is the resource the analysis is trying to expose.

## 7. Finite shell ledgers now have both a telescope and an actual bonding map

Round 36 proved

```text
I_Q + B_Q = eta,
B_(Q+n) = B_Q 2^-n.
```

Round 37 adds

```text
I_(Q+n) - I_Q = B_Q (1 - 2^-n),
(I_(Q+n)-I_Q) + B_(Q+n) = B_Q.
```

Thus refinement splits the old boundary exactly into newly internalized resource and the new boundary.

It also defines the finite bonding map

```text
pi(I,B) = (I-B, 2B)
```

and proves on canonical shadows

```text
pi(L_(Q+1)) = L_Q.
```

So the owner ledgers form a literal inverse-system skeleton.  The analytic inverse limit still requires physical boundary vanishing and compactness.

## 8. Reserve optimization is constructive and falsifiable

Round 36 defined an admissible owner polytope.  Rather than postulating

```text
Delta_* = 1 - inf feasible etaTotal,
```

Round 37 defines a `CertifiedEtaMinimizer`: an actual feasible point whose `etaTotal` is no larger than every feasible competitor.  It proves that this point maximizes reserve among feasible points.

Two sharp diagnostics follow:

```text
etaTotal(minimizer) < 1
```

gives a strict feasible owner allocation, whereas

```text
1 <= etaTotal(minimizer)
```

proves that **no** feasible allocation can have strict reserve.  A certified minimum equal to one is therefore a genuine critical obstruction, not a tuning failure.

## 9. F4 is narrower than the stale Round-30 marker suggests

The repository already contains exact physical `C^3` three-leg cancellation from resonance, Fourier reality and divergence-free transversality, plus literal duplicate-free cutoff triad enumeration.  Round 37 specializes that theorem to the exact rational carrier and proves

```text
threeLegPower(tau) = 0
```

for every physical triad and therefore

```text
sum_{tau in physicalTriadEnumeration N} threeLegPower(tau) = 0.
```

No caller-supplied cancellation witness is used.  The remaining F4 seam is explicitly the same-object/multiplicity theorem equating the complete Galerkin nonlinear power with this enumerated three-leg fold.  The local physical cancellation itself is no longer the mathematical unknown.

A second repository audit found that `NSTriadKNFiniteComplexFourierDynamics` already derives its zero-sum modal-transfer conservation from local complex algebra via `physicalSixTermComplexFactorizationFromLocalAlgebra` and `physicalModalTriadTransferConservationFromLocalAlgebra`; therefore the stale `complexSixTermFactorizationPhysicalClosed = false` marker should not be interpreted as the mathematical frontier.  The actual unresolved F4 issue is the global enumeration/fold identification and concrete authority wiring, not local six-term cancellation.

## 10. Classification remains a scoped property edge

`ClassifiedAt` and its `HHBadAt` specialization keep bad/good/selected properties attached to their index, state and evidence.  Mapping a classification requires an explicit implication between predicates; forgetting the classification returns the original ambient state.  This encodes the anti-terminalization/scope lesson directly: a theorem about a selected subclass does not silently change the carrier of the final theorem.

## Revised highest-alpha frontier

The next three analytic targets are now more precise than at the start of the round:

1. **A6 — HH-bad localization/allocation, not elementary coercivity:** prove that the actual HH-bad energy/gain is represented by the energy quantity used in the coercivity cell and that its owner charge receives enough of the literal shell viscous dissipation.  Keep this distinct from the older Luo upper critical-smallness hypothesis, which remains a separate physical estimate.
2. **A1 — physical Com cross-channel realization:** identify the literal shell `P_q T Q_q` and `Q_q T P_q` maps with the Round-35 Gram cells / two Cotlar pair products and prove the half-dyadic decay uniformly in cutoff.
3. **A3/A4 — periodic PV projector increment theorem:** prove the literal torus strain kernel's PV zero-mass/cancellation representation and estimate its amplitude-weighted projector-increment integral by the existing `Theta` defect plus admissible kernel/tail terms.

In parallel, the finite lane should finish the Galerkin-power/enumerated-fold same-object identity, Bishop-state codec/Picard--Lindelof authority, time integration and global finite flow.  After the physical owner coefficients are available, the certified reserve optimizer gives an immediate falsification test for whether the nine-owner feasible region intersects `sum eta_i < 1`.

No module in this round promotes these finite/algebraic results to unconditional Navier--Stokes regularity.