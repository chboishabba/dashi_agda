# Bishop π × YM.REAL cross-PR max-cut, 17 November 2026

## Latest checked PR heads

- dashi_agda PR #1478 (merged 14 Nov 2026), head fb374e50e59a98e2b8a1eee215c77428c5728b68.
- dashi_lean4 PR #104 (merged 14 Nov 2026), head dbda83aec4b6aa07746d5c692d2d99440872bda1.
- YM current target is dashi_agda PR #1444 (open).

## Actual Agda π already exists, but periodicity is open

BishopMachinArctanConstructionExact constructs the two true convergent Bishop atan series and their genuine same-object real
\[
\pi_M=16\,\operatorname{atan}_B(1/5)-4\,\operatorname{atan}_B(1/239).
\]
BishopMachinPiArchimedesWindowExact proves
\[
223/71<\pi_M<22/7.
\]
BishopMachinQuarterAngleBranchExact constructs
\(\theta_M=4\operatorname{atan}_B(1/5)-\operatorname{atan}_B(1/239)\),
proves \(4\theta_M\simeq\pi_M\), \(3/4<\theta_M<11/14\),
and the rational tangent parameter 1.

The actual Round11 elementary sine/cosine series are available,
with source series convergence (BishopConcreteTrigSeriesConvergenceExact)
and setoid congruence (BishopSineCosineSetoidCongruenceExact).
JInvariantBishopTrigUnitPhaseExact has the correct *Pythagorean
input interface*, but does not construct the Pythagorean theorem there.
AbelBishopMachinQuarterToQPeriodExact establishes an algebraic
two-pi/eight-quarter equality, not an exponential periodicity theorem.
BalabanWilsonFourierMachinPeriodCarrierExact selects the *same*
Machin real definitionally, avoiding a duplicate free period.

**Actual analytic obligations:** prove the original power series
Pythagorean identity, concrete sine/cosine addition/doubling,
the Maclaurin arctan tangent agreement and positive cosine branch
at theta_M. Then, using the existing rational Machin tangent arithmetic,
\[
\sin_B(\theta_M)\simeq\cos_B(\theta_M)>0,\quad
\sin_B(\pi_M)\simeq0,\quad\cos_B(\pi_M)\simeq-1.
\]
The last step is now source-written in
DASHI/Foundations/BishopMachinPiDoubleAngleAlgebraExact.agda and
DASHI/Foundations/BishopMachinPiPeriodFromQuarterExact.agda,
for the actual Round11 selected elementary functions.
Both files still await Agda kernel acceptance; the concrete analytic
premises are inputs, not invented proofs.

## Lean cross-prover boundary

Lean Integration/BishopVendoredMachinPiSemantics.lean (PR #104)
contains eval_atan_eq_real_arctan and eval_machinPi_eq_real_pi.
The latter uses Mathlib's Real.four_mul_arctan_inv_5_sub_arctan_inv_239.
These theorems require a VendoredMachinSourceMirror of the actual
Bishop arctan convergence inputs. The source explicitly sets
actualAgdaMachinConvergenceMirrorInhabited=false; similarly the
primitive-extraction source marks the complete Agda vendor mirror
package uninhabited. Therefore the Lean theorem is a powerful
conditional semantics compiler, NOT an Agda kernel theorem or a
verified same-object inter-prover witness.

## YM.REAL current six gates

1. Finite Fejer products: finite positive-weight transport source-written,
   transitive/kernel checks pending.
2. General Fourier/cubature: no accepted all-m Bishop trig or dyadic-root
   exact producer, regardless of reference rational checks.
3. Effective b_n approximation: mathematical constructive bound
   established, original Bishop polynomial/Cauchy proof still open.
4. Bishop Haar completion: native Sequence.fast-cauchy⇒convergent
   consumer source-written, actual b_n Cauchy proof open.
5. SU2 quaternion trace/determinant/unitarity: Agda candidate source
   and exact symbolic checks present, kernel and original carrier open.
6. Original Wilson exponential/Haar/cylinder identity:
   actual source/finite Gibbs and exp order weld open.

Do NOT close YM.REAL or claim --safe from a local pragma. No pinned
Agda/Nix execution in this environment. Expanded auxiliary ledger
remains 19/28 open.

Attribution: Machin, Archimedes, Bishop–Bridges, Murray/Csimma,
Mathlib, Aristotle-Harmonic upstream proof, original DASHI and
Wilson/Balaban theorem authors.


## Direct positive finite SU(2) Gibbs max-cut (this PR continuation)

Existing original SAME Bishop real owners recovered:
- BishopSquareNonnegativeExact.bishopSquareNonnegative, actual nonnegative every real square.
- BishopExponentialPositiveOrderExact.bishopExpAtLeastOneOnNonnegative.
- BishopExponentialCauchyProductExact.bishopExpTimesNegativeIsOne.
- BishopNegativeExponentialGlobalUnitIntervalExact existing strictly
  positive exp(-x) for STRICT positive x, plus actual inverse lemmas.
- YMClayBishopFiniteWilsonNormalizedExact weightedSumStrictPositiveHead,
  previously source-written and still not Agda-accepted.

New source:
1. YMClayBishopWilsonGibbsPositiveExact: derives exp_B(-S)>0 for **every
   NonNegative S**, including zero, without excluded middle or trichotomy:
   exp_B(S)>=1>0; exp_B(S)exp_B(-S)=1;
   exp_B(-S)=inverse(exp_B(S))>0 by actual Bishop inverse order.
   This removes a free strict-positive exponential leaf.

2. YMClayBishopSU2WilsonDeficitPositiveExact: for a norm-one genuine
   Bishop unit quaternion q,
   \[
     \frac12((q_0-1)^2+q_1^2+q_2^2+q_3^2)
     \simeq 1-q_0.
   \]
   Hence 1-q0 is nonnegative from actual Bishop square positivity.
   Finite lists of these plaquettes at beta>=0 have nonnegative Wilson
   action, and exp_B(-action) is strictly positive.

3. YMClayBishopSU2FiniteGibbsPartitionExact: on a nonempty finite
   weighted list of these plaquette configurations, a positive first
   node weight and nonnegative remaining weights give an ACTUAL
   strictly positive finite Gibbs partition, and a normalized
   expectation of 1 equal to 1 with the genuine Bishop inverse.
   No separate positive-partition axiom is introduced.

4. scripts/check_ym_su2_gibbs_positive_20261117.py: 146 exact rational
   reference assertions over all 24 rational 24-cell vertices and
   three nonnegative rational couplings; not an Agda kernel certificate.

These construct the FINITE algebraic/Gibbs side on the Bishop quaternion
carrier. Crucially they do NOT prove that this configuration list is
the original 4(n+1)^4-link six-plane lattice Wilson Gibbs/Haar source.
The same-source link→plaquette map, all-degree Haar cubature, completed
continuous admissible one-link functional, and gauge-invariant original
finite cylinder source remain OPEN. Do not mark YM.REAL closed.

All new Agda modules require pinned Agda typechecking, including
transitive non-safe imports; none has been run here.
