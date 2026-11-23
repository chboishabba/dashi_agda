## P0 ADDENDUM — ORIGINAL positive-radius source REFUTES phase-only descent and yields a √R Fourier-zero splitting law

**This section corrects an essential potential overreach from the pure atomic C4 bridge above.** The ORIGINAL `scripts/check_rh_original_bump_explicit_radius_20261122.py` already proves a source-specific selected positive-radius q=4 high-pole sign, under its recorded Fourier remainder/IVT majorants (not Lean kernel): for **R=10^-10**, `K_{R,∞}(0,4)>R²/6`, and for physical `t≥10^14, |a|≤1/2`, `K_{R,t}(a,4)>11R²/300>0`. The **same original source** has `K_{R,∞}(0,0)=0` identically because its normalized projective q-observer is `Q(q)=2(A1(A(q-2)+A(q+2))-A2(A(q-1)+A(q+1)))` and evenness gives `Q(0)=4(A1 A2-A2 A1)=0`. The actual selected q4 source is POSITIVE while the atomic `F(4)=0`. Thus two original REAL frequency arguments q=0,4 with identical four-phase circle coordinate `z(q)=1` have DIFFERENT high-pole positive-radius original responses. **The original smooth physical response does NOT FactorsThrough the four-phase quotient**, even though the atomic F does. This is a genuine same-original-source consumer collision, stronger than q1/q4 C3-only aliasing. A phase-only finite RH smoothing square is therefore REFUTED, not merely unproved.

Independent exact local source symbolic regression `scripts/check_rh_smooth_bump_c4_alias_obstruction_20261123.py` (local) and `scripts/check_rh_original_bump_q4_sqrtR_boundary_layer_20261123.py` (committed) consume original centre angles (0,π/3,π/2,π), endpoint λ=1/2,2/3, source J2 roots `μ0=(13λ-8)/(144-54λ)`, original selected pole `P=(A15+A17)A2/2-(A14+A18)A1/2`, and original q-profile Q above. For `e=E[Y²]/2`, the source's fixed-shape even normalized bump (Y=R Z) gives `e=(m2/2)R², m2=E[Z²]∈[1/24,1]`. The original exact J2-root first variation `μ1` then produces the source **uniform finite-q-neighbourhood Taylor**:
```text
K_R(q)=F(q)+e K1(q)+O(R^4)     for q in a compact neighbourhood of 4,
K1(4)=120/13,
K1'(4)=-200*sqrt(3)*pi/117 -10/13 +764*pi/351,
F(4+δ)=-5*pi^4*δ^4/1404 +5*pi^6*δ^6/33696+O(δ^8).
```
Uniformity of the last O(R⁴) follows from the original compact bump Fourier remainder bounds for |q±2|≤18 and the nonzero `∂μ J2` at both endpoints, not from a Gaussian approximation or an arbitrary finite-operator change of chart. The source local SymPy derivatives passed. **Finite-t original phase/derivative neighbourhoods need a separate q-uniform pole bound**; the old 13e6/t² receipt at exactly q4 is NOT silently extended to all q.

Set `ε=√R`, `q=4+xε`. The SAME original source asymptotically satisfies, uniformly for x in compact real intervals and one fixed normalized bump shape,
```text
K_R(4+x√R)/R²
  = (60*m2/13) -(5*pi^4/1404)*x^4 +O(√R).
```
The leading polynomial has two nonzero SIMPLE roots
```text
x_±=±(6/pi)*m2^(1/4).
```
The original J2 root is analytic in R near zero (source nonzero Jacobian and compactly supported scaled even bump), so the rescaled physical projective source extends smoothly in ε near zero. The ordinary implicit function theorem gives TWO actual **high-pole smooth-source Fourier-response zeros**, one on either side of q4, with the claimed asymptotics
```text
q_±(R)=4 ± (6/pi)*m2^(1/4)*√R +o(√R),   R↓0.
```
These are OBSERVED Fourier-response zeros of the `J2`-selected original smooth high-pole projective *test*, not ζ zeros, not signed A2 zeros, and not proof of any new actual RH zero.

Even without solving the root exactly, the original m2 bounds give UNIVERSAL sufficiently-small-R sign brackets:
```text
K_R(4±(1/2)√R)>0,    K_R(4±2√R)<0
```
because the positive worst-case leading coefficient at m2=1/24,x=1/2 is `5/26 -5*pi^4/22464>0` using π<22/7; the negative worst case at m2=1,x=2 is `(20/351)*(81-pi^4)<0` since π>3. Source-bounded uniform O(√R) makes both signs rigorous for sufficiently small R. The explicitly selected R=10^-10 q4 positive certificate is independently stronger at the CENTRE; we do NOT claim the outward sign bracket for this one fixed R or for t≥10^14 without a new explicit q-uniform remainder proof.

**New geometric construction required for actual finite-width observables:** the original atomic `q mod4` angular phase is a valid consumer sufficient statistic only for F. To reconstruct `K_R` even on integer q one needs at least its **winding/frequency index** (q0 versus q4) plus original bump moment/source R, pole t and normalized branch data. On real q the exact phase and winding pair `(e^{i*pi*q/2}, floor(q/4))` with a chosen phase representative recovers q, while the original H05 sign/history/refinement/Frobenius/consumer and original ζ-zero multiplicities must still be retained independently. The source-specific F `R=0` is a quotient where winding becomes unobservable; finite R reopens that fibre. This is precisely the original `ConsumerFibreRepairExact` / `SectionedProjectionProvenanceBridgeExact` pattern, and the mathematical reason to distinguish Fourier-observed zero, q-labelled cancellation, actual ζ-zero and nonempty source.

**Next RH analytic cut:** use this source-identified `R²` versus `δ⁴` boundary layer when designing an original `K_{R,t}(q)` quantitative **q-neighbourhood** transport (with physical pole, horizontal a and source derivatives). For the A2 strict terminal the genuinely signed `FarExact` against `μ`/compensation remains independent. Do NOT confuse the new Fourier-response root splitting with ζ-zero production or claim that q smoothing is the actual angular bump.

---

# RH P0: source-correct C3 spatial × C4 angular phase, Lacan/Irigaray grammar and real-q quartic coercivity (23 November 2026)

**Selected exact SOURCE**: Lean `Synthesis/RiemannProjectiveQuarticFourWindowAtomic.lean`, `...PoleSameObject.lean`, `...SignedPoleTarget.lean`, RH Agda `RHFourWindowBiharmonicFiniteCubeExact.agda`, original H05 `GovernedIndexedResidualCubeExact.agda`. Already-proved atomic high-pole source `Docs/proofs/RHA2AtomicBiharmonicStencilCoefficientAnatomy20261122.md` and original Bishop π proof notes own the negative-square fourth-difference, raw `pi/3` cancellation and finite-t/positive-radius nonpromotion. **New source module** `DASHI/Analysis/RHFourWindowAngularC3C4SufficientConsumerExact.agda` reuses original `FiniteThreeCycleTorusExact.Residue3`, `ShiftPhaseTableInterference.Phase4`, `ConsumerDescentMinimalObserverExact` / `ObserverFactorizedRefinementExact`, and retains original RH `Source4`. Exact local regression `scripts/check_rh_angular_c3_c4_grammar_mixed_consumer_20261123.py`; real-q inequality `scripts/check_rh_atomic_real_angle_quartic_coercivity_20261123.py`. LOCAL SymPy rational and exhaustive integer finite checks PASS; committed Agda not kernel-typechecked, no Lean/CI.

## 1. Correct the philosophical-to-spatial interpretation (source-first, NOT arbitrary role renaming)

Original `LacanFregeTernaryRoleChartExact.lacanOneCentredEdge` is the specifically scoped **directed** relation `code1→code0`, `code1→code2`. Its `code0` is Frege/genesis lack/inexistence and code1 is a privileged comparison hub; not a physical spatial zero, anatomical role or general Lacan/S2 ontology. Original `IrigarayLabialRelationalCarrierExact.irigarayReciprocalEdge` is directed reciprocity `code1↔code2`, with `code0` **classification refusal**, not a spatial midpoint or cardinal zero. Original `LacanIrigarayTernaryGrammarBridgeExact.noTernaryRelabellingPreservesGrammar` already proves, for all six three-label permutations, these directed source relations do not match. Reuse that exact theorem, DO NOT reprove it as a new abstract claim.

**The concrete distinct rechartings of their UNDIRECTED skeletons** are:
- Lacan symmetrized comparison `0—1—2` with central `code1` mapped to native balanced zero and endpoints to `-1,+1`, giving true original spatial P3 Laplacian `[[1,-1,0],[-1,2,-1],[0,-1,1]]` in (-1,0,+1) order. This symmetrization LOSES the original directed privilege, which is preserved separately in provenance.
- Irigaray contact `1↔2` with `code1,code2` mapped to native signed `-1,+1` and `code0` to zero gives the edge `-1—+1` and **isolated zero**. This is `K2 ⊔ K1`, not C3, because C3 requires adding BOTH zero-to-endpoint edges that are ABSENT from her grammar. It also is NOT the nonwrap P3 edge.
- The independent spatial C3 graph has ALL three pairwise undirected edges, a physical graph CHOICE on the three native coordinates, not a Lacan or Irigaray relation.

The Laplacian spectra are `P3: {0,1,3}`, `Irigaray contact skeleton: {0,0,2}`, `C3: {0,3,3}`. At the EXACT finite model time pi, their wave operators are `U_P3(pi)=U_C3(pi)=2J/3-I` but `U_Irigaray(pi)=I`. Thus coincidence of P3 and C3 stroboscopic operators does **not** descend through the original reciprocal-contact grammar. Original relational role meaning, direction of arrows, sign, distinguished zero and source history are separate consumers, not forced physical identifications. No metaphysical/philosophical source is claimed to prove PDE/gauge/RH physics.

## 2. Exact RH integer-frequency alias obstruction and positive repair

The original atomic RH projective stencil has `h=pi/2`, the *surviving* three sites 0,h,2h, and original full raw `pi/3` site with TWO nonzero cancelling contributions. Exact signed Laurent symbol:
```text
B_h= -(20/351) (T+T^-1-2I)^2
F(q)=-(80/351)(1-cos(pi*q/2))²
    =-(320/351)sin(pi*q/4)^4.
```
The origin physical angular frequency q is REAL; its Fourier response is 4-periodic. If one deliberately RESTRICTS this q to INTEGER values for the proposed comparison to original periodic C3 Fourier classes, `q=1` and `q=4` share q mod3 =1 (and same native U(pi) phase -1), but
```text
F(1)=-80/351,     F(4)=0;   also F(0)=0 vs F(3)=-80/351 despite both q mod3=0.
```
This is a direct `ConsumerNonDescentWitness`: original RH fourth-difference does NOT `FactorsThrough` the C3 mode, not even when the scalar finite U(pi) time operator agrees with the original P3 walk. The earlier evaluation of the SAME RH polynomial on a C3 shift, with nonzero spectrum -20/39, is an algebraic group-ring specialization **on a different representation**, NOT the original angular character q=4. It aliases the fourth-order notch to a nonzero C3 eigenvalue and cannot replace the original angular source.

**Consumer-aware REPAIR:** original `ShiftPhaseTableInterference.Phase4` supplies the four-valued angular residue `q mod4`. In selected integer units `-80/351`, the original signed response is `(0,-1,-4,-1)` for q=0,1,2,3 mod4. `quarticMagnitude4=(0,1,4,1)` and an independent `QuarticSign=(observedNotchZero|negativeNotch)` retain sign and zero. The new Agda source writes a negative original C3-only `ConsumerNonDescentWitness`, a positive original Phase4 `FactorsThrough`, and a traced full `RH.Source4` with both nonzero cancelled pi/3 components and all index fields.

For **INTEGER q only**, the joint quotient is `(q mod3, q mod4)`. Classical Chinese remainder identity
```text
q mod12 = (4*(q mod3)+9*(q mod4)) mod12
```
recovers all twelve classes. The original `C3.Residue3×Phase4` is 12 states, and advancing BOTH source generators gives a single length-12 orbit: fourth iterate advances C3 alone, ninth advances C4 alone, twelfth returns. New Agda has all12 `refl` cases for these three orbit laws. This 12 is an **angular/frequency quotient cardinality**, NOT 12 physical dimensions or replacement for H05's 12 arrows.

## 3. Same actual finite joint operator, not mere numerical phase parity

On the exact 12D space `V=Fun(C3×C4,Q)`, let `Z` advance both native source cyclic labels. Then `Z^4=T3`, `Z^9=T4`, `Z^3=T4^-1` (the last agrees with the symmetric fourth-difference). The REAL original RH atomic angular signed operator evaluated at the RIGHT C4 shift is
```text
B_RH= -(20/351)(Z^3+Z^-3-2I)^2,
```
and the native original `P3/C3` finite stroboscopic time operator is
```text
U(pi)= (2/3)(I+Z^4+Z^-4)-I.
```
These are concrete nonidentity 12×12 rational matrices with `[B_RH,U(pi)]=0`, `U(pi)^2=I`. `B_RH` has rank9 and exact eigenvalues `0×3, -80/351×6, -320/351×3`; its actual Fourier-notch kernel has dimension3, with **one** U(pi)=+1 mode (q=0) and **two** U(pi)=-1 modes (q=4,8). The distinguished `q=4` RH observed-zero Fourier mode has native U(pi) phase -1, NOT a zero eigenvector of U(pi), and NOT a zero of ζ(s). This is the exact signed/zero-aware geometric commuting square omitted by the C3-only model.

For real nonINTEGER q, `q mod3` is NOT a valid character of finite C3 (characters of C3 require integer exponent q). The correct actual original RH angular observer is the continuous circle phase `z(q)=exp(i*pi*q/2)`, with `F(q)=-(20/351)(z+z^-1-2)^2`. One may pair this C4-angle circle with a SEPARATELY SOURCED native integer spatial wavevector and the original k/time/H05 history indices, but never collapse analytic q, spatial wavevector and Singer G eigenlabel to one fictitious integer.

## 4. NEW global REAL-q quartic coercivity: a quantitative analytic min-cut

Let `d(q)=dist(q,4Z)∈[0,2]`. Because `|sin(pi*q/4)|=sin(pi*d/4)` and, for `0≤x≤pi/2`, `2x/pi≤sin x≤x`, the SOURCE original atomic real-frequency Fourier response satisfies rigorously:
```text
(20/351) d(q)^4  ≤  -F(q)  ≤  (5*pi^4/1404) d(q)^4.
```
The constants are EXACT, and the near-notch jet is `F(4n+δ)=-(5*pi^4/1404)δ^4 + (5*pi^6/33696)δ^6 + O(δ^8)`. Thus for any probability measure ν in q with nonzero mass off 4Z,
```text
integral (-F(q)) dν >= (20/351) integral d(q)^4 dν >0.
```
This is a genuine uniform lower bound for NEGATIVE ATOMIC angular response after **q-variable smoothing**; it is NOT the original finite-R positive-radius *angular bump* smoothing! The original RH source already records that the actual finite-t positive-radius q=4 kernel can be POSITIVE, so our atomic statement cannot be transferred to that kernel by handwaving.

**Sharp next ORIGINAL physical source criterion:** write actual finite-source `F_(R,t)(q)=F(q)+E_(R,t)(q)` only after proving a same-normalization source identity. To transport the global atomic sign uniformly near the notches, require an exact weighted-error estimate `|E_(R,t)(q)|< (20/351)d(q)^4` on the controlled interval (or a stronger source-specific signed comparison), with explicit orders 0,1,2,3 vanishing at q=4n where appropriate. A merely uniform additive `O(t^-1)` error is insufficient to guarantee sign arbitrarily close to any notch. More importantly, neither F sign nor q-smoothing alone pays the ORIGINAL marked actual-zero/µ and signed FarExact A2 terminal. Keep both original positive-pole and signed-slack estimates intact.

## 5. Status and ownership

**Exact PASS locally:** source-directed Lacan/Irigaray graphs and all six relabellings, full P3/Irigaray/C3 rational spectral comparison, all 12 CRT/four-phase finite integer responses, 12D exact operator commutation, 9/3 rank/kernel with 1(+)/2(-) split, real-q quartic symbolic jet, 2401 grid probes and exact trigonometric inequality derivation. Files `scripts/check_rh_angular_c3_c4_grammar_mixed_consumer_20261123.py`, `scripts/check_rh_atomic_real_angle_quartic_coercivity_20261123.py`, and `DASHI/Analysis/RHFourWindowAngularC3C4SufficientConsumerExact.agda`. Agda and Lean kernel acceptance NOT run, no numerical grid is a replacement for the mathematical sine inequalities. Original H05 eight-vertex/twelve-map/six-face structure, source 13/26 orientation/sign, and k/time transport remain separate and can be jointly tagged without inferring a physical isometry.

**P0 physical endpoint remains:** original actual ζ-zero multiplicities/local-fourth discrepancy, smooth μ, signed `FarExact`, compensation threshold, finite positive-radius/high-pole transfer, A2 strict inequality and RH/GRH are OPEN. The geometric result is an exact selected source-correct angular-frequency quotient/operator, with an actual quantitative atomic sign estimate—not an analytic RH proof.
