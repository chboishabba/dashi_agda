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
