# Actual nonflat 26D NS-NS string background: SU(2) flux × spacelike linear dilaton
Date 2026-10-24. Canonical continuation of [Agda hyperfabric #1249](https://github.com/chboishabba/dashi_agda/pull/1249) and [Lean TOE #84](https://github.com/chboishabba/dashi_lean4/pull/84).

## Prior-source status, not a new string discovery

This is the standard SU(2) WZW / round-S3 NS-NS flux and *spacelike linear dilaton* construction, transplanted into the source-selected 26D **bosonic closed-string effective field equations**. Established worldsheet Sugawara/WZW and NS-NS low-energy action theory remain original mathematical/physical authorities. The Dashi contribution is **an executable source-specific exact rational EOM, geometric connection and finite-level quantum discrepancy audit**, an attribution-respecting selected target for existing 369/VOA/KK/GR operators.

Source action (e.g. [Kevin Wray, *An Introduction to String Theory*, §13.26](https://math.berkeley.edu/~kwray/papers/string_theory.pdf)):
```text
S26 = (1/(2 kappa0²)) integral d26x sqrt(-g)e^(-2 Phi)
      [ R[g] + 4|grad Phi|² - H_ijk H^ijk/12 ],  H=dB locally.
```
Leading NS-NS beta / variational equations (string frame, D=26):
```text
E_g(i,j)  = Ric(i,j) + 2 HessPhi(i,j) - (1/4) H_i m n H_j^m n = 0
E_B(i,j)  = covdiv(e^(-2Phi) H^..._ij) = 0
E_Phi     = R + 4 LaplacePhi - 4|gradPhi|² - H²/12 = 0.
```
This is a two-derivative classical effective calculation, not a full quantized string or all-orders effective action.

## Selected genuine nonflat ansatz, no hidden zero coupling

Let `M26 = R^(1,22) × S³_r` with one Minkowski time direction, 22 flat spatial directions, and round 3-sphere radius `r>0`. Pick `x¹` one of those **flat spacelike** coordinates, not time. Set
```text
Phi = x¹ / r,
H3 = (2/r) vol_(S³_r).
```
On the sphere use the bi-invariant SU2 orthonormal left-invariant frame,
`[e_i,e_j]=(2/r) epsilon_ij^k e_k`,
`nabla_ei ej=(1/r)epsilon_ij^k e_k`. It is torsion-free and metric-compatible.
The actual nonzero curvature `Ric_S3=(2/r²)g_S3`, scalar `R=6/r²`,
`H_i mn H_j^mn = (8/r²)delta_ij`,
`H²=24/r²`, `gradPhi²=1/r²`, HessPhi=LaplacePhi=0.
Therefore:
```text
S³ Einstein beta: 2/r² - (1/4)(8/r²) = 0.
Flat Einstein beta: 0 + 2*0 - 0 = 0.
B EOM:             H parallel in S³, dPhi in orthogonal flat direction -> 0.
Dilaton beta:      6/r² -4/r² - (24/r²)/12 = 0.
```
**This is a literal nonflat coupled leading-order EOM solution** with nonzero source fields, unlike the earlier false flat metric/B example. The FULL 26D geometry exists analytically as the standard SU2 group manifold with the chosen round metric; the executable checks its orthonormal connection, curvature via the structure constants and all source terms exactly. It is not imported from the Agda *three time-slice warped* geometry: same general physical subject, different actual metric.

**GLOBAL B potential warning:** `H3` is a nontrivial closed class on `S³`, so there cannot be a single globally defined smooth `B2` on `S³` with H=dB. The proper global object is patchwise B plus gerbe transitions, subject to flux quantization. `∫_S³ H = 4*pi²*r²`; with standard WZW normalization `r²=k alphaPrime`, `k` is quantized. This local-global failure is part of the acceptance, not an ignorable anomaly.

## Actual 2D conformal/VOA cross-pollination and finite-level negative test

Source WZW Sugawara identity `c_SU2(k) = 3k/(k+2)`, integer `k>=1`; [WZW current algebra](https://adscft.org/cft/two-dimensional-cft-strings-ads3/current-algebras-wzw/). On `R^(1,22)` there are **23 worldsheet free bosons**; one of their spatial coordinate fields has linear-dilaton gradient V and adds `6 alphaPrime V²` to central charge (standard bosonic normalization). Total matter
```text
c_matter = 23 + 6 alphaPrime V² + 3k/(k+2).
```
The bosonic reparametrization ghosts contribute `c_bc=-26`. Thus EXACT criticality requires
```text
alphaPrime V² = 1/(k+2),   c_matter=26,   c_matter+c_bc=0.
```
But the **unshifted leading two-derivative geometry** above with `V=1/r`, `r²=k alphaPrime`, gives `alphaPrime V²=1/k`. Then
```text
c_matter - 26 = 12/[k(k+2)] > 0 at every finite positive k.
```
This explicitly identifies a finite-level quantum correction to the classical balance; the two are compatible at large `k` but NOT exactly the same finite-k physical sigma model. A worldsheet CFT using the source-selected corrected slope is a legitimate existing-construction candidate with central-charge cancellation, **not a kernel proof of BRST cohomology, complete modular sewing, stable vacuum, or α'-exact spacetime equations**. In particular, the bosonic tachyon and linear-dilaton strong-coupling end remain unaddressed.

## Source-owned deliverables and exact checks

- `scripts/check_k27_26d_su2_flux_linear_dilaton.py`: from SU2 Lie bracket, exact rational Koszul/Levi-Civita, Riemann and Ricci, parallel H, sphere/flat B/metric/dilaton NS-NS EOM for six rational radii. All local direct executions PASSED.
- Same script: thirty WZW `k=1..30` rational identities, quantum-corrected `c=26` positive, finite-k classical residual `12/[k(k+2)]` negative. Local PASS.
- Lean #84 `Integration/DASHITOE/K27NonflatNSNSLinearDilatonCut.lean` source writes general ℚ parameter proofs of sphere metric beta, full dilaton beta, timelike-dilaton **counterexample**, exact `k+2` worldsheet charge, and explicit unshifted-slope anomaly. It takes geometric SU2/NS identities as **source premises** (not Lean manifold theorems). Lean/Lake kernel UNVERIFIED.
- Existing SU2/SO3 and group cover formalisms in Agda supply **candidate language only**. The actual `S³=SU2` connected group manifold is not a 27-site balanced-ternary path cube, nor the `C3³` periodic Fourier torus, nor automatically a Monster VOA/BRST state.

## Max-cut roadmap after actual nonflat source completion

**D0** original literal 27D gravity+3form action **FAIL** (125/121) and coefficient-only scalar patch fails automatic EOM. This motivates using 26D theory directly, not unconditional 27D uplift.

**D1** correct physical 26D matter and fields **PASS at leading NS-NS continuum** for chosen S3 flux/linear dilaton. This is stronger than earlier flat toy or target-only EOM record and removes the *mathematical existence* blocker for one nonflat NS-NS continuum example.

**D2** source-published worldsheet CFT via SU2k/current algebra + spacelike background-charge flat boson has exact `c_matter=26` upon `alpha'V²=1/(k+2)`; the large-k geometric ansatz predicts only `1/k`. **Finite-level same-background matching OPEN**. It is crucial not to replace k+2 with k or equate central-charge arithmetic with a full local/unitary BRST CFT.

**D3** B2↔dual C22 positive local Hodge and physical 299+276+1 from the separate K27/M24 source ledger. A full K27 Lie-generator, dual 22-form in a globally nontrivial B gerbe, same stress/metric and genuine on-shell physical Hilbert state remain open.

**D4** M24 p276 ordinary duad != antisymmetric string B2 under natural M24 action, SOURCE-EXACT character 2A 36≠20 and 2B 12≠−12. The ORIENTED duad local Z2 line corrects the representation, but not a Monster Tate 276 or signed-neutral C3 meaning by fiat.

**D5** physical 369/Monster claim would require a selected operator-preserving state/field map from the original hypervoxel/VOA candidate to the SU2 WZW × linear-dilaton 26D CFT and continuum g,B,Phi. No such map is presently identified. NS/YM/RH/other Clay owner estimates receive no automatic theorem promotion from this background.

## Independent high-value subsequent experiment

Give the selected SU2 WZW k and level-corrected linear dilaton a precise physical worldsheet realization, compute Virasoro/BRST nilpotence and physical-state cohomology using existing VOA/TwistedModule owners, and compare the induced spacetime NS-NS background at alpha' corrected order. Fail closed if background level shift or stress does not match. Then ask if the 369 hyperfabric admits an action-preserving operator map at all; do not start from equal numerical labels.


## 2026-10-24 source-snowball / explicit global-gerbe + affine VOA max-cut

**Most relevant original source found on the WEB:** Michael B. Schulz, *T-folds, doubled geometry, and the SU(2) WZW model*, JHEP06(2012)158, https://arxiv.org/html/1106.6291v4 . The author's §2.1 and Appendix B already construct **the physical WZW target g,H and quantum current/Sugawara/primary states**, and §3–4 develop the much more appropriate **worldsheet momentum/winding doubled bundle** and `O(d,d)` generalized geometry for physical string transport. This is a stronger *operational* bridge to the user's hyperfabric and KK/p-adic refinement programme than 27 vs 26 numerology. DO NOT install a new Courant/T-duality framework merely from this citation: to use it one must implement a SAME sigma-model momentum-winding generalized metric `TM⊕T*M`, `B`-shift, patch cocycle and corresponding worldsheet Hamiltonian on the actual selected 26D fields. The existing original mathematical owners are the (SU(2)_k) affine-level `DASHI/Physics/QFT/KacMoodyLevelReceipt.agda`, `SU2Level4Spin1RepReceipt.agda` (literal k=4 j=0,1/2,1,3/2,2 and h=0,1/8,1/3,5/8,1), `LevelRankDualityReceipt.agda`, `DASHI/Moonshine/VertexOperatorAlgebraCore.agda` and `TwistedModuleModularity.agda`. The SU2_4 level/spin sources are **already present** and must be reused, not recreated from bare counting. Their separate SM-weak, p3 conductor and duality interpretations remain source-candidate and are NOT imported into physical bosonic string gauge coupling by notation.

**Additional primary quantum source:** standard SU(2)_k affine Sugawara `h_j=j(j+1)/(k+2)`, `c=3k/(k+2)`, e.g. https://www.sciencedirect.com/science/article/abs/pii/S0550321306009321 (2007 original SU(2) extended-algebra analysis). See also https://www.conferences.itp.phys.ethz.ch/esi-school/Lecture_notes/WZW%20models.pdf for state/character expansions. Exact 2D WZW CFT **exists in published theory**, not source-created by our numerical representation checks. Linear dilaton bosonic central charge `D+6 alpha' V²` has external textbook/research authority. The April 2026 published Biswas DDF https://doi.org/10.1007/JHEP04(2026)076 treats a **LIGHT-LIKE** dilaton only: it is relevant to future physical-state algebra, but must NOT be silently substituted for this strictly SPACELIKE dilaton background.

### NEW actual global target-space forms: B gerbe cannot be a single B2

Use round S³ polar angle `0<=chi<=pi`, S² volume `omega2=sin(theta)dtheta^dvarphi`, radius r, `H=(2/r)vol_S³=2r² sin²(chi) dchi^omega2`. Set `f(chi)=chi-sin(2chi)/2`; then two regular patch potentials are

```text
B_N = r² f(chi) omega2       (regular at north chi=0)
B_S = r² (f(chi)-pi) omega2  (regular at south chi=pi)
dB_N = dB_S = H.
B_N-B_S = pi r² omega2 on their overlap;
int_S² (B_N-B_S) = 4 pi² r² = int_S³ H.
```

Because the overlap S² two-form has nonzero integral, it is **not** globally exact there; one cannot use a single globally smooth gauge 1-form to glue both patches. The correct global B is a **U(1) 2-gerbe connection / bundle-gerbe with higher patch data** (in string terminology, a B-field gerbe), and `[H/(4pi² alpha')]` has integer WZW level k. With source semiclassical convention `r²=k alpha'`, `int H/(4pi² alpha')=k`, (kin Z_{>0}). The exact local potential and flux calculation has been independently executed in SymPy (not yet kernel-proved in Agda/Lean). Do not confuse this U(1) gerbe cocycle with the **Z2** oriented-duad local sign or **C3** signed-neutral-phase rotation.

### NEW actual explicit C22 on THE SAME nonflat source metric

Choose product orientation `vol26 = vol_(R1,22)^volS³`, mostly-plus metric and `Phi=x¹/r` where x¹ is FLAT **spacelike**. For H=+(2/r)volS³, the Lorentzian Hodge convention then gives `*26H=-(2/r) vol_(R1,22)`. Define `beta22=dt^dx²^...^dx²²`, for which `dx¹^beta22=-vol_(R1,22)`. The **global smooth potential on the noncompact R1,22 factor**:

```text
C22 = -exp(-2Phi) beta22
dC22 = -(2/r)exp(-2Phi) vol_(R1,22)
     = exp(-2Phi) *26 H3 =: G23.
```

Thus the previous literal coupled NS-NS source background (all *leading* equations) now carries an actual **same-background B2/C22 dual potential**, not just degree-22 counting. `dG=0` is the B equation; `d(e^(2Phi)*G)=dH=0` uses Lorentzian `**=+1` on degree 3/23 under the stated orientation and a local Bianchi relation. The globally topologically nontrivial H has no global B2, whereas its dual G23 on noncompact R1,22 **is exact**, explaining why a global C22 can be given here without claiming global `B2`. This explicit POTENTIAL is a legitimate source-field representative; it is **not** the `K27` infinite-dimensional Lie generator corresponding to a 22-form. Source primal/dual potential construction itself is established Hodge/gerbe prior art.

### Exact quantum CFT operational discriminators

Script added: `scripts/check_k27_26d_global_gerbe_dual_cft.py`.
Independent exact SymPy/Fraction and 50-digit mpmath reference run PASSED:
- both patch potentials with `dB=H` and overlap class; full integral `4pi²r²`;
- WZW integer levels (k=1..20);
- explicit dilaton-weighted global C22 primitive on flat factor with the correct Lorentzian Hodge sign;
- 20 source-exact SU2 WZW (c_{SU2}=3k/(k+2)) with (c_{matter}=26) when `alpha'V²=1/(k+2));
- **135** SU2 integrable primary (k=1..15, `ell=0..k`) weights `ell(ell+2)/(4(k+2))`;
- standard source SU2 affine modular matrices (12 levels) numerically satisfy `S²=I` and `(ST)³=S²` with 50-digit errors below `10^-42`.

**IMPORTANT TEST STATUS**: the SymPy rational/analytic identities are exact; `S,T` modular identity checks are numerical, not symbolic nor a new theorem about the infinite algebra. The full noncompact linear-dilaton string partition function, physical Hilbert positivity, ghosts, complete BRST and modular sewing are **not** established by the affine-sector modular test. The checked local source version is mathematically equivalent to GitHub committed source; **the exact committed blob has NOT been byte-executed in this turn**. Original literature authorship is not claimed as DASHI novelty.

### A finer α' / same-source negative test

For classical r²=k alpha' and the **quantum-corrected** slope `alpha'V²=1/(k+2)`, the simple two-derivative dilaton equation gives a remaining residual (multiply by alpha'):

```text
alpha' [R-4V²-H²/12]
  = 6/k - 4/(k+2) - 2/k
  = 8/[k(k+2)] > 0 .
```

This is NOT evidence against the conformal WZW background: it demonstrates that substituting the exact worldsheet background charge into the *unshifted classical* target fields without the proper higher-order α'/field-redefinition corrections is invalid at finite k. A physical same-object bridge needs a source-specified renormalisation scheme and target-frame map. Merely renaming radius to `k+2` while holding H quantization and curvature fixed can also violate the global gerbe integer and local flux relationship; independently test each source-normalized term before accepting a level shift.

### Strong remaining programme after this cut

**E0 DONE:** discover primary WZW / doubly extended string geometry / exact CFT literature, cross-check original SU2 WZW level4 and VOA owners. No new 369 ontology.

**E1 DONE exact geometric source test:** nonflat classical 26D metric/H/Phi EOM; explicit global patch B gerbe with integer WZW class; on exactly same background explicit global dual C22. Existing finite classical/check receipts and new SymPy exact test. Pending kernel proof of manifold/gerbe and differential-form operators.

**E2 DONE source-selected exact worldsheet model (external theorem authority):** standard SU2_k affine CFT plus 23 free bosons (one spacelike background-charged) at `alpha'V²=1/(k+2)` has c26; source S/T modular group and all integrable modules are known. Repo has multiple actual SU2 level CFT-labelled donors. Agda/Lean **kernel-local VOA instantiation and physical BRST** are unproved.

**E3 OPEN physical SAME quantum-classical target:** exhibit exact scheme-controlled map SU2_k WZW stress/OPE, target g/H gerbe, level shift and beta functions beyond tree order. Correct finite-k α' mismatch above is a concrete falsifier.

**E4 OPEN genuine K27 generators and duality:** construct selected Lie generators and dual-potential action on this same global gerbe background, not just matching 22-form degree.

**E5 OPEN hyperfabric operators and oriented fibre:** a 27-site ternary cube is not the SU2 group manifold or affine module. Also `SO(24)` little-group 299+276+1 is the **FLAT vacuum/tangent-space** decomposition, not a global `SO(24)` symmetry of the curved SU2-flux and preferred-gradient solution; this background BREAKS much of the flat Lorentz symmetry. M24-duad 2A/2B mismatch is a mathematical representation result on chosen natural M24 action, not an observed M24 symmetry of this curved target. Any 369 representation map must explicitly respect these distinctions.

**E6 OPEN full spectrum/viability:** global worldsheet completion, physical BRST, modular invariant closed-string sector and noncompact coupling. `g_s=e^Phi` diverges at one end of the spacelike linear dilaton, and standard bosonic-string tachyon is not removed; this background is not a stable realistic observed vacuum. No YM/NS/RH/BSD/Hodge/P≠NP theorem is gained without the original analytic source estimates.


### Latest E1→E3 concrete WORLD-SHEET HAMILTONIAN same-object bridge

Source: Schulz (2012), https://arxiv.org/html/1106.6291v4 ,
§1, §3, Appendix B. The original physical phase-space
model is not a generic 27/729 symbolic analogue:
`(v,p)∈TM⊕T*M`, with local worldsheet quadratic
Hamiltonian
`E_B(v,p)=vᵀg v+(p+Bv)ᵀg^{-1}(p+Bv)`.
On the ACTUAL round S3 gerbe charts already constructed,
`ΔB=B_N−B_S=pi r² ω2`. Under the
same-source patch change
`(v,p_S)→(v,p_N)`,
`p_N=p_S−ΔB v` for this convention,
the full quadratic form agrees exactly:
`E_(B_N)(v,p_N)=E_(B_S)(v,p_S)`.
The antisymmetry of ΔB also preserves the
natural `O(3,3)` pairing on `T⊕T*`.

**New exact executed test**:
`scripts/check_k27_wzw_gerbe_od3_hamiltonian.py`
calculates the ENTIRE symbolic 6×6 `O(3,3)` B-shift
`T^T eta T=eta`, the conjugate
generalized metric
`T^T M(g,B_N) T=M(g,B_S)`,
and 27 exact equatorial (three radius × three
winding × three momentum) phase-space examples.
Independent local symbolic script PASS.
This is a real physical model patch law, although
the standard B-transform theory is external
prior mathematics. The published source's
worldsheet action/Hamiltonian remains distinct
from DashI finite 27-site graph Laplacian
and the Monster VOA operator.

**Crucial global boundary**:
because `∫overlap_S2 ΔB=4pi²r²≠0`,
ΔB is not globally exact on the whole overlap;
the patch relationship is locally canonical,
but global consistency requires the higher
U(1) gerbe rather than one global shift by
a globally defined 1-form.
This is a genuine geometric/descent cut for
the user's hyperfabric formalism.
`O(3,3)` B-transform, `Z2` oriented
duad sign, `C3` signed-zero phase,
and the later proposed `O(26,26)`/K27
target representation are separate.
No physical 369→WZW equivalence follows.

**Repository follow-through**:
Lean #84
`Integration/DASHITOE/K27GerbeWZWC3OrientationCut.lean`
now contains direct ring-identity **SOURCE-WRITTEN**
local Hamiltonian and O(2,2) pairing invariance
in the B-supported angular tangent plane.
No Agda/Lake exact-head kernel receipt.
The exact GitHub Python blob was not executed
byte-for-byte; equivalent local SymPy run PASS.
The next honest physical cut is to *select*
an explicit discretization/operator-preserving
map from the original hypervoxel to the
actual WZW momenta, winding and gerbe charts,
not to postulate its existence.


## 2026-10-24 Witten 1989 vs Witten 2007 theorem-owner integration

Do NOT overindex a single word “Witten”. The source-grounded current
programme owns TWO radically different 3D/2D constructions:

- **Witten 1989** CS/Jones, `SU2_4` 3D topological Chern–Simons
  with a 5-dimensional chiral torus conformal-block space
  controlled by the SU2_4 affine WZW S/Verlinde fusion category.
  The standard chiral 2D WZW current algebra can also be used
  as the INTERACTING worldsheet factor of our independently
  selected 26D bosonic string on S3. The full worldsheet is a
  nonchiral sigma model with left/right and ghosts, NOT the
  3D CS bulk.
- **Witten 2007** AdS3 pure/chiral gravity candidate with
  holomorphic Monster `Vnatural` c24, one chiral VOA
  irreducible module, partition J. Existing original Agda
  sibling PR #1239 already implements source J finite coefficients,
  Virasoro primary subtraction, B3/SL2Z and many literal
  Monster C27 projectors. This is a still-conjectural
  GRAVITY bulk dual; Maloney–Witten 2007/2010 supply
  an explicit caution about unphysical naive saddle sums.

The new source-specific exact script
`scripts/check_witten_su2_4_cs_wzw_monster_chiral_cut.py`
checks the real Witten 1989 SU2_4 S matrix in `Q(sqrt3)`,
all 125 SU2_4 Verlinde fusion coefficients and 625
associativity equations, quantum dimensions
`[1,sqrt3,2,sqrt3,1]` (squared dimension12),
and Gauss–Milgram framing anomaly phase
`exp(2pi i c/8)=i`.
Holomorphic c24 Monster has one chiral module and
trivial phase1: **not directly the same modular
tensor category** (5 vs1, i vs1). Both can be
ingredients of a larger specified construction,
but not identified merely because CS and AdS3
both have 3D bulks and modular boundary CFTs.

An equivalent exact local script executed PASS; new
Agda thin consumer of `SU2Level4Spin1RepReceipt`
and `JCoefficientCharacterBridge` plus Lean fusion
ring sources are **kernel unverified**.
Canonical new source and roadmap:
`docs/hyperfabric-witten-cs-wzw-monster-ads3-source-maxcut-20261024.md`.

Correct physical acceptance remains exact **same WZW**
SU2_k current modes, k+2 scheme, global S3 H gerbe,
the worldsheet `O(3,3)` momentum/B patch Hamiltonian,
and BRST state spectrum for a 26D string; no leap
from SU2_4 CS conformal blocks to physical
Monster/AdS3 gravity or the original 27-site cube.


## Witten principal SU2_4 ⊂ SU3_1 operator extension is now source-tested

Primary literature Lacki/Zaugg 1989 DOI
10.1016/0370-2693(89)90662-X, rather than
hypothetical 369 colour from counts. A new
actual `sl2⊂sl3` rational 3×3 principal
embedding has trace index4 and adjoint `3+5`,
which induces source affine SU2_4 level
from SU3_1 level1. Conformal c matches
`3·4/6=8/4=2`.
Source SU3_1 vacuum restriction `0⊕4`,
two distinct fundamental/antifundamental
restrictions to WZW label2 yield
`D4=|chi0+chi4|²+2|chi2|²`.
Actual source exact modular branching,
D4 S/T and 27/81 SU3_1 Verlinde/associativity
checks all PASS on independent local SymPy
source. After Z2 simple-current extension
the pointed category is SU3_1 C3, which
does NOT exist as three invertible objects
in unextended SU2_4.

This corrects the roadmap's previous
“only 5 different SU2 labels; SU3 candidate
still just 3 numerically suggested”: there
is a genuine established CONFORMAL EXTENSION.
It does **not** identify the SU3 sigma target
dim8 with the round SU2 S3 target dim3
or solve the full 26D quantum string BRST,
nor provide an SU3_1 physical colour
gauge group/Monster c24 quantum gravity.
Canonical original and repo owner matrix:
`docs/hyperfabric-witten-d4-conformal-su2-4-su3-1-current-embedding-maxcut-20261024.md`.
Native Agda/Lean branch proof sources committed
but Agda/Lake kernel UNVERIFIED.
