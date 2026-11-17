# KSW668 F8 — maximum-cut XL: S3/C3 / YM S³ donor crosswalk

**18 November 2026.** PR [#1527](https://github.com/chboishabba/dashi_agda/pull/1527), original AdS5 moving brane a=t, three F8 radial multipoles ell=0,2,4. This is a **same-object proof-compression adapter**, not a physically established S3 or SU(2) symmetry. Agda kernel acceptance remains pending.

## 1. Three different exact mathematical carriers

1. **DASHI 3-coordinate permutation group S3/C3:** source-owned `DASHI/Foundations/TernaryPermutationS3LawsExact.agda`, `DASHI/Foundations/PolynomialC3S3OrbitSamplingProjectionExact.agda`, `scripts/check_polynomial_c3_s3_reynolds_character_exact.py`. The source 27-ternary-code orbits (C3:11 classes, S3:7 functional-graph classes) have a specific endomorphism-conjugation action. **They are not the original F8 three modes.** We reuse the abstract finite *coordinate-permutation/Reynolds proof pattern*, not the 27-state ontology or representatives. The original 27-code sampling projector is also distinct from the rational Reynolds average on three mode positions.
2. **YM rational S³ cubature:** source-written `DASHI/Physics/YangMills/YMClayRationalS3DegreeFifteenInvariantCertificateExact.agda` in the independent YM branch (the original 1,464 positive rational SU2 nodes). Its signed-coordinate permutations act on quaternion coordinates `(q0,q1,q2,q3)` with `sum q_i²=1`; `e2,e3,e4` reduce degree-15 symmetric invariant moments to eleven source equations. This is a *4-coordinate S³* (the compact group SU(2)); it is neither `S3` (six three-coordinate permutations), nor `C3` (three cycles), nor the F8 **physical** angular S²/azimuth S¹.
3. **Original F8 mode carrier:** `ell=0,2,4`, native effective radial dimensions `d=3,7,11`, with different shell volumes `W_d,j` and radial operator `L_d`. This is an ordered triple of **inequivalent original radial channels**, not the YM quaternion and not a source-defined C3 physical representation.

## 2. Positive cross-pollination: one normal theorem, three weighted instances

The original F8 `normal_order=3` characteristic SBP2, moving warp `-3(P-M)/(2z)`, and weak-Israel/outer SAT **use identical coefficient formulae across all three modes**, once a mode's own radial force/source is supplied as data. For a mode-independent rational stage map `f` and any of the original six `S3.TriPermutation` constructors, the three-coordinate **relabeling** identity is
```
map3(f, action(p, X)) = action(p, map3(f, X)).
```
This makes one generic XXXVIII/XXXIX normal/warp/SAT energy proof reusable for all three original radial modes.

For any fixed radial shell index j, each mode has its own **positive** original FV volume `W_(3,j),W_(7,j),W_(11,j)`, and its own normal energy `E_(ell,j)` and commutator residual `R_(ell,j)`. Multiplying `|R_ell,j| <= (12/b) E_ell,j` by the positive native shell mass and summing (also over j) yields the **genuine full-three-channel, radial-indexed normal/warp estimate**:
```
|sum_(ell,j) W_(3+2ell,j) R_(ell,j)|
 <= (12/b) sum_(ell,j) W_(3+2ell,j) E_(ell,j),
0<dy<=b(T), -1<v(T)<0.
```
The local exact-rational audit checks this for all three native d values, several original j and several y-node counts. This result **excludes radial forcing and its moving shift**, which couple the radial shell gradient to the U/P/M system. It is not a full G3 energy estimate. Its arithmetic positive-weight/absolute-value order argument is independently verified but **not yet kernel accepted in Agda**. Finite rational Agda companion `KSW668F8ThreeModeWeightedNormalEnergyReynoldsExact.agda` proves the weight-distribution/relabel algebra, not the order lift.

## 3. Exact sharp obstruction: C3 rotation is NOT a physical radial symmetry

The original FV radial **origin** row is `(L_d V)_0=2d (V_1-V_0)/h²` for `d=3,7,11`. In grid units the diagonal operator on the three radial differences is
```
L_origin = diag(6,14,22)
         =14 I + diag(-8,0,8).
```
For the mode-label cycle `R(x0,x2,x4)=(x2,x4,x0)`:
```
[L_origin,R](x0,x2,x4)
  =(-8 x2, -8 x4, 16 x0), not zero.
```
Its C3/S3 Reynolds-average projector `P x=(mean(x),mean(x),mean(x))` obeys `P²=P`; the mode-symmetric origin part is `14 I`, but the asymmetric operator defect is **unavoidable**, not a removable choice of orbit representatives. Moreover
```
mean(L_origin x)=14 mean(x)+(8/3)(x4-x0).
```
Already at the original first shell (unit radial spacing), the true masses are **W3,0=1/24, W7,0=1/896, W11,0=1/22528**. Rotating the fields without also rotating these masses is NOT an isometry of the physical weighted energy. Rotating *fields, coefficients, sources and weights together* is valid relabeling, but cannot simplify the physical unequal-coefficient dynamics.

The first interior row also has distinct exact shell coefficients (from the original first-cell owner):
```
d=3:  (c+,c-)=(27/13,3/13)
d=7:  (5103/1093,7/1093)
d=11: (649539/88573,11/88573).
```
Hence the C3 origin obstruction persists in the actual original radial FV operator. The source does **not** have a hidden C3 operator equivariance or S3 symmetry of the physical action.

## 4. YM S³ design: useful proof tactic, not positive-energy shortcut

The YM sign/permutation invariant design suggests **compressing a genuinely invariant, already-grounded polynomial certificate to orbit generators**, not enumerating every monomial. For F8, a concrete future use would be to derive a small symbolic invariant/SOS certificate for a **properly normalized coupled quadratic or quartic energy defect** if (and only if) its symmetry subgroup is proved on the actual native weighted state. This could reduce the number of Agda proof obligations in the higher-Sobolev G4 multi-jet energy ledger.

But simply matching `S³` moments or averaging a polynomial is not a pointwise positivity theorem: on the rational unit S³, `q0²-q1²` takes both +1 and -1. Thus a valid averaged invariant formula can hide an **unstable anisotropic direction**. The new mode adapter includes both exact sign witnesses. **Do not** import the YM degree-15 quaternion measure as the physical F8 angular measure or treat C3 permutation of (U,P,M) as a symmetry: those three variables have different dynamical roles and SAT closures.

## 5. New verified artefacts and acceptance

- `DASHI/Physics/Gravity/KSW668F8C3S3ModeReynoldsRadialObstructionExact.agda`: imports original S3 permutation constructors; defines the rational three-mode C3 Reynolds averaging, its idempotence, the common-stage naturality, actual radial-origin diagonal and its nonzero three-component commutator, Reynolds residual and non-invariance of original shell mass.
- `DASHI/Physics/Gravity/KSW668F8ThreeModeWeightedNormalEnergyReynoldsExact.agda`: full-three-mode shell-mass-dependent algebra, simultaneous relabel invariance, distribution and source-residual aggregation, and the explicit YM S³ positive/negative controls.
- `scripts/test_ksw668_f8_c3_s3_mode_reynolds.py`: **4,556/4,556** independent exact Fraction tests: six permutations, C3 Reynolds idempotence, all-mode normal stage and original radial asymmetry, actual native origin/first-interior FV values, physical mass noninvariance, and weighted multi-mode normal+warp residual bound.
- Both owners imported through `KSW668F8SameObjectWeylAuthorityBoundary.agda` into the existing KSW/TOE route. Original YM / polynomial S3/C3 source attribution remains with their original owners; no ESD edits.
- **Agda pinned kernel NOT RUN**, and the original YM complete orbit/basis induction and Bishop Haar/C3 gates are not thereby accepted.

## 6. Ordered remaining max-cut

**Next G3:** retain full native unequal mass matrices; use the XXXIX `Q=(P-M)/2-D_yU` constraint to turn the moving radial shift into normal SBP face terms plus SAT boundary Q defect. Construct a *single* original time-dependent `z^-3` weighted **radial-gradient + characteristic** energy, including outer Dirichlet and origin V0. Apply source XXXIX all-v Israel cap, then derive a radial/normal grid-uniform semidiscrete bound and a separate SSPRK3 amplification/CFL certificate. The new S3/C3 decomposition is a diagnostic and proof compression at the normal block; it does not remove the radial coercivity/trace wall.

G1 full tensor gauge/FV/Weyl still OPEN; G2 full joint weak-Israel/radial boundary energy OPEN; G3 fully coupled SSPRK3 OPEN; G4 moving higher-Sobolev both-Weyl OPEN; G5 three-axis convergence OPEN; G6 original matter/FIO/detector OPEN.

**Attribution:** signed permutation/Burnside/Reynolds and Pólya mathematics is classical. Original DASHI YM S³ construction and original polynomial S3/C3 owners are explicitly reused without reassignment; user-directed F8 crosswalk and local regression are new derivative work. See Dixon & Mortimer (1996) *Permutation Groups*, DOI 10.1007/978-1-4612-0731-3, and the existing YM source-cited quaternion cubature/analysis references.
