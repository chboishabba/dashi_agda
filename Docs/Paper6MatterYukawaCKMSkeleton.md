# Paper 6 Matter, Yukawa, CKM, and Penguin Draft

Date: `2026-05-29`
Status: docs-only substantive draft; fail-closed; non-promoting

Contribution claim: the current repository supports a carrier-side matter
surface in which Yukawa entries, ultrametric depth slots, symbolic
off-diagonal up-sector entries, and alpha diagnostics form a suppression
pattern consistent with the observed fermion hierarchy.  This is a structural
and diagnostic claim about the carrier geometry.  It is not a derivation of
physical fermion masses, the Cabibbo angle, a non-identity physical CKM matrix,
or rare-decay empirical adequacy.

The central rule for this paper is simple: the draft may use inhabited carrier
receipts as typed data, but it must not promote any physical statement whose
promotion bit is still false.  In particular,
`CabibboAngleCarrierReceipt.agda` records
`yukawaSuppressPatternConsistent = true`, while `cabibboAngleDerived = false`;
`CKMVusCarrierPredictionTargetReceipt.agda` records the current carrier CKM
matrix as identity and the `|V_us|` target as comparison-only; and
`YukawaFromCarrier.agda` keeps `physicalYukawaPromotionConstructed = false`
even after exposing diagonal and symbolic off-diagonal carrier entries.

## Abstract

We describe the matter/Yukawa/CKM frontier currently formalized in DASHI as a
fail-closed carrier geometry.  The positive content is a concrete carrier-side
Yukawa package: canonical up/down `3x3` matrices, carrier flavor bases,
identity CKM transport on the diagonal canonical carrier, DHR/Yukawa formula
access, first-generation ultrametric depth data, and an upper-triangular
up-sector off-diagonal receipt with symbolic inter-lane/depth suppression.
These receipts support a limited hierarchy statement: the carrier geometry
exhibits a Yukawa suppression pattern compatible with the qualitative ordering
seen in fermion masses, and it exposes alpha diagnostics that can guide a
future frozen ratio-comparison protocol.

The paper deliberately stops before physical promotion.  The alpha readbacks
are derived from fermion-mass ratio diagnostics, not accepted constants.  The
two alpha estimates currently recorded do not agree as an accepted common-alpha
receipt.  The off-diagonal up-sector entries are symbolic carrier data with an
unknown physical coupling scale.  The current carrier CKM matrix remains the
identity, so nonzero CKM mixing and CP violation are not derived.  The Cabibbo
target `theta_C = arcsin(alpha1 * g12)` is recorded as a target form only:
`g12`, an arcsin error bound, PDG authority binding, and a non-identity physical
CKM diagonalizer remain absent.

## 1. Scope and Claim Discipline

Paper 6 should be read as a receipt-indexed paper about a carrier construction,
not as a phenomenology paper claiming calibrated Standard Model masses.  Its
allowed positive claim is:

- the carrier surface contains finite typed Yukawa data;
- the carrier/DHR formula surface exposes matrix-entry access;
- the up-sector now has explicit upper-triangular off-diagonal carrier entries
  `y12`, `y13`, and `y23`;
- the alpha diagnostics and depth suppressions are consistent with a
  hierarchy-pattern interpretation;
- the Cabibbo and `|V_us|` surfaces name falsifiable next targets.

Its disallowed claims are equally important:

- no physical fermion masses are derived;
- no absolute Higgs/VEV/W4 calibration is supplied;
- no accepted running-mass scale convention is bound;
- no accepted common alpha is promoted;
- no physical Yukawa matrices are supplied;
- no non-identity physical CKM matrix is constructed;
- no Cabibbo angle is derived;
- no P5 prime or Wilson-coefficient adequacy theorem is promoted.

The paper should use language such as "carrier-side suppression pattern",
"diagnostic alpha readback", "comparison target", and "fail-closed blocker".
It should avoid language such as "derived quark masses", "predicted CKM",
"explained Cabibbo angle", or "new-physics fit".

## 2. Receipt Surface

The draft is anchored by four matter-side receipts.

`YukawaFromCarrier.agda` packages the carrier-side Yukawa construction.  It
reuses the exact up/down `3x3` Yukawa matrices from `CKMExactWitnesses`, threads
the Froggatt-Nielsen and Higgs receipts, consumes carrier-derived CKM and CKM
unitarity receipts, and exposes the DHR/Yukawa formula
`Y_ij = <rho_i, Phi_H * rho_j>` as matrix-entry access.  The current carrier
CKM matrix is the identity.  The receipt explicitly records that physical
fermion masses, Higgs/VEV/W4 calibration, splitting-field/eigenbasis lifts,
actual DHR sector representations, and physical Yukawa matrices remain
fail-closed blockers.

`CarrierYukawaRatioTargetReceipt.agda` names the ratio targets the paper may
discuss: `u/c`, `u/t`, `c/t`, `d/b`, `s/b`, `e/mu`, and `mu/tau`.  The up/down
targets are bound to existing canonical carrier-Yukawa entries and to the
DHR formula surface, while the charged-lepton targets remain blocked until a
charged-lepton Yukawa carrier exists.  The receipt also records alpha-ratio
forms for the up-sector diagnostics, but keeps alpha target value, alpha bound,
physical value promotion, and physical ratio promotion false.

`CKMVusCarrierPredictionTargetReceipt.agda` records the first non-identity CKM
target.  The current carrier matrix has zero off-diagonal entries, so the
carrier `v12` entry is zero.  The physical target is stored only as a
PDG-sized comparison datum for `|V_us|`, together with a symbolic target
formula `|V_us|_target(alpha,g_12)=alpha*g_12`.  The receipt keeps the
accepted alpha coupling, off-diagonal coupling evaluation, physical
eigenbasis, exact physical CKM product, PDG authority binding, and error bound
open.

`CabibboAngleCarrierReceipt.agda` binds the ratio and `|V_us|` target surfaces
into a Cabibbo-angle target.  It records
`theta_C = arcsin(alpha1 * g12)` as the carrier form and
`theta_C = arcsin(|V_us|)` as the comparison target.  Its positive statement is
that the Yukawa suppression pattern is consistent at the carrier-diagnostic
level.  Its governing negative statement is that `cabibboAngleDerived = false`
and physical CKM promotion remains false.

## 3. Carrier-Derived Yukawa Texture

The starting object for the paper is not a measured Yukawa sector.  It is a
typed carrier package with canonical matrix data.  The diagonal up/down
Yukawa matrices provide a minimal exact surface on which the carrier CKM and
DHR/Yukawa formula receipts agree.  This lets Paper 6 state that carrier
Yukawa entries are available as formal data and can be addressed generation by
generation.

The new up-sector surface adds the first nontrivial texture information the
paper should emphasize.  `YukawaFromCarrier.agda` contains an
`UpperTriangularUpOffDiagonalYukawaCarrierReceipt` with three upper-triangular
slots:

| Carrier slot | Receipt interpretation | Stored carrier suppression |
| --- | --- | --- |
| `y12` | first-second inter-lane entry | real `1/5`, imaginary `0` |
| `y13` | first-third depth-suppressed entry | real `1/25`, imaginary `0` |
| `y23` | second-third inter-lane entry | real `1/5`, imaginary `0` |

The receipt marks `offDiagonalEntriesInhabited = true` and
`physicalCouplingScaleUnknown = true`.  Therefore the paper may say that
symbolic upper-triangular off-diagonal carrier entries have been inhabited with
inter-lane/depth suppression.  It may not say that these are measured
off-diagonal Yukawa values, that the weak/mass basis has been physically
identified, or that CKM mixing follows from them.

The hierarchy interpretation is correspondingly modest.  The diagonal carrier
entries, the first-generation ultrametric depth carrier, and the symbolic
off-diagonal suppressions give a structured pattern in which deeper or
inter-lane entries are smaller carrier data.  That pattern is compatible with
the qualitative fermion hierarchy, but it is not yet a calibrated mass
formula.

## 4. Alpha Diagnostics and Fermion Hierarchy

The alpha diagnostics should be presented as readbacks and test targets, not
as physical constants.  `CabibboAngleCarrierReceipt.agda` records:

- `alpha1` approximately `0.041240`, read back from the existing `m_u/m_c`
  diagnostic;
- `alpha2` approximately `0.085720`, read back from the existing `m_c/m_t`
  diagnostic;
- `alpha1^2` approximately `0.00168`, recorded as within three percent of the
  `m_u/m_c` diagnostic target;
- `derivedFromFermionMasses = true` for the readback;
- `alphaEstimatesAgree = false`;
- `acceptedCommonAlphaPromoted = false`.

This is enough for a falsifiable program but not enough for a physical theorem.
Paper 6 can propose that a future version freeze the experimental mass inputs,
running scale, threshold convention, uncertainty model, fit rule, and rejection
threshold.  It can then test whether a single carrier alpha explains multiple
ratio targets.  The present repository does not yet pass that test because the
two recorded alpha estimates are not an accepted common-alpha receipt.

The draft should make a sharp distinction between three levels:

1. Carrier entries: exact data in the repository's `Matter.MixingMatrix` and
   `Matter.MixingGaussianRationalDatum` surfaces.
2. Ratio diagnostics: readbacks comparing carrier-inspired alpha forms against
   selected fermion hierarchy ratios.
3. Physical masses: calibrated running or pole masses with authority-bound
   scale conventions.

Only the first two levels are present here, and even the second remains
diagnostic rather than promoted.  The third is absent.

### 4.1 Modular j Alpha-Geometry Target

`DASHI.Physics.Moonshine.ModularJInvariantAlphaReceipt` records a new
moonshine-facing alpha target.  It freezes only the classical modular anchors
`j(i)=1728`, `j(rho)=0`, and the Eisenstein elliptic-point statement.  Its
negative fields are part of the claim:

```text
alphaDerivedFromModularGeometry = false
alphaOneDerivedFromModularGeometry = false
alphaTwoDerivedFromModularGeometry = false
alphaValuesPromoted = false
```

This gives Paper 6 a precise next numerical experiment: define a normalized
map from supersingular or CM \(j\)-value separations to the carrier alpha
diagnostics and test whether it reproduces `alpha1 = 0.041240` and
`alpha2 = 0.085720` with a frozen normalization rule.  The current repository
has not done that.  Therefore the honest statement is that modular \(j\)
geometry is a candidate source for the alpha diagnostics, not their derivation.

`DASHI.Physics.Moonshine.MonsterOrderDepthBoundReceipt` supplies a related but
separate target: the Monster-order exponent table is recorded as a conjectural
depth-bound surface, with `depthBoundConjectured = true` and
`depthBoundProved = false`.  This may guide future carrier-depth hypotheses,
but it cannot be used as a physical Yukawa, CKM, or first-principles prime-set
promotion.

### 4.2 CabibboAngleCarrierReceipt Accounting

The Cabibbo receipt should be cited by its exact claim split.  Its positive
content is:

```text
yukawaSuppressPatternConsistent = true
```

This means the carrier-side alpha and Yukawa hierarchy diagnostics are
internally consistent as a suppression-pattern surface.  In particular, the
draft may discuss the observed alignment:

```text
alpha_1^2 ~ m_u / m_c
```

where `alpha_1` is the first alpha readback and the comparison is a
ratio-diagnostic statement.  This should be phrased as "approximately matches"
or "is within the recorded diagnostic tolerance", not as "derives the quark
mass ratio".  The ratio is an input-side diagnostic target, not an output-side
physical mass theorem.

The same receipt fixes the negative boundary:

```text
cabibboAngleDerived = false
physicalCKMPromoted = false
```

These two fields must appear anywhere the Cabibbo target is presented as a
headline result.  The paper may say that the carrier has a Cabibbo target
surface.  It may not say that the Cabibbo angle has been derived.

### 4.3 The Suppression Pattern Claim

The phrase "Yukawa suppression pattern consistent" has a narrow meaning in
Paper 6.  It combines four carrier-side observations:

- the diagonal carrier entries are ordered in a hierarchy-compatible way;
- `alpha_1` and `alpha_1^2` expose a first-generation suppression diagnostic;
- the upper-triangular off-diagonal entries use smaller inter-lane and
  depth-suppressed carrier values;
- the Cabibbo target form connects the first mixing lane to the alpha
  diagnostic rather than to an already-promoted CKM matrix.

This is a structural consistency statement.  It is not a calibrated
phenomenological fit.  It also does not override the fact that
`alphaEstimatesAgree = false` and `acceptedCommonAlphaPromoted = false`.

The manuscript should therefore use the following chain:

```text
carrier texture -> ratio diagnostic -> suppression pattern consistent
```

and should not use:

```text
carrier texture -> physical Yukawa matrix -> CKM prediction
```

## 5. Cabibbo and CKM Target Surfaces

The Cabibbo lane is valuable because it records precisely where a future
non-identity CKM derivation would have to enter.  The target form is:

```text
theta_C = arcsin(alpha1 * g12)
```

This refines the `|V_us|` symbolic target:

```text
|V_us|_target(alpha,g_12)=alpha*g_12
```

The current carrier does not evaluate this target.  `g12` is not supplied as
an accepted physical coupling.  The arcsin approximation has no accepted error
bound.  The PDG-sized `|V_us|` datum is a comparison target rather than a
derived value.  The carrier CKM product is closed only in the diagonal identity
case, so the current matrix cannot be advertised as a physical CKM prediction.

Paper 6 should therefore state the Cabibbo result in two parts:

- positive: the carrier has a typed symbolic form for the first CKM mixing
  target and it is connected to the alpha/Yukawa hierarchy diagnostics;
- negative: `cabibboAngleDerived = false` and `physicalCKMPromoted = false`.

The negative half is not a caveat after the result; it is part of the result.
It prevents the carrier hierarchy pattern from being silently promoted into a
CKM theorem.

### 5.1 Why `alpha_1^2 ~ m_u/m_c` Is Not A Cabibbo Derivation

The relation `alpha_1^2 ~ m_u/m_c` is useful because it links the first alpha
readback to a first/second generation hierarchy diagnostic.  It does not by
itself supply:

- a physical `g12`;
- a physical weak-to-mass basis change;
- a non-identity diagonalizer pair for the up/down Yukawa matrices;
- a promoted physical CKM product;
- an arcsin approximation/error bound accepted for `theta_C`;
- an authority-bound PDG comparison receipt.

Therefore the Cabibbo target remains a target:

```text
theta_C = arcsin(alpha1 * g12)
```

not a derived angle.  The most precise prose formulation is:

```text
The carrier records a Cabibbo-angle target whose alpha factor is compatible
with the first-generation Yukawa suppression diagnostic, while the physical
coupling, diagonalization, and CKM promotion receipts remain absent.
```

This sentence keeps all three required facts visible:

```text
yukawaSuppressPatternConsistent = true
cabibboAngleDerived = false
physicalCKMPromoted = false
```

### 5.2 `g12` Is The Remaining DHR-Sector Parameter

The symbol `g12` should be presented as the remaining free parameter in the
Cabibbo target, not as a fitted constant and not as a value already derived by
the carrier.  The current target has the form:

```text
theta_C = arcsin(alpha1 * g12)
|V_us|_target(alpha,g_12)=alpha*g_12
```

Here `alpha1` is the current first-generation suppression diagnostic, while
`g12` is the still-missing first/second generation mixing coefficient that
would have to be determined by DHR sector data.  Honest Paper 6 wording is:
the carrier has isolated the slot where DHR sector structure must enter the
Cabibbo/`|V_us|` target, but it has not supplied the sector representation,
intertwiner normalization, or physical weak-to-mass basis data that would
determine `g12`.

This keeps the direction of explanation precise.  Future work may try to derive
`g12` from non-identity DHR sector actions, Higgs/Yukawa intertwiners, and a
calibrated physical basis.  The present draft may not choose `g12` by matching
PDG `|V_us|`, may not call it a first-principles prediction, and may not treat
the symbolic target as an inhabited CKM theorem.  Until the DHR-sector receipt
for `g12` is inhabited, the governing flags remain:

```text
cabibboAngleDerived = false
physicalCKMPromoted = false
```

## 6. DHR/Yukawa Compatibility Boundary

The DHR/Yukawa receipts supply useful structure for Paper 6, but only at the
carrier and symbolic level.  `YukawaFromCarrier.agda` threads
`YukawaDHRIntertwinerCompatibility` and records that the carrier/DHR formula
surface agrees with the up/down carrier matrices.  It also threads identity
sector coverage, symbolic non-identity sector actions, U(1) phase/charge
selection, and SU(2) doublet-shape checks.

The missing pieces are the physical ones.  Actual non-identity DHR sector
representations are still absent.  Physical Yukawa matrices are still absent.
The receipt keeps physical non-identity DHR action and physical Yukawa
promotion fail-closed.  Consequently, Paper 6 may use the DHR surface to
organize the carrier texture, but it may not claim that DHR reconstructs the
observed Standard Model Yukawa sector.

## 7. Penguin and P5 Prime Interface

Paper 6 can mention the rare-decay lane only as a downstream target interface.
The matter/Yukawa/CKM receipts are relevant because rare-decay observables
eventually require CKM-loop inputs and Wilson coefficient authority.  The
current repository has separate receipts for:

- CKM-loop projection targets;
- Wilson `C9/C10` authority slots;
- SM-baseline authority paths;
- checksum-bound P5 prime artifacts;
- residual comparison laws;
- carrier-derived `C9` constraint targets.

This paper should not promote any rare-decay conclusion.  The current Gate 5
state records empirical contact and selected borderline anomaly classifications
elsewhere, but full covariance binding, accepted residual promotion, Wilson
authority closure, projection-code freeze, and numerical `C9_NP` derivation
remain separate blockers.  Paper 6's role is to say what matter-side carrier
data would feed that pipeline if the CKM/Yukawa promotion blockers were later
closed.

## 8. Draft Theorem Statements

The following statements match the current receipt surface.

**Theorem 6.1, carrier Yukawa surface.**  The repository contains an inhabited
carrier-side Yukawa package in which canonical up/down `3x3` matrices,
carrier-derived identity CKM transport, CKM unitarity, DHR/Yukawa formula
access, first-generation ultrametric depth slots, and upper-triangular
up-sector off-diagonal carrier entries are threaded into one receipt surface.

**Proof status.**  Receipt-backed by `canonicalYukawaFromCarrier` and its
threaded receipts.  This theorem is carrier-side only.

**Theorem 6.2, hierarchy-pattern diagnostic.**  The carrier surface records a
Yukawa suppression pattern consistent with the qualitative observed fermion
hierarchy: diagonal carrier entries, ultrametric depth slots, alpha readbacks,
and symbolic off-diagonal suppressions all point in the direction of a
hierarchical texture.

**Proof status.**  Receipt-backed at the diagnostic level by
`CarrierYukawaRatioTargetReceipt` and `CabibboAngleCarrierReceipt`, especially
the `yukawaSuppressPatternConsistent = true` field.  This is not a theorem
deriving physical masses.

**Non-theorem 6.3, physical Yukawa promotion.**  The repository does not
currently promote the carrier texture to physical Yukawa matrices or physical
fermion masses.

**Proof status.**  Fail-closed fields include
`physicalYukawaPromotionConstructed = false`,
`physicalRatioPredictionsPromoted = false`,
`physicalFermionMassReceiptsConstructed = false`, and
`absoluteHiggsScaleW4CalibrationConstructed = false`.

**Non-theorem 6.4, Cabibbo/CKM promotion.**  The repository does not currently
derive the Cabibbo angle or promote a physical non-identity CKM matrix.

**Proof status.**  `CabibboAngleCarrierReceipt.agda` records
`cabibboAngleDerived = false`; `CKMVusCarrierPredictionTargetReceipt.agda`
records `|V_us|` as comparison-only; and the current carrier CKM matrix remains
identity.

## 9. Validation Protocol for Future Alpha Claims

A future promoted alpha claim should be required to freeze all comparison
degrees of freedom before looking at the outcome.  The minimum protocol is:

1. Choose the mass scheme: pole mass or running mass.
2. Choose the renormalization scale and threshold treatment.
3. Bind the source table and uncertainty model to authority receipts.
4. Define the carrier alpha formula for every ratio target before fitting.
5. Select whether alpha is fit from one ratio and predicted on the rest, or
   globally fit across all ratios.
6. Fix the acceptance threshold and report failed targets without retuning.

The current repository should be described as pre-protocol.  It records useful
diagnostics, including `alpha1`, `alpha2`, and `alpha1^2`, but it does not yet
contain the authority-bound experimental table or error model needed to turn
those diagnostics into accepted physical predictions.

## 10. Blocker Map

The current blockers are:

- physical Yukawa promotion: missing absolute Higgs/VEV/W4 calibration,
  physical fermion mass eigenvalue receipts, splitting-field/eigenbasis lifts,
  and physical Yukawa matrices;
- ratio validation: missing authority-bound mass table, scale convention,
  uncertainty model, accepted alpha target value, and accepted alpha bound;
- charged leptons: named `e/mu` and `mu/tau` targets, but no charged-lepton
  Yukawa carrier matrix;
- CKM transport: missing non-diagonal physical Yukawa matrices, physical
  weak/mass-basis identification, non-identity diagonalizers, exact physical
  CKM product, and CP/Jarlskog derivation;
- Cabibbo target: missing accepted common alpha, evaluated `g12`, arcsin error
  bound, and PDG authority binding;
- DHR/Yukawa compatibility: identity and symbolic checks exist, but actual
  physical non-identity DHR sector representations remain absent;
- Wilson/P5 prime: downstream empirical contact exists in separate receipts,
  but full covariance binding, accepted residual promotion, Wilson authority
  closure, projection-code freeze, and numerical `C9_NP` derivation remain
  blocked.

These blockers should be presented in the paper as typed scientific content,
not as editorial disclaimers.  Paper 6's contribution is the carrier hierarchy
and suppression-pattern surface together with a falsifiable alpha/CKM target
program.  Every stronger physical conclusion remains fail-closed.

## 11. Recommended Wording

Acceptable:

- "The carrier geometry records a Yukawa suppression pattern consistent with
  observed fermion hierarchy."
- "The alpha diagnostics are readbacks that motivate a frozen future
  comparison protocol."
- "The Cabibbo surface records a target form, not a derived angle."
- "The current CKM carrier product is the identity and is not promoted as the
  physical CKM matrix."

Not acceptable:

- "DASHI derives fermion masses."
- "The Cabibbo angle is predicted."
- "The CKM matrix is reconstructed from the carrier."
- "The off-diagonal carrier entries are physical Yukawa couplings."
- "The P5 prime residuals prove empirical adequacy or new physics."

The final manuscript should keep this distinction visible in the abstract,
the theorem statements, the alpha diagnostic section, and the blocker map.
