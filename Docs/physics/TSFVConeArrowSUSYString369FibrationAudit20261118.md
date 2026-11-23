# TSFV cone/arrow, 5+1 archaeology and SUSY/string↔369 fibre bridge — 18 November 2026

## Authorship / attribution policy

- Historical mathematical owners: Lorentz/Minkowski/Sylvester, Kaluza–Klein, Hopf, Polyakov/string sigma models, Calabi–Yau compactification, RNS and Witten's supersymmetry/index mathematics. Nothing in the present audit is their first derivation.
- Original DASHI owners: named Agda modules below, previous PR #70, #84, #1217, #1239/#1241 and #1460, plus original dashifine/dashitest experimental signature work. Do NOT credit new documents with their proofs.
- User-originated research questions: whether the original cone/arrow Agdas completely force 3+1; origin of competing signatures including 5+1; use existing U1→SU2 and 369/Calabi–Yau fibre to bridge string and TSFV unification.
- New ChatGPT-assisted work: concrete vacuity counterexample, source-direct conditional TSFV–metric/fibre consumer, and bounded documentation/acceptance gate ledger. No 5+1 original empirical discovery or physical string compactification claimed.

## 1. Existing exact TSVF/TSFV bridge: YES, with a physical assumption boundary

Existing:
1. `DASHI/Physics/Foundations/TSFVFiltrationArrowLorentzBridgeExact.agda`: early vs late filtration, same past vs differing hidden histories, time reversal of microscopic action; these are finite operational information-arrow theorems. `SelectedTSFVToLorentzPhysicalSource` requires actual `PhysicalState`, selected state, measured principal-axis probe, physical quadratic signs and a same-state `Lorentz.DirectionalProbe` plus `AxisCalibration`. `selectedTSFVPhysicalSignatureIs31` proves the selected sign counts =3,1 **from that input record**.
2. `DASHI/Physics/Foundations/Lorentz31DirectionalProbeExact.agda`: four-axis finite exhaustive proof `calibratedProbeForcesThreePlusOne`, for any independently provided probe that has EXACTLY one true arrow bit, with sign matching `classifyProbe`. The input does not literally contain a 31 name; yet it requires the one-arrow and sign-calibration results as premises, and four axes are built in. `RealizedDynamics` remains uninhabited from original physical source evidence.
3. `DASHI/Physics/Foundations/TSFVKKSameMetricTransportExact.agda`: `SameMetricTSFVKK` proves same four-coordinate selected metric signed count 3,1 by equality with the source-selected TSFV state. The record's physical inhabitant is NOT supplied by its theorem.
4. `DASHI/Physics/Foundations/TSFVKKSelectedHorizontalMetricSchurExact.agda` and `TSFVKKFiveMetricInvertibleShearExact.agda`: the exact arbitrary-base KK horizontal/shear algebra already exists and is reused.
5. New conditional consumer `TSFVConeArrowStringFibreOwnerBridgeExact.agda` imports the exact existing TSFV/metric owners and the existing Calabi–Yau369 bundle projection. It is not an observed metric or worldsheet proof; Agda kernel acceptance of new file NOT obtained here.

Correct status: **operational TSFV arrow proved in its finite selected model; one-arrow four-axis calibrated signature conditional; same selected KK metric conditional; 5D physical Einstein–YM+observer link still open.** This is a useful existing bridge, but not an independently observed 3+1 derivation.

## 2. Why the old 'full intrinsic' cone/arrow chain needs stricter audit

I inspected ACTUAL owners:
- `DASHI/Geometry/ConeTimeIsotropy.agda`: `ConeNontrivial`, `Irreflexive`, `Transitive`, `PresCone`, `PresQ`, `PresShell1`, `PresShell2` and finite-action `actCompat` are often `⊤`, not physical mathematical predicate proofs. Having fields of those types is no evidence of nontrivial cone/causality.
- `DASHI/Geometry/Signature31FromConeArrowIsotropy.agda`: the output `Signature31Theorem` is itself a **field of an input axioms record**. It is not constructed from cone/arrow data.
- `DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda`: requires `IntrinsicSignatureCoreAxioms` holding strengthened contraction plus `CausalSymmetryPackage`; its secondary `IntrinsicProfileWitness` explicitly carries `profileMatches31` equality. The derived `signature31` is through `CausalForcesLorentz31`, not independent from assumptions.
- `DASHI/Geometry/CausalForcesLorentz31.agda`: `AdmissibleSignature` has only the constructor `admissible31 : AdmissibleSignature sig31`. Rival exclusion `nonAdmissibleOther` therefore follows from the *definition of admissible*, not from an independent classification of physical metrics. `CausalSymmetryPackage` gives independent arbitrary `Set` fields and inhabitant witnesses; `causalClassificationFromEvidence` installs `forced = sig31` directly rather than computing its inertia from the supplied quadratic `q`. This is not sufficient as a claim that 3+1 is physically inevitable.
- New `DASHI/Geometry/CausalSignaturePackageVacuityControlExact.agda`: constructs the full `CausalSymmetryPackage` with every property instantiated as Unit and every witness as tt, without supplying any actual cone, signature or dynamics. This is a decisive **source-level negative control on the package's physical interpretation**; it does not refute correct finite conditional theorems elsewhere. New module not kernel checked in this session.

Upgrade acceptance: define non-vacuous physically measurable `InCone` and the selected indefinite quadratic **on the same state**, establish genuine irreflexivity/transitivity and nonzero null cone, symmetry preservation via actual transformations, compare 3+1 with 4+0, 2+2 etc on exactly the same measurements, and then derive the signature. Don't prelabel the only admissible signature.

## 3. Original 5+1 request: current actual evidence

- Direct default-branch code search of `chboishabba/dashifine`, `chboishabba/dashi_agda` for `sig51`, `signature51`, `p5_q1`, `5plus1`, and six-dimensional Lorentz descriptions did **not** return an original numerical `(5,1)` carrier/run/score report.
- `dashitest` is accessible but NOT code indexed. Its default README includes many sibling and mirrored references; this is a coverage limit, not a claim absent from user's unpublished/local work.
- Existing five-coordinate `dashifine/26_hepdata_mdl_fejer_closestpoint_signature.py` tests (4,1),(5,0),(3,1,1),(3,2),(4,0,1). The last three-number tuple includes null axes; (5,1) requires **six nonzero axes**. No inference of a six-dimensional empirical selection from five-coordinate fits is permissible.
- **Mathematical construction**: start with base (3,1) and TWO spacelike KK square fibres with positive coefficients and a nondegenerate metric; by two successive invertible block shears, the total six-metric has (5,1). Alternatively start from base (4,1) plus one spacelike circle. This is a conditional Sylvester/Schur result, not an original 5+1 measurement. Existing `TSFVKKFiveMetricInvertibleShearExact` covers the 4→5 one-fibre case. A true 5→6 lift would need its own physical fibre and global patch/field equations.
- In the physical 4→5 programme, (3,1)→(4,1) and (4,0)→(5,0) are already permitted without assuming their observational selection. Never mix the six-dimensional candidate with 5D Taub–NUT's four-spatial-plus-time carrier merely because five axes appear in one probe.

**Status: original (5,1) experimental claim NOT independently verified.** Original file/branch receipts remain an open targeted repository/history gate.

## 4. String / SUSY / 369 / fibrations: strong existing donors

- `DASHI/Geometry/CalabiYau369CompactFibreBridge.agda`: original `Dimension369` explicitly establishes **3 extended spatial + 6 internal real + 1 time =10**. `BaseCompactFibreBundle` defines `includeFibre`, `projectBase`, and proof `projectionReturnsBase`. `EffectiveFibreObservable` supplies a typed internal integration operation and equivalence with a supplied effective field. Crucially `localProductStructure : Set` is merely a TARGET, not a smooth six-dimensional compactification proof. Its own `canonicalCalabiYau369Boundary` records string compactification as FALSE/not paid.
- `DASHI/Unified/HyperfabricGRStringExistingDonorWeldExact.agda`: finite nonflat Einstein source, original Nambu membrane tension, and CY dimension reading reused; distinguishes a 2+1 membrane from a 1+1 string worldsheet.
- `DASHI/Unified/HyperfabricMonsterBosonicWorldsheetExistingOwnerCutExact.agda`: original Monster VOA `c=24`, Lorentzian `II_{1,1}` `c=2`, bosonic ghosts `c=-26` bookkeeping; also independent RNS ten-boson+ten Majorana fermion budget `10+5+11=26`. These are arithmetic constraints, NOT worldsheet CFT/BRST nilpotence, GSO, string background or observed theory.
- `DASHI/Physics/QFT/WittenIndexSUSYBoundarySurface.agda`: has a full list of SUSY targets but **explicit postulates** for background/super-Hilbert/charges and placeholders. NEVER import it to a `--safe` proof, claim supersymmetry is built, or use its `WittenIndex` to certify observed SUSY.
- `DASHI/Algebra/Quantum/NVSpinOneFiniteSUSYFactorisationExact.agda`: bounded finite SUSY QM factorization, not a ten-dimensional supersymmetric quantum field theory.
- `docs/hyperfabric-quantum-string-classical-spacetime-crosspollination-20261024.md`: ALREADY distinguishes ternary 27 path graph (`P3^3`, 54 edges) vs periodic (`C3^3`, 81 edges), whose operators/eigenvalues differ. A matching 369 label or C3 does NOT supply worldsheet map or holonomy.
- Prior unified source owner: #1217 TOE/369 universal realization; do not fork a duplicate TOE theory.

## 5. String→369 fibration commuting bridge (new bounded receipt)

One **constructive** and well-typed bridge can use the ACTUAL CY original bundle, not a new pretend fibre. Given `f : BaseCompactFibreBundle B I T`, a proposed worldsheet `Σ` with `X_B:Σ→B` and `X_I:Σ→I`, define `X(s)=includeFibre f (X_B(s)) (X_I(s))`. By the source's existing projection theorem, `projectBase f (X(s)) = X_B(s)` pointwise. Implemented in `TSFVConeArrowStringFibreOwnerBridgeExact.agda`. This is a legitimate string-*target-map* fibration/projection equation; it does not establish the physical Polyakov action or conformal invariance.

The next same-source proof must bind this `B` to the original selected TSFV+KK 4D metric and 369 YM connection, bind `I` to an actual smooth compact internal manifold, define `X` and the induced worldsheet metric on the SAME total space, and transport curvature/connection/Wilson holonomy through local trivialisations with all boundary/gauge transformations accounted for.

After that: (a) CY canonical bundle and Ricci-flat metric, moduli/radion stabilization, spin structures; (b) 10D critical RNS superstring conformal/BRST/GSO; (c) 4D low-energy effective action with matched gauge charges/anomalies/fermions; (d) independent observables and tests. `U1SU2GroupTorusExact` remains the actual reusable subgroup but alone cannot provide physical E6/SU3/U1 anomaly-safe embeddings.

## 6. Roadmap and acceptance ledger

- [x] Recover correct preexisting finite TSFV arrow and conditional four-axis probe theorem.
- [x] Recover existing same-source KK metric and arbitrary-g4 shear, no new duplicate.
- [x] Check intrinsic cone owner for reliance on conditional classifiers and Unit placeholders; source-level negative control committed.
- [x] Find actual CY 369 bundle and string central-charge donors; record distinct 26D bosonic and 10D RNS routes.
- [x] Add first commuting projection theorem from original CY fibre to proposed worldsheet base map.
- [ ] Kernel-check both new modules at exact PR head with pinned Agda; no receipt in this session.
- [ ] Produce signature-neutral selected measured cone and metric from actual TSFV observer states; prove a non-vacuous competitor elimination theorem on same carrier. This is the **real** missing P01/P02 link.
- [ ] Find original measured 6-axis (5,1) run or mark absent after full history and unindexed dashitest audit.
- [ ] Construct source-owned actual fibre metric and string worldsheet target, transition atlas, CY geometry and anomaly-safe SUSY spectrum.
- [ ] Transport to same source YM Wilson bond, measured 369 operators and KK Einstein action; original RG continuum, OS mass gap and fermionic soliton remain open.

### Important negative controls to preserve

1. Package with 8 Unit witnesses must NOT pass as observational proof of Lorentz 3+1.
2. CY dimension 3+6+1=10 must NOT count as a constructed Ricci-flat compactification.
3. Scalar central-charge equality must NOT count as a BRST/no-ghost proof.
4. 5-axis mask must NOT count as a measured 6-axis (5,1).
5. A worldsheet base-projection identity must NOT count as a string equation-of-motion solution.
6. A finite C3 Fourier lattice must NOT count as the original path 369 operator without an intertwiner.
7. U1→SU2 as groups must NOT be equated with full noncommuting YM curvature.
