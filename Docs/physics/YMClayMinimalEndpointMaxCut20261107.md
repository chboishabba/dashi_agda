## 7 November — final safety cuts: genuine selected epsilon--N convergence; geometric physical D1

**E1 genuine topology:** `YMClayE1OriginalSUNFiniteCylinderLawsExact.PhysicalRealConverges` now means an actual epsilon--N estimate, **not** equality to an arbitrary selected `limit : (Nat -> Real) -> Real`:
```
forall epsilon>0, exists N, forall n>=N:
  abs(nativeExpectation(n,F) - continuumExpectation(F)) <= epsilon.
```
`PhysicalRealSequentialConvergenceLaws` makes standard real-analysis uniqueness, arithmetic and positivity closure explicit. `ActualSelectedOriginalSUNConvergence` now demands the above genuine convergence **only for the proof-bearing selected gauge-invariant local algebra**, NOT all `(forall n, Links_n -> Real)` sections. `nativeSUNAsDependentE1Source` uses that topology, native original Haar/Wilson finite integration, and the selected physical cylinder realization. There is no tautological `lim(s)=lim(s)` path to E1.

**Concrete selected algebra:** `OriginWilsonPolynomial` and `originWilsonPolynomialSelectedAlgebra` are source-written with actual original local plaquette holonomy/trace, constants and polynomial operations; `originPolynomialGaugeInvariant` inducts over the true native finite-gauge action. These are microscopic original finite-local expressions: physical local renormalization, UV/IR convergence, full Euclidean/OS axioms and nontriviality remain open.

**D1 quantitative shape:** `YMClayD1OriginalRealCMP116VariableCutoffExact` now additionally requires physical cube length `physicalCubeLength > 0`, a shared real `0 <= commonContraction < 1`, finite amplitude and a physical block distance; it proves `originalWilsonRealCovarianceGeometricBound`:
```
forall n, left, right:
  abs(Cov_original_Wilson_n(left_n,right_n))
    <= amplitude * (commonContraction ^ physicalBlockDistance(left,right)).
```
This is the correct positive-rate *physical-block* form, without a rational T5 equality. **The actual source calibration is not established:** `pairAdmissible`, `differentiatedSourceIsOriginalRealCovariance`, `uniformSourceEnvelope`, and `upperHasUniformGeometricRate` remain physical source inputs. A cutoff-independent bound with no distance factor is not sufficient for Clay D1.

**D2:** R287 and `BalabanClayT5OSReconstructionCyclicityExact` already compile abstract cyclicity and subgap detection; the specific selected original E1 OS Hilbert representation and full positive spectral-measure inclusion still need original-source proof. No dependence on #1460 observer/HIL.

**Trust:** The Agda source is committed, and the regression imports were added; exact-head Agda `parallel_checker` and transitive proof/real-authority trust have **not** been run. The source modules are conditional and do not prove Clay. An actual 4D interacting YM theory, physical D1 estimate, full D2 spectrum, N1 and G1 remain genuine outstanding results.

---

## 7 November — selected physical E1 algebra repair and original plaquette polynomial witness

The initially introduced `ActualSelectedOriginalSUNConvergence` over `Native.Cylinder = (forall n, Links_n -> Real)` was **too broad**: arbitrary cutoff-dependent sections (including oscillating constants) cannot all converge in an ordinary physical continuum topology. The original endpoint candidate was unusable as a genuine E1 existence proof. It has now been **replaced** by `SelectedNativeCylinderAlgebra` with an explicit `Observable : Set` and source-realization `selectedSection : Observable -> forall n, Links_n -> Real`, pointwise selected zero/one/add/scale meanings, positivity interpretation and actual original Wilson gauge-invariance proof at every n. `ActualSelectedOriginalSUNConvergence` now quantifies **only over that selected observable class**. The new `nativeSUNAsDependentE1Source` derives the finite normalized state laws via `nativeExpectationExtensional` from the real original product-Haar measure and the selected pointwise meaning proofs; it does **not** assume convergence of all cutoff sections.

A concrete proof-bearing nonempty class is now implemented as `OriginWilsonPolynomial` (constants, one original local Wilson plaquette trace, finite sums/products, scalar multiplication), interpreted by `evalOriginWilsonPolynomial` on the **actual** changing-cutoff Wilson links. `originPolynomialGaugeInvariant` proves exact original gauge invariance by structural induction using existing original finite-source owners, and `originWilsonPolynomialSelectedAlgebra` instantiates the selection record. **Physical caveat:** the fixed microscopic plaquette shrinks with cutoff; its continuum limit may collapse. Thus this is a concrete E1 **finite local algebra**, not a proof of local renormalized continuum YM observables, and cannot be used as the N1 nontriviality witness by declaration.

The genuine next E1 theorem is **selected local continuum source convergence on a physically supported/renormalized cylinder algebra**, with projective consistency, correct physical (a_n,L_n,β_n), and full Euclidean/OS QFT identification. No generic `limit` oracle or arbitrary n-section can stand in for it. Exact Agda 2.9 kernel/parallel_checker acceptance remains unverified.

---

## 7 November — E1/D1 source-level implementation: no borrowed YM endpoint

### E1 safe compiler and native source
`YMClayE1VariableCutoffCylinderLimitExact.agda` was **repaired** to parameterize the n-dependent `Measure : Nat -> Set` and normalization operation instead of importing the postulated-real physical module into a purported `--safe` generic theorem. The existing proof still derives normalization, positivity, additivity and homogeneity from finite laws and explicitly supplied same-source convergence; no arbitrary source-independent continuum expectation is created.

New `YMClayE1OriginalSUNFiniteCylinderLawsExact.agda` instantiates those finite laws with the original **changing** `YMClayE1OriginalSUNDependentCylinderExact.actualOriginalWilsonMeasureAt n`. The real denominator is definitionally the SAME `Quotient.divide` used by the native Wilson measure. Existing `YangMillsFinitePhysicalMeasureLimitExact` finite algebra is reused at each cutoff (a local constant family at the selected n, NOT a fictitious common configuration space across all n). `fixedCutoffFiniteLaws`, `nativeExpectationZero`, `nativeExpectationOne`, `nativeExpectationAdd`, `nativeExpectationScale`, `nativeExpectationPositive` are new source-written proofs.

The new `nativeSUNAsDependentE1Source` constructs a full `ActualVariableCutoffCylinderFamily` with those five finite laws **derived**, requiring only (a) native physical Haar integration/partition-nonzero laws, and (b) `ActualSelectedOriginalSUNConvergence.originalWilsonCylinderConverges` on its chosen continuum cylinder class. The latter remains a genuine uninhabited physical convergence input, not computed by a generic `limit (Nat -> Real)` selector. Unrestricted arbitrary n-dependent cylinder sections do not generally converge; select a projectively compatible local gauge-invariant class for a physical E1 claim.

### D1 direct original REAL CMP116 application
New `YMClayD1OriginalRealCMP116VariableCutoffExact.agda` dispenses with the rational T5 representation altogether for the original SU(N) changing cutoff carriers. Its `OriginalRealCMP116PhysicalSelection` has the exact selected local gauge-invariant Wilson test realizations on `YMClayOriginalVariableWilsonCovarianceSourceExact`, CMP116 source directions at every n, physical source-pair admissibility, a same-source **real** derivative/covariance identity, one original uniform physical envelope, and real source-order interpretation. `originalWilsonRealCovarianceUniformBound` composes the actual CMP116 differentiated localization theorem to bound the native original finite covariance for EVERY n by the same selected `physicalUpper left right`. No illicit \u211d=\u211a transport or frozen n=3 test source.

**Remaining D1 analytic lemma, still genuinely unsolved:** derive the record's `pairAdmissible`, `differentiatedSourceIsOriginalRealCovariance` and `uniformSourceEnvelope` from the ORIGINAL CMP119/122/R445 physical RG source with a strictly positive spatial rate at a fixed physical length scale. An arbitrary n-independent upper bound does **not** itself prove exponential clustering. `PublishedCMP116DifferentiatedLocalization` is a source theorem ABI, not an automatically inhabited physical-source lemma; its `SourceEnvelopeHasPositiveExponentialTreeDecay : Set` needs actual meaningful quantitative interpretation.

### D2/N1/G1
Existing `BalabanClayT5OSReconstructionCyclicityExact` and R287 already compile abstract positive-time cyclicity into mode detection. Do not rebuild those abstractions. Prove the physical selected Wilson cylinder cyclic density and genuine spectral lower bound on the same E1 OS Hilbert space and full-sector inclusion; `YangMillsClayCMP119CoreSemigroupH3Exact` has the exact outstanding semigroup/cyclicity and physical spectral completeness coordinates. N1 same-source Ward/Maxwell or fourth-cumulant noncollapse remains original physical, G1 all compact simple forms remains original physical.

**Receipt status:** all files exist at PR #1444 and imported into `YMClayOriginalWilsonPhysicalRegression`, but no Agda 2.9 exact-head `parallel_checker` execution or transitive real-axiom trust audit is available here. New source proofs are unverified, and E1/D1/D2/N1/G1 are **not completed** as physical Clay results. Never convert these conditional implications into a claim of a 4D Yang–Mills mass-gap solution.

---

## 7 November — E1 original finite Wilson integration and safe/physical boundary

**Source-written proof:** `YMClayE1OriginalSUNFiniteCylinderLawsExact.agda` is pinned to `YMClayE1OriginalSUNDependentCylinderExact.actualOriginalWilsonMeasureAt` at every varying cutoff `n`. It reuses `YangMillsFinitePhysicalMeasureLimitExact` *at each actual n-specific link carrier* by constructing `fixedCutoffFiniteLaws`; there is no attempt to equate different finite link types. It derives `nativeExpectationZero`, `nativeExpectationOne`, `nativeExpectationAdd`, `nativeExpectationScale`, and `nativeExpectationPositive` from **only** native `PhysicalFiniteMeasureIntegrationLaws`, original partition nonzero and one common genuine quotient/division operation. This is exactly the finite E1 requirement and removes five independently supplied physical finite-state laws, not an arbitrary new continuum expectation oracle.

**Safe boundary repair:** `YMClayE1VariableCutoffCylinderLimitExact.agda` now parameterizes `Measure : Nat -> Set` and `originalNormalizedExpectation` and imports NO physical measure or postulated real-analysis module. Its selected-limit algebra/transport is genuinely abstract and `--safe`-eligible. The native Wilson finite source module remains non-safe due to `RealAnalysisAxioms`. Exact Agda kernel acceptance is not claimed without `parallel_checker`.

**Important analytic restraint:** the legacy `BalabanRealSequenceLimitByVanishingErrorExact.RealSequenceLimitByVanishingError.limit : (Nat -> Real) -> Real` is an externally supplied `limit` for every sequence. Defining `Converges s target` as `limit s ≡ target` can be an adequate abstract convergence authority, but MUST NOT be interpreted as proving ordinary topological convergence of all original Wilson expectation sequences. The genuine E1 obligation is an actual sequence-specific physical convergence/tightness theorem in a well-defined topology on physically admissible local cylinders; no finite linearity identity proves that.

**D1/D2/N1/G1 remain genuinely open:** the original real-valued Wilson physical CMP116 bound, a full-sector spectral theorem for the reconstructed OS Hamiltonian, actual nontrivial continuum local correlation, and all compact-simple-G extension. The real-valued `YangMillsClayCMP119RealSelectedGapExact` route renders the proposed general ℚ/ℝ scalar-isomorphism obligation optional.

---

## 7 November: original LOCAL two-plaquette Wilson physical D1 test class and marked-source identity

`YMClayOriginalVariableWilsonCovarianceSourceExact.agda` additionally constructs `originalLocalPlaquetteTraceAt n p` for **every** original positive plaquette `p : Plaquette.PeriodicPlaquette n` at every changing cutoff `n`. This uses the actual original Wilson plaquette holonomy and selected SU(N) real trace—not a synthetic test or one global all-lattice action. `originalLocalPlaquetteTraceAtGaugeInvariant` consumes `Variable.periodicSUNPositivePlaquetteGaugeTrace`; `originalLocalPairProductGaugeInvariant` proves any two selected plaquette insertions produce a gauge-invariant original test.

Most importantly, `originalTwoLocalWilsonMixedLogIsOriginalD1Covariance` directly instantiates **the original real-valued** `YMClayOriginalWilsonFiniteTwoSourceJetExact.originalWilsonMixedJetIsSameFiniteCovariance` on these two local plaquette insertions. For all n and all p,q it identifies the actual original same-source real mixed-log two-J coefficient with the **same** `originalWilsonConnectedCovariance n` on the changing four-torus; no auxiliary rational `R320` source introduced. Together with `originalE1LocalPlaquetteConnectedCovarianceIsSameD1`, this welds E1 finite observable, physical two-source marked J, D1 covariance on precisely one selected original finite Wilson measure.

**Decisive remaining analytic D1:** derive a quantitative original-source CMP116/RG clustering bound on exactly these physically located plaquette pairs and the chosen renormalized fixed-physical-size Wilson observables; prove a positive physically calibrated rate uniform in a→0 and volume→∞. A single microscopic plaquette has support O(a) and its naive trace may collapse to the identity, so this is NOT N1, no continuum source and no mass-gap claim. Full E1 nontrivial local continuum construction, D2 full spectrum, N1 survival and G1 remain OPEN. No Agda exact-head parallel_checker receipt.

## 7 November original Wilson E1 physical local-test producer, no new carrier

`YMClayOriginalVariableWilsonCovarianceSourceExact` now contains a literal n-dependent **gauge-invariant** real Wilson cylinder subalgebra: `OriginalGaugeInvariantSection` states invariance under the original variable periodic-site gauge action at **each n**, and the source proves `originalGaugeInvariantZeroCylinder`, `originalGaugeInvariantUnitCylinder`, `originalGaugeInvariantSectionAdd`, `originalGaugeInvariantSectionScale`, and `originalGaugeInvariantSectionProduct` from the actual Wilson matrix/gauge operations rather than a second arbitrary cylinder carrier. In particular, `originalSixPlaquetteDeficitSection` is the native six-positive-plaquette Wilson action density of the changing four-torus, `originalSixPlaquetteDeficitIsGaugeInvariantSection` consumes the real selected `Variable.periodicSUNSixDeficitGaugeInvariant` theorem, and its square remains in the same algebra. `originalE1SixDeficitCovarianceIsSameD1Source` is an exact equality of E1's second moment and D1's original connected covariance of that physical gauge-invariant cylinder at **every cutoff**.

**What this actually closes:** the E1 physical cutoff-dependent **gauge-invariant polynomial cylinder closure and native Wilson-deficit generator** and its same-measure E1/D1 covariance source equality. These are finite proofs, not yet the projectively compatible **bounded-support localized continuum subalgebra**. The six-plaquette action sums the entire lattice; it does NOT itself furnish local-test support or a nonzero renormalized continuum observable. Required E1 physical locality, ultraviolet scaling/convergence, Osterwalder-Schrader limit and axioms, D1 uniform original covariance bound, D2 full cyclic spectral detectability, N1 original continuum noncollapse and G1 all groups remain OPEN. Neither scalar ℝ nor matrix Haar is genuinely kernel-accepted here; source-written and regression-imported only.

**Additional exact E1↔D1 source weld:** `actualE1D1SameWilsonConnectedCovariance` is proved in `YMClayOriginalVariableWilsonCovarianceSourceExact` for **all** cutoff-dependent original cylinder sections and **all** n, by literal definitional identity with `YMClayE1OriginalSUNDependentCylinderExact.actualOriginalWilsonCylinderExpectation`. Thus E1's finite cylinder sequence and D1's finite connected covariance are now the **same selected original real physical measure**, not merely two records with matching symbolic names. This is a finite identity, NOT selected source convergence or uniform covariance decay; the same true original ℝ ↔ historical rational T5 source scalar representation and actual Wilson CMP116 estimate remain outstanding.

## 7 November continuation — literal all-cutoff REAL Wilson connected covariance

New source owner `DASHI/Physics/YangMills/YMClayOriginalVariableWilsonCovarianceSourceExact.agda` constructs **the actual changing-cutoff SU(N) Wilson covariance directly in the same original family** `YMClaySUNVariablePhysicalCutoffFamilyExact.physicalFiniteCutoffMeasure` for every `n`. It uses the original `Codec.decodeOriginalBonds (suc n)` and **proved product-Haar integral congruence** `YMClaySUNMatrixProductHaarC3Exact.productIntegralCongruent` to establish `originalWilsonExpectationExtensional`. Hence `originalWilsonConnectedCovarianceSymmetric`, `originalGaugeInvariantProduct`, and `originalWilsonGaugeInvariantConnectedCovariance` are proved algebraically for arbitrary finite test cylinders on the actual n-dependent ℝ-valued Gibbs measures, not via an independent n=3 pushforward or unrelated rational T5 record. Imported in `YMClayOriginalWilsonPhysicalRegression`.

**Sharp remaining D1:** prove one quantitatively cutoff/volume-uniform rooted-shell/exponential bound on `originalWilsonConnectedCovariance n F G` for the physical gauge-invariant localized F,G and chosen distance and β(n) scaling, then relate that very original real expectation to the selected rational (ℚ) T5 `R320` consumer without equating distinct scalars by fiat. The existing `YMClayD1OriginalCovarianceToR320Exact` identifies the selected ℚ mixed-J Hessian with its own ℚ-valued finite covariance; **it does not itself identify that sequence with ℝ-valued n-dependent `YMClaySUNVariablePhysicalCutoffFamilyExact`**. The new module supplies the *concrete real physical side* of that remaining weld, not a rate or limit.

**E1/D2 owner alignment:** independent #1444 E1 constructors for true varying configuration carriers and selected cylinder limit-state laws now exist, and the finite rational invisible-sector example correctly falsifies an unqualified selected-covariance → whole OS spectrum inference. Neither the original admissible local cylinder continuum convergence, whole-H spectral detectability, N1 or all compact-simple G follows from this finite theorem.

**Trust status:** source-written on #1444 and regression-imported, no exact-head Agda 2.9 `parallel_checker` receipt; the ℝ analysis facade has external/postulated authority. No physical endpoint claim.

## 7 November continuation 2 — actual changing-cutoff E1 and D2 completeness guard

**New E1 source:** `YMClayE1VariableCutoffCylinderLimitExact.agda` defines a *dependent* finite configuration carrier `Configuration : Nat -> Set` and a cutoff-indexed cylinder realization. `ActualVariableCutoffCylinderFamily` pins every finite expectation definitionally via `Physical.normalizedExpectation (finitePhysicalMeasure n) (realization n observable)`; it separately requires the selected original physical convergence proof. Theorems `variableCutoffContinuumZero`, `variableCutoffContinuumNormalized`, `variableCutoffContinuumAdd`, `variableCutoffContinuumScale`, and `variableCutoffContinuumPositive` prove actual limit-state laws from finite integration identities and the SAME source convergence, without inventing a general limit for all arbitrary real sequences.

**Native source instantiation:** `YMClayE1OriginalSUNDependentCylinderExact.agda` defines the actual `ActualLinks n = SUNPeriodicLinks theory n`, every-changing-cutoff original `Original.originalWilsonMeasure ... n`, and `nativeSUNSelectedFiniteExpectationIsLiteralWilson` with exact definitional equality. Its full `Cylinder = forall n, Links_n -> Real` is a **finite-source section algebra only**: arbitrary cutoff-dependent sections (e.g. alternating constants) need not converge. For E1 choose an admissible gauge-invariant local cylinder subclass, prove its physical compatibility, uniform convergence/tightness and OS/Euclidean properties. This is NOT a construction of a 4D continuum theory.

**D2 negative control:** `scripts/check_ym_selected_covariance_spectrum_bidi_20261107.py` independently executed with exact rational Fractions. Positive transfer operators with eigenvalues `(1,1/2,n/(n+1))` have a selected covariance decaying as `(1/2)^t` uniformly in n, while the *full* transfer gap is `1/(n+1)->0`. Thus original selected D1 decay cannot by itself prove a full OS spectral gap: must show the selected gauge-invariant test algebra is cyclic/spectrally complete for the actual OS Hamiltonian, or directly control the full relevant spectral sector. No toy model is promoted to YM.

**Kernel:** both new E1 Agda files and the original D1 source are imported by the dedicated physical regression; Github readback is available; no exact-head `parallel_checker` run. Mathematical completeness of E1/D1/D2/N1/G1 remains open.

---

## 7 November continuation — actual original covariance-to-R333 finite-source equivalence

**New original D1 Agda owner:** `YMClayD1OriginalCovarianceToR320Exact.agda`, imported in the dedicated physical regression root. It reuses `NormalizedTwoSourceConnectedCumulantExact.mixedSecondLogDerivativeIsConnectedCovariance` and `BalabanT5StateFamilySourceAlgebraRound295Exact.sourceConnectedCovarianceIsExactFiniteT5` to prove an **equality** between the selected normalized mixed-log Hessian and the true connected covariance of the very same finite `measureSequence` at every cutoff. Thus it proves the forward and reverse implication between the existing R320 `DirectSelectedT5MarkedDecayPayment.mixedDerivativeMagnitudeBelowSelectedShell` and ONE literal finite connected-covariance rooted-shell inequality. The new `originalCovarianceBoundBuildsR333FiniteSource` then consumes the physical covariance estimate through the existing H1/R313/R296 compiler to construct the finite T5 source expected by R333. No new independent two-J polynomial, Hessian axiom, rooted-shell distance or physical measure is introduced.

**Exact genuine physical D1 lemma not yet provided:**
```
for every selected cutoff n and local gauge-invariant original Wilson tests F,G:
  |Cov_{mu_n}(F,G)|
    <= rootedShell(scale(n), volume(n), root(n,F,G), distance(F,G)).
```
It must be derived from actual original CMP119/122/R445 physical conditional/polymer bounds with the chosen scaling, not supplied as a handpicked source field. This inequality is all R320 asks on the selected T5 family; its analytic proof remains open.

**E1 reuse correction:** `YangMillsLiteralRealCylinderLimitPhysicalMeasureExact`, `YangMillsFinitePhysicalMeasureContinuumOS2Exact` and `YangMillsFinitePhysicalMeasureSymmetryLimitExact` already compile a concrete normalized positive continuum expectation, reflection-positive real Gram and finite-symmetry preservation from **selected finite expectation convergence**. A temporary duplicate `YMClayE1ConcreteCylinderStateOS2Exact` was removed from the branch, and its regression import removed. This avoids parallel wrapper debt. The hard E1 work is an actual nontrivial gauge-invariant `R^4` cylinder limit from the variable-size Wilson family, with all accepted axioms, not re-proving a generic functional-limit theorem.

**Verification:** source-written and GitHub readback pending exact Agda `parallel_checker` acceptance. These compiler equalities are partial results; no infinite-volume/continuum existence theorem, published uniform analytic D1 estimate, spectrum or nontriviality was constructed.

---

# Clay Yang–Mills: minimal endpoint max-cut (7 November 2026)

**Canonical target**: for every externally specified compact simple Lie group G, construct a nontrivial four-dimensional quantum Yang–Mills theory on R^4 satisfying an accepted axiomatic QFT scheme, with a strictly positive mass gap above its vacuum. The YM proof is independent of TSVF, measured observer dynamics, Lorentz (3,1) emergence and 5D KK. No fixed 1024-bond sample, R443/R445 phase, CMP116/CMP119/122 scheme or OS route is mandated by Clay. They may be employed ONLY as needed by the selected proof.

## Four terminal claims; three main mathematical producer cuts

### E — Existence and axioms (C1)
For a **fixed external compact simple G**, construct one actual cutoff-to-continuum family of four-dimensional gauge-invariant Schwinger functions and prove the regularity, positivity, covariance, symmetry, growth/locality, Euclidean/OS or accepted Wightman strength, and local nontrivial quantum YM identification required at the endpoint. Source-generated finite measures, tightness/weak limits and local observable representation must all refer to the same physical G, action, coupling trajectory, cutoff and volume. In the selected Euclidean route, the finite Wilson RP theorem is reusable; only its application to the actual original Wilson measure and preservation at the limit matter.

**Source owner:** `BalabanOSMassGapClosure.PreGapContinuumSchwingerSystem`, `PreGapOSReconstructionAuthority` and `YangMillsClayLiteralTopDownConstructionExact`. The former OS reconstruction interfaces are records with `Set` predicates, **not constructed original Schwinger functions or a checked implementation of the full physical QFT axioms**. `YMClaySUNVariablePhysicalCutoffFamilyExact` constructs changing finite lattices, explicitly not a continuum limit.

**Required physical lemma E1:** construct the actual same-source continuum Schwinger family and proof-bearing endpoint axioms, including full `R^4` Euclidean symmetry, local gauge-invariant observables, correct YM/UV interpretation and genuinely reconstructed OS/Wightman QFT. This is an existential source construction, not another implication from a parametrically supplied `ContinuumSchwingerSystem` record.

### D — Direct spectral gap (C3)
**Preferred shortest existing route:** `YMClayRouteSH1DirectSelectedMarkedDecayExact` and `YMClayDirectSourceOSMassGapFrontierExact`: original selected R320 direct marked decay `RouteSH1DirectSelectedPayment` -> R295/R313/R296 -> R333 `CanonicalBOSIndexedApplication` and `CanonicalBOSIndexedCompletion` -> `BalabanOSMassGapClosure.PhysicalMassGapCertificate`. The separately expressed direct upper route `YMClayR387PhysicalSpectrumExact` consumes `PhysicalSpectrumInterpretation`. None builds the required physical analytic input automatically.

**Required analytic lemma D1:** on the *same* physical cutoff/continuum family E1, derive the direct selected two-source rooted-shell/connected Wilson correlation bound uniform in the physical scaling limit (the actual R320 source payment). Do not rebuild the finite mixed-derivative polynomial already supplied by the original source owners.

**Required spectral lemma D2:** prove the actual reconstructed self-adjoint `H_G` and its vacuum, same-family transfer/time/functional-calculus correspondence, and the genuine spectrum statement
`sigma(H_G) subset {0} union [Delta_G,infinity)`, `Delta_G > 0`, excluding positive subgap spectrum in physical units. The R333 transfer/spectral application and limit fields must be derived from E1 and D1, not inhabited by arbitrary `Set` parameters. A fixed lattice q=1/2 estimate is not automatically a finite physical gap under a->0. Dense L2/Mosco/finite-form route is optional, not an independent prerequisite when the direct OS route is proved.

### N — Nontriviality (C2)
Existing sufficient (possibly **stronger than necessary**) route: `YMClayRGLossBudgetToNonGaussianExact.RGReferenceChargeSurvival` yields `referenceRGUniformNoncollapse` from an actual reference charge, summable physical one-step losses and total budget; `ActualRGContinuumChargeLimit` plus `BalabanClayT5CumulantLowerBoundNontrivialityExact` gives an original nonzero fourth connected cumulant and excludes Gaussianity. This is an optional **witness strategy**, not a requirement of Clay that the particular fourth cumulant be nonzero.

**Required lemma N1:** construct one genuinely nontrivial local gauge-invariant continuum YM observable/correlation on the SAME E1 source. Use original RG fourth cumulant charge-survival if it is the shortest certifiable route; otherwise a weaker physical noncollapse witness suffices. A mere `InteractingContinuumWitness` with uninterpreted `Witness : Set` does not prove physical nontriviality.

### G — All compact simple groups (C4)
Fix G first and allow G-dependent constants. Then quantify the **same per-group completed E1,D1,D2,N1 construction** over every externally specified compact simple Lie group. `YangMillsClayFixedGroupMaxCutRound477Exact` permits group-dependent constants; `YMClayCompactSimpleScopeBidiNoVacuitySafeExact` prevents vacuous internal group-index scopes. Existing SUN matrix constructors alone do not establish every compact simple G.

**Required lemma G1:** provide an externally sound compact-simple group index/interpretation, and for each G the actual fixed-group physical continuum + gap + nontriviality construction. Do not infer arbitrary G from one SU(2)/SU(N) example.

## Minimal decisive proof cut

`E1` (one original continuum axiomatic YM theory at fixed G) + `D1` (physical selected uniform decay) + `D2` (same OS Hamiltonian spectral identification) + `N1` (genuine nontriviality), then `G1` quantification. D1 is only required **for this chosen direct decay proof route**, not by Clay. If a different direct Hamiltonian gap proof is shorter, substitute it without reopening R443/R445/CMP116.

## Supporting proof modules, not terminal requirements

`YMClayNative1024*`, `YMClayOriginalWilsonF19*`, R443, R445, CMP119/122, CMP116, R342, R344, R467, R482, R333 remain donors. Review or repair those only when E1/D1/D2/N1/G1 consumes them. Published reflection positivity and analytic estimates must be applied accurately to the selected source; do not demand per-polymer PSD, an extra observer model, 5D gravity or reconstruction of the source literature in Agda.

## Acceptance/verification

A completed proof has an exact-head `parallel_checker` Agda receipt, transitive trust review identifying any postulates/external mathematical authorities, and a closed theorem whose constructor does not accept the missing endpoint properties as arbitrary user-supplied `Set` evidence. A generic record or conditional compiler is useful mathematics but cannot be presented as E1/D2/N1. At the time of writing no exact-head kernel check or physical endpoint witness has been obtained in this session.

**Next implementation target:** E1 and D1 in parallel, then D2/N1; G1 is a group-index/scoping requirement throughout, not a demand for a uniform gap constant over all G.
