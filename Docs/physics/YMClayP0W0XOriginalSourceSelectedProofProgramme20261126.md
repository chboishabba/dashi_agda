# YM P0W/P0X — original source-selected proof programme, 26 November 2026

## Scope decision and falsifiable acceptance

**Proceed** with a new source-specific P0W/P0X proof programme, using original Bałaban CMP119 and CMP122-II primary extracts plus the recovered *CMP122-I primary-PDF audit* on master. Keep all actual Wilson ↔ Eq. (1.71), source-dependent small-/large-field, physical-rate, E1/OS, noncollapse and same-H gap leaves explicitly **CONDITIONAL**. This is approval to seek new source mathematics, **not** authorization to fill the missing physical fields with axioms or to relabel a canonical F19 candidate as Bałaban's selected historical operation.

**Source state at decision:** `master=f55ec6217181eaeb0af5cf46bae18071dea5e7d8` was inspected. The original CMP122-I paper was subsequently found in a research worktree at `/home/c/Downloads/balaban1989.pdf`; the repository audit `Docs/physics/YMClayW0CMP119SourceDomainTOperationPriorArt20261123.md` already reports direct inspection of its pp. 175–202 and Eqs. (0.1)–(0.6), (1.1), (1.63), (1.70), (1.73), (1.75), (1.89)–(1.96). **That local file is not part of this repository or a portable PDF deliverable.** The CMP119 and CMP122-II OCR extracts are tracked in `Docs/support/reference/balaban-source-extracts/`; an actual CMP122-I extracted text file is **not** present at the guessed path `cmp122-rg-lattice-gauge-i.txt`. The selected Eq. (1.71) displayed formula in CMP122-II's tracked OCR is incomplete, so source symbols must be visually checked against the actual PDF before asserting their literal equality. Never invent or repair OCR signs by plausibility.

## Exact parent source references (primary authors retain attribution)

- Tadeusz Bałaban, *Convergent Renormalization Expansions for Lattice Gauge Theories*, CMP **119** (1988), 243–285, DOI `10.1007/BF01217741`. Source Sect. 2 Eqs. (2.1)–(2.3), (2.10)–(2.23) provides `Ω/Λ/S` domains, ordered `T`, component and sequence indices, original Wilson/E/R/B/V source actions and normalization. In particular `S_j` is **inside** `T`, not an extra outer (2.18) sum.
- Tadeusz Bałaban, *Large Field Renormalization. I. The Basic Step of the R Operation*, CMP **122** (1989), 175–202, DOI `10.1007/BF01257412`. Original-pdf audit in `YMClayW0CMP119SourceDomainTOperationPriorArt20261123.md`; local renormalized `R` / good-bad splitting, localized component selection and modified-density bounds; not a full Wilson F19 identification.
- Tadeusz Bałaban, *Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation*, CMP **122** (1989), 355–392, DOI `10.1007/BF01238433`. Equation (1.71) is a **source-localized constrained integral**, including the domain, axial tree `rT`, background/action and component/symmetry sum. Do **not** replace it with `T_k(X)1=exp(-A_k(V))` by fiat.
- Original Wilson lattice action, compact Haar / reflection positivity and DASHI prior finite and RG constructions remain their own primary owners. The new programme is source selection, not a claim of independent invention of these theorems.

## P0W — exact source-selection lemma/cutset (geometry forward, equality backward)

Names here are **PROPOSED new proof endpoints**, not existing Agda declarations or hidden theorem completions.

**W0a — `originalWilsonCMP119PhysicalDomainDictionary`.** For each selected genuine 4D Wilson cutoff/volume/scale, construct from native periodic links and plaquette incidence the exact `Ω_k,Λ_k,S_k,B` family, determining sets, nonempty components, nested/small/large admissibility and source-measure domains. Reuse `P10SourceFaithfulActivityContract.P10P11WeightedRelativeDomainCarrier`, `BalabanCubeEdgeDomains`, `BalabanClayGate4FiniteEnlargementCollarOwnershipExact` and original periodic carrier. Prove source cover AND reverse selection of the genuine component and step indices; retain all exceptional and excluded-domain indices as a separate signed residual. Geometry merely naming a domain is insufficient.

**W0b — `originalWilsonCMP122ConstrainedMeasureChange`.** Construct the measure-preserving dictionary between the **original** compact SU(N) Haar constrained Wilson fluctuation/gauge integral and *the historically selected* Eq. (1.71) `T/rT` component integral. Prove forward and reverse equality on a measure-determining selected test algebra with one normalization, explicitly accounting for constraint deltas, gauge fixing, Jacobians/FP/ghost, background `V`, E/R/B and vacuum normalization. A candidate `R445` map can be reused but is not automatically the historical `T` operation; prove the actual identified conjugacy or a controlled residual. Respect zero-mode stabilizers/gauge quotient and all six 4D orientation planes; no silent factorization of original spectators.

**W0c — `originalF19SelectedEq171FourColumnCorrespondence`.** On the same selected domain, the actual original Wilson weight carries four *unique* marked coefficients `K0,KF,KG,KFG` from `YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact`, `YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact` and `YMClaySUNWeightedHaarPairFibreDisintegrationExact`. Prove their equality to the corresponding four **selected** CMP119/122 `T` masses, or prove a precisely quantified four-component discrepancy with explicit source terms and signs. Only then supply `BalabanCMP119Equation171WeightedStepApproximationExact.sourceStepIsEquation171Mass`; do not fill its field with a tautological definition unrelated to the original article. The side-four benchmark contains 64 original ordered pairs, 896 spectators, 1024 positive links and 1536 plaquettes, but an all-refinement theorem cannot be inferred from this one finite box.

**W1 — `originalCMP119F19SignedFibreHessianLedger`.** Reuse, rather than duplicate, `BalabanFiniteRGTotalCovarianceExact.finiteRGTotalCovariance`, `BalabanFiniteRGMultiscaleCovarianceTelescopingExact`, `BalabanFiniteRGGoodBadResidualEnvelopeExact` and original F19 transports. At any positive coarse fibre `K0(W)>0` define
```text
K(W;s,t)=K0(W)+s KF(W)+t KG(W)+st KFG(W),
A(W)=KF(W)/K0(W), B(W)=KG(W)/K0(W),
R_fibre(W)=KFG(W)/K0(W)-A(W)B(W).
Cov_fine(F,G)=Cov_(K0 dH / ∫K0 dH)(A,B)+E_(K0 dH / ∫K0 dH)[R_fibre].
```
This algebra already exists at the appropriate abstract and finite levels. The missing task is **continuous source incarnation** with the original 4D Wilson product-Haar and historical CMP119/122 selection, including integrability, conditional fibres and the case `K0_good(W)=0`. Preserve the zero sector: do not divide at such W or infer pointwise positivity from positive total good mass. The signed `R_fibre` may be nonzero; conditional means of fine marks do not imply coarse measurability of the marks.

**W2 — `originalCMP116GoodSourceThreeResidualBound`.** Reverse-solve `|Cov_good(F,G)-C_CMP116|≤C_m exp(-m_mR)` into proof-accounted same-source contributions: (i) conditional fibre Hessian, (ii) induced coarse transported-mark covariance and (iii) original effective-law / historical CMP119/122 comparison, each with the genuine marked-normalization terms. Use `YMClayD1OriginalRealCMP116VariableCutoffExact.sourceResponseIsActualOriginalWilsonJet`, source-selected CMP119 `Ω/Λ/S` and `BalabanLiteralWilsonMarkedLocalizationSourceExact.normalizedWilsonResponseIsMarkedMixedDerivative` as target fields. **A bad-contour tilt alone does not force good-law/CMP116 equality.**

## P0X — actual weak-coupling physical-rate theorem cutset

**X0 — `originalRenormalizedGoodLargeFieldHistory`.** Reuse CMP119's genuine source E/R/B/V state and CMP122-I's localized `R` small-field replacement / component selection; identify the original cutoff running `β(a)`, the full normalized density and every source-dependent denominator. Bare-side strong-coupling Dobrushin `q<1` is not a UV weak-coupling estimate. The CMP122-I small factor `exp(-P0(g0))` does **not** give a positive power of the cutoff; the renormalized (R)-operation and source geometry are indispensable.

**X1 — `originalConnectedMarkedActivityBound`.** On each source-selected and genuinely connecting cluster, prove a pointwise absolute bound for the **actual marked** derivative (direct Hessian, source-score covariance, boundary/exceptional terms), on the correct CMP119/122 analyticity domain and with all source interaction spectators. Reuse P06 animal entropy, R429/Step-V and `BalabanLiteralTwoWilsonCMP116ConnectingTailExact`; their combinatorial tail compilers are already present. Neither toy Q8 sampling nor a hypothetical independent plaquette probability pays this theorem.

**X2 — `originalLargeFieldExceptionalSuppression`.** Prove the physical full-Gibbs exceptional weight/bad-mass decay on the source CMP122-I/II R-operation class, including all components not controlled by the good fibre and correct renormalized normalization. Reuse `BalabanFiniteRGExceptionalCovarianceMassExact.exceptionalCovarianceBelowTwiceMass`. This is a **source analytic estimate**, not a new covariance identity.

**X3 — `originalUniformPhysicalRootedShellRate`.** Establish a shared positive SI physical rate and cutoff/volume-independent prefactor:
```text
forall a in admissible UV trajectory, L in admissible volumes, R>=R_min:
  terminal(a,L,R) + sum_j |goodMarkedFibreResidual_j(a,L,R)|
      + sum_j |exceptionalMarkedResidual_j(a,L,R)|
  <= C exp(-m R),  where C<infinity and m>0 independent of a,L.
```
The exact existing consumers are `BalabanFiniteRGGoodBadResidualEnvelopeExact.finiteRGClusteringFromGoodBadEnvelope`, `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.chargeSumBelowPhysicalRootedShell` and `YMClayD1OriginalFullWilsonSmallLargeFieldExact.OriginalSmallLargePhysicalSource.originalFullCovarianceBelowSmallPlusLarge`. Do not infer a uniform physical rate from `q(a)<1` alone; show the physical spacing and prefactor scaling. A direct literal W1/W3 absolute proof may REPLACE P-CONT/P-MATCH as a sufficient path but does not bypass source-identification.

## P0Y — parallel continuum endpoint / proof trust

Complete `YMClayE1OriginalSUNFiniteCylinderLawsExact.ActualSelectedOriginalSUNConvergence.originalWilsonCylinderConverges` and the exact-head full E1 sanctioned Agda kernel receipt; build the genuine original Wilson continuum OS Gram/the same H, uniform clustering on a dense gauge-invariant local-word core, positive spectral gap with nonvacuum zero-energy exclusion, N1 survival of a nontrivial observable and G1 all compact simple groups. The transitive `RealAnalysisAxioms` / `--safe` trust boundary remains independently blocked. Preserve `YangMillsClaySolved=false` / `clayYangMillsPromoted=false`.

## What counts as progress, and what does not

1. **Primary-symbol receipt:** inspected original page image for each selected Eq. (1.71)/(2.18) term; extracted sources alone do not settle corrupted symbols. Cite printed page/DOI and retain the original primary author.
2. **Same-source proof:** a concrete original Wilson 4-column integrand/measure, actual CMP source domain, forward and reverse index/field transport, and explicit Jacobian or controlled mismatch. A new record with `sourceStepIsEquation171Mass` as an assumption is not payment.
3. **Native kernel proof:** sanctioned `scripts/run_agda29_parallel_check.sh <module.agda>` on the exact source head; no user GitHub CI; `--safe` and legacy axioms audited separately. Cheap SymPy/static tests validate only their own contracts.
4. **Physical estimate:** absolute connecting charge/bad-field bound derived on the real 4D SU(N) weak-coupling source, one fixed physical `C,m` independent of UV cutoff and volume; no cherry-picked scale or bare β.
5. **Endpoint:** only the actual original continuum E1+OS, D1, nontrivial N1, same-H full D2 and G1 admits Clay-flag review. No such endpoint is claimed here.

**Current state:** new proof PROGRAMME authorized and recorded; P0W/P0X physical source inhabitants are OPEN. The missing exact Eq. (1.71) glyphs and source dictionary require a primary page-image inspection; there is no permission to replace them with invented formulas.
