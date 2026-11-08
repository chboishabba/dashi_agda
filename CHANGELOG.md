# Changelog

This changelog is append-only. Older mentions of `false` are historical wave
records unless the entry explicitly states it is describing the current live
monitor surface.

## 2026-07-19 — Wetsuit seam optimisation boundary

- Added `DASHI.Geometry.WetsuitSeamOptimisationBoundary`, a fail-closed typed
  carrier for body-zone design priors, material/panel budgets,
  manufacturability evidence, weighted seam cost, admissibility, relative
  optimality, validation gates, and split advice.
- Added `DASHI.Geometry.WetsuitSeamOptimisationRegression` with canonical
  underarm/inner-leg preference and shoulder/spine avoidance prior receipts,
  while keeping continuum optimality and manufacturing authority explicitly
  unpromoted.
- Added the compact aggregate `DASHI.Geometry.WetsuitSeamOptimisation`.
- The module formalises the optimisation and obligation surface only; it does
  not claim universal biomechanics, continuum-mechanics closure, or certified
  manufacture. `DASHI.Everything` was not run in this connector-backed pass.

## 2026-07-13 — P06 duplicate-free valid-walk enumeration

- Added and focused-checked `P06GeneratedWalkUniqueness.agda`.  Under the
  canonical neighbour adapter it proves extension-block `NoDuplicates`,
  recursive block disjointness, and
  `generatedWalkVertexListsNoDuplicates` without postulates or proof-heavy
  `WalkObject` equality.
- Added `GeneratedWalkVertexListSemantics`, packaging generated valid-walk
  lists, extensional completeness, duplicate-freedom, and the single
  `countWalks ≡ length` bridge.
- Added focused-checked additive `P06ConcreteEnumerationEndpoint.agda` and
  `P06SkeletonEnumerationSurface.agda`.  The former makes DFS membership an
  explicit field of a membership-indexed map; neither module touches the
  legacy total-index API.
- Added focused-checked `P06ConcreteSkeletonWitness.agda`, which proves all
  individual-candidate chooseN facts and packages the remaining skeleton list
  obligations (`complete`, vertex-list uniqueness, and count agreement)
  without pretending they are derivable from an arbitrary list.
- Added focused-checked `P06DFSValidWalkSurface.agda`.  It packages the
  minimal per-skeleton `WalkObject` plus equality to `dfsWalkRange`, derives
  generated-list membership and soundness, and adapts map witnesses to the
  membership-indexed endpoint.  It deliberately does not infer path validity
  from `DFSCover` coverage alone.
- `Everything.agda` was not run.  The remaining P06 mathematical blocker is
  now the genuine DFS-valid-walk membership witness; the legacy total-index
  record remains compatibility-only.

## 2026-07-13 — Corrected P06 walk status

- Corrected the P06 record: recursive walk completeness has landed through
  `walkObjectsCompleteByVertices`, and successor-membership inversion has
  landed through `walkObjectsSucMemberByVertices` and
  `walkObjectExtendMemberByVertices` in
  `DASHI/Physics/YangMills/GraphCombinatorics.agda`.

## 2026-11-08 — CCDCOE P3 G20/COP21 institutional cross-case original-source cut

- **Source authority and attribution:** original G20 Brisbane ¶19 (2014), Antalya ¶24 (2015), COP21 decision 1/CP.21 (2015), treaty Article 4.2 (operative from 2016), and Hamburg (2017) speakers are attributed to their actual original institutions. The 2017 US withdrawal position and other G20 leaders' continuing support remain DIFFERENT speakers and position scopes. Original C20 Turkey 2015 civil-society communiqué and B20 Turkey 2015 submission catalog remain their own organisations' documents, not leaders' adopted commitments.
- **DASHI proof attribution:** new `DASHI/Cognition/CCDCOEP3G20COP21AttributionExact.agda` instantiates EXISTING `DASHI.Core.IntersectionalNonFactorability` and `DASHI.Core.DiscriminatorSynthesisExact` proofs. External authors do not receive DASHI theorem attribution; DASHI gains no claim to their historical authorship/endorsement.
- **Original evidence:** `Docs/research/ccdcoe_p3_g20_cop21_attribution_manifest.json` retains nine original source identities, ten selected claims, exact author and legal speech act, separate source dates and original-source locators, null actual lobbying/doc-drafting transmission, no fabricated full-original-byte hashes or statistical effect measures.
- **Fail-closed checks:** `scripts/check_ccdcoe_p3_g20_cop21.py` validates original speaker/claim joins, Hamburg split, civil/business submissions versus adopted text, Paris adoption-versus-entry-into-force and dated withdrawal announcement, plus optional original bytes SHA256 / reviewed extracted passage receipts. Synthetic negative tests do not constitute original source review.
- **Golden governance:** imported into `DASHI/Cognition/Everything.agda` and `CCDCOEP3CausalTrialecticRegressionExact.agda`; wired into `scripts/check_ccdcoe_cognition_agda.sh` via the existing `parallel_checker`. This commit records source-written mathematical claims, **NOT** an exact-head Agda kernel acceptance receipt or reproduced causal influence.
- **Roadmap and source atlas:** `Docs/research/CCDCOEP3G20COP21PrimarySourceAttribution20261108.md`; `Docs/roadmaps/CCDCOEP3CausalTrialecticSourceMaxCut20261106.md`. Remaining gates I0–I5: original source bytes/review, full corpus and coder reliability, actor-to-draft transmission, country-level compliance/implementation, causal identification, independent replication and kernel acceptance.
