# Origin Traceability Ledger

Declared surface level: `bridge/governance`.

This ledger reconciles
`temp-DOWNLOADED/DASHI_origin_traceability_disconnections.md` with the current
repo. It is a reader and reviewer surface, not a theorem owner. Its purpose is
to keep the origin story visible without upgrading bridge, packaging, or
empirical lanes into stronger claims than the Agda modules carry.

## Origin Thesis

The useful organizing thesis is:

> contraction on a ternary carrier produces stable structure.

In repo terms, that means:

- carrier: `Base369.TriTruth`, `DASHI.Algebra.Trit`, and
  `DASHI.Physics.RealTernaryCarrier.Carrier n`;
- metric: the prefix/agreement ultrametric over ternary vectors;
- contraction surface: bounded non-expanding/strict maps plus explicit
  fixed-point or descent certificates;
- scalar modulation bridge: the `47 * 59 * 71 + 1` CRT/J identity and the
  p47/p59/p71 SSP positions.

This is currently a `bridge` thesis. It is not a theorem that every downstream
physics module is an instance of one universal fixed-point theorem. A theorem
surface becomes origin-traceable only when it says which role it plays:

- `A`: instance lane, naming a concrete map, carrier, certificate, and consumer;
- `B`: structural lane, proving or packaging a carrier, metric, algebraic,
  signature, Clifford, moonshine, or seam property needed by an instance lane.

## Current Reconciliation

| Surface | Current repo state | Correct traceability reading | Remaining gap |
|---|---|---|---|
| CoreSpine carrier bridge | Exists through `TritTriTruthBridge`, `TritCarrierBridge`, `FascisticContractionInstance`, `MoonshineBridge`, `CRTPeriodJFixedBridge`, and `StageQuotient`. | `B`: structural bridge from triadic algebra to the ternary carrier, agreement ultrametric, contraction-certificate interface, and CRT/J scalar. | Concrete descent/fixed-point certificates are still per-map obligations; active-wall periodicity and Monster representation semantics are obligations, not proved facts. |
| `MinimalCrediblePhysicsClosureShiftInstance` | Exists and packages full closure, observable prediction, and signature match. | `A + packaging`: current bounded shift-side minimal closure instance. | Origin receipt is not co-located. A reviewer must follow several modules to see carrier, map, signature, dynamics witness, and scalar bridge. |
| W8 origin observation receipt | `P0BlockadeProofObligations` now exposes `OriginObservationReceipt` beside the older `OriginReceipt`. | `bridge/governance`: conservative typed receipt surface that names `Source`, `Carrier`, `Obs`, `SignatureOwner`, `DynamicsWitness`, `CRTJBridge`, `mapToCarrier`, `carrierTransport`, `originObservationMap`, concrete owner/witness/bridge values, `EmpiricalReceiptStatus`, `empiricalCaution`, and `closureClaimBoundary`. | No instance is promoted here. The record does not require `EmpiricalAdequacy`, `ConvergenceBound`, or `MDLSeam`; consumers must import or discharge those obligations separately before claiming adequacy, convergence, seam closure, or empirical prediction. |
| W8b minimal-credible shift origin observation | `MinimalCredibleShiftOriginObservation` now instantiates `OriginObservationReceipt` for the `minimumCredibleClosureShift` path with typed source/carrier/observation tokens, projections to the actual minimal-credible closure, signature equality owner, dynamics witness projection, and CRT/J bridge surface. It also exposes `MinimalCredibleShiftBlockedOriginInstance`. | `A + bridge/governance`: concrete non-promoting origin-observation receipt for the minimal-credible shift path. | Positive origin/empirical promotion remains blocked on `missingEmpiricalAdequacyBridge`; the receipt marks `empiricalBlocked` and does not claim empirical adequacy, convergence-rate closure, or MDL seam closure. |
| W8c origin receipt promotion obligation | `OriginReceiptPromotionExternalObligation` names the external receipt shape needed to move the minimal-credible origin receipt beyond `empiricalBlocked`: empirical adequacy or promoted empirical status, origin-observation-map compatibility, and closure-boundary preservation. | `bridge/governance`: explicit promotion intake surface for the already-landed origin receipt. | It does not alter the existing receipt status and does not construct an empirical adequacy bridge, `P0.OriginReceipt`, or closure promotion. |
| `CanonicalStageCTheoremBundle` | Exists as a large summary bundle over many canonical and known-limits theorem surfaces. | `packaging`: useful status bundle, not a new primitive origin theorem. | Needs reader-facing traceability back to the origin thesis and explicit non-claim boundary. |
| Empirical chi2 / orbit-shell lane | Exists as bounded audit and validation surfaces, including `ShiftContractMdlLevelChi2WitnessAudit` and `RootSystemB4ShellComparison`. The chi2 audit records `poolCarrierMismatch`, and the B4 comparison currently marks the candidate `standaloneOnly`. | `empirical + validation`: evidence and diagnostics, not theorem-source truth. | No theorem currently proves that an origin fixed point uniquely predicts the observed empirical profile. A future `EmpiricalAdequacyBridge` would first need to resolve the carrier mismatch and promotion status. |
| `AtomicChemistryRecoveryTheorem` | Exists locally and is already named as a strong owner in reader docs. Its own comments explicitly say it does not claim atom recovery, spectra recovery, or chemistry recovery from the canonical closure stack. | `packaging/bridge`: strongest current atom/chemistry interpretation carrier with explicit gates. | Needs a dynamics/relaxation bridge and stronger chemistry-facing law before it can be read as actual atomic or chemistry recovery. |
| `CanonicalDynamicsLawTheorem` | Exists and packages propagation, causal admissibility, monotone quantity, and continuum-law slots. | `bridge`: theorem-bearing status surface over current bounded dynamics witnesses. | It does not yet prove a realization-independent convergence-rate theorem of the form `d(K^t x, x*) <= max 0 (d(x, x*) - t)`. |
| Photonuclear empirical lane | Exists and is already normalized through registry, measurement, evidence, and validation summary docs/modules. | `empirical`: calibration and diagnostic lane. | Must remain separated from theorem claims until a theorem-owned adequacy bridge connects predictions to observations. |
| NGram / ITIR join sidecars | `DASHI.Combinatorics.NGram` and `DASHI.Interop.ITIRJoinBridge` exist locally and are aggregate-imported by `DASHI.Everything`. | `bridge/adapter`: n-grams are fixed-width ternary windows; ITIR join is a conservative UFTC severity/code to pressure adapter. | No text semantics, live ITIR runtime, production join-edge classifier, or system theorem is claimed. The next promotion step is consumer wiring. |
| ITIR PNF / residual logic sidecars | `DASHI.Interop.SensibLawResidualLattice`, `DASHI.Algebra.TetralemmaBridge`, `DASHI.Algebra.SixfoldLogic`, and `Ontology.Hecke.PNFResidualBridge` exist locally and are aggregate-imported by `DASHI.Everything`. | `bridge/adapter`: residual levels form a proved four-level join-semilattice; PNF comparison is signature-fibred with wrapper gating and index fallback; `PNFEmissionReceipt` makes emitted atoms receipt-bound; `performativeEvidence` maps to `scopeExceeded6` only when emitted by the pipeline; `TriTruth` embeds into the non-contradiction residual image; six-level residual refinement embeds through `Base369.HexTruth`; the Hecke quotient-fibre adapter maps stable/illegal/other defects into partial/contradiction/noTypedMeet residual pressure. | No spaCy parse, PNF atom, residual comparison, live political claim, Hecke support class, sixfold carrier, or domain-incommensurability label is promoted to semantic authority or physics theorem input without a future receipt-bearing consumer. No wrapper/qualifier/signature/domain label may be assigned by human inspection. |
| Claim comparison engine | `Docs/ClaimComparisonEngine.md` exists as the normalized reader surface over the PNF/residual sidecars, UFTC pressure, logic-carrier bridges, and Hecke adapter. | `documentation/bridge`: accurate current-state map of runtime emission versus compiled residual algebra. It now also records operator-level formula fixtures as receipt-bound local-expansion hypotheses, not as proof certificates, records domain-incommensurability as an open design fixture rather than a compiled residual value, and separates political-label PNF claims from formal operator traces. | The engine is not complete as a product or theorem consumer. It still needs runtime receipt fixtures, a checked receipt import/certificate format, and a theorem-side consumer for residual evidence. A formula span cannot prove a real-world `AntiFascistSystem` instance, empirical period, actor classification, market response, failed cross-domain measure bridge, or state-level political label without a separate model witness and taxonomy. |
| Attractor / orbit classifier | `Docs/AttractorOrbitClassifier.md` exists as a design note over receipted residual, wrapper, domain, formula, and Hecke features. | `design/bridge`: useful downstream hypothesis generator for convergent/orbiting/terminal trace labels after receipts and feature extraction exist; it now records state/institution operator classification as a composite per-domain hypothesis surface, aggressor/responsibility classification as a shared-fibre or cross-fibre taxonomy-and-receipt fixture, existential/multi-domain operator completeness as a physical-survival-witness fixture, enemy-classification operators as lineage-fixed or behaviour-conditional textual fixtures, collapsed quotients as well-formed no-typed-meet/product-lattice fixtures, protected-identity/conduct-axis and three-body models as product-lattice/decision-projection fixtures, hostile-provenance and four-body theology as source-critical product-lattice fixtures, non-Abrahamic/N-body comparative lattices as school-level carrier/process/perspective fixtures, East Asian/Indigenous living lattices as culturally governed topology-changing carrier fixtures, affective-state/feelings-wheel models as non-clinical taxonomy-and-session fixtures, Base369-chain interpretation as an algebraic-lift fixture, pairwise interaction classification as a product-carrier fixture, conditional-trigger/latent-fixed-point classification as a trigger-semantics fixture, bot/source join-domain exactness as an orbit-input-bijectivity design target, and global phase/bifurcation classification as a state-space fixture. | Not a theorem, production classifier, trading bot, market predictor, price-floor model, hidden-cause attribution engine, political-label classifier, aggressor/responsibility classifier, existential-completeness classifier, enemy-classification classifier, collapsed-quotient resolution oracle, two-axis/three-body legal-theological classifier, hostile-provenance/four-body theology classifier, non-Abrahamic/N-body comparative classifier, living-lattice classifier, affective-state classifier, clinical tool, diagnosis, treatment model, Base369-chain semantic classifier, relational conflict classifier, trigger-resolution oracle, canonical-source selector, or global phase-transition detector. Promotion needs checked feature extraction plus separate empirical, causal, political/legal taxonomy, responsibility taxonomy, cost/threat/response receipts, third-party burden provenance where relevant, physical-survival witness receipts, warrant-ordering rules, typed multi-domain interaction operators, textual/theological receipts, source-critical wrapper profiles, school-level comparative receipts, culturally governed living-tradition receipts, affective taxonomy and subject/session receipts, psychometric or clinical validation status, clinical non-authority flags, classifier-input taxonomy, inverse/deactivation semantics, quotient maps, lost-distinction records, role-binding taxonomies, component meet/join laws, orientation maps, process/action/perspective semantics, relation/flow/graph/bundle semantics, affective tone/naming/wrapper semantics, product-lattice/lift semantics, decision-projection rules, typed Base369 carrier maps, commutation/seam proofs, product-operator validation, trigger receipt/connective/deactivation semantics, typed observation-map/canonical-representative theorem, and global carrier/basin/threshold/interaction-operator model. |
| Mathematical atlas / higher-structure charts | `Docs/AttractorOrbitClassifier.md` and `Docs/ClaimComparisonEngine.md` now record category-theory, Jain-topos, HoTT, ergodic, information-geometric, coinductive/non-well-founded, tropical, renormalization, and infinity-categorical readings as possible future chart languages. | `design/governance`: these charts can organize future promotion work for cross-lattice morphisms, sevenfold truth carriers, path identity, scan-order ergodicity, MDL geometry, circular dependency carriers, degeneration limits, scale flow, and higher morphisms. | No theorem currently proves that DASHI is an infinity-topos, that Jain predication is a repo subobject classifier, that Whakapapa/Dreaming is a HoTT path space, that Songlines or scan orders are ergodic-maintenance laws, that PNF/MDL selection is a Fisher-geodesic projection, that collapsed classifiers are tropical degenerations, that any operator has RG relevance, or that `JFixedPoint` is a terminal object. Promotion needs typed chart carriers, morphisms from receipted PNF/residual/operator surfaces, preservation laws, and validation. |
| Cross-scale physics / biology / consciousness charts | `Docs/AttractorOrbitClassifier.md` and `Docs/ClaimComparisonEngine.md` now record quantum, QFT/RG, thermodynamic, chemical, molecular-biology, epigenetic, neuroscience, affective, theological, and consciousness readings as scale-unification fixtures. | `design/governance`: these charts can organize future promotion work for typed scale carriers, scale maps, and observable-preservation laws between physical, biological, neural, affective, social, and theological surfaces. | No theorem currently proves that quantum collapse is vedana, projectors are Amalek, unitaries are AntiFascistSystem, DharmaSystem is gauge symmetry / Maxwell demon / DMN, Monster / 196884 is a string-theory vacuum, `FascisticSystem` is the second law, Landauer erasure proves cultural-memory destruction, live triggers are chemical phase transitions, `CRTPeriod` is correlation length, DNA eigenclasses are literal DASHI biology, epigenetics is a Dreaming layer, trauma or healing are epigenetic operator theorems, polyvagal states are Base369, IIT Phi is `JFixedPoint`, or the full chain is reality's self-description. Promotion needs typed carriers at each scale, scale maps, preservation laws, measurement protocols, empirical validation, and clinical non-authority flags where neural, trauma, affective, or health-related claims are involved. |
| Neurochemical / body-brain-chemistry charts | `Docs/AttractorOrbitClassifier.md` and `Docs/ClaimComparisonEngine.md` now record synaptic/electrical, volume-transmission, endocrine/hormonal, and epigenetic or cultural propagation readings as biomedical cross-scale fixtures. | `design/governance`: useful for future typed biological carrier work if neurotransmitters, hormones, receptors, biomarkers, and organism-scale state variables are modeled separately from DASHI operator labels. | No theorem currently proves that synaptic vesicle release is quantum measurement or vedana, receptor context is Jain Naya, GABA is FascisticSystem, glutamate is AntiFascistSystem, volume transmission is a Dreaming layer, dopamine is MDL compression, serotonin is Seven Generations, norepinephrine is Amalek precision weighting, oxytocin is Whakapapa chemistry, cortisol/allostatic load is an Amalek marker or Hutchinson gap, insulin controls trader operator class, acetylcholine is lattice depth, or the body-brain-chemistry triad is Base369 / DASHI made flesh. Promotion needs typed synaptic/electrical, volume-transmission, endocrine/hormonal, and epigenetic/cultural carriers, receptor/context models, biomarker measurement protocols, causal hypotheses, biomedical validation, and clinical non-authority flags. |
| Market self-observation / trader-operator charts | `Docs/AttractorOrbitClassifier.md` and `Docs/ClaimComparisonEngine.md` now record trader-as-node, market-as-RG-stack, operator-trading psychology, three-conjunct signal architecture, MDL market compression, and `JFixedPoint trade` readings as market hypothesis fixtures. | `design/governance`: useful for future risk-model architecture if trader-state, market-data, cross-scale, execution, and validation surfaces are explicitly typed. | No theorem currently proves that trader state determines operator class, that market price is an RG fixed point, that any civilisational operator is market-RG-relevant, that a three-conjunct trigger is a trading signal, that MDL compression predicts price, or that `JFixedPoint` exposes cycle exhaustion before price. Promotion needs typed trader-state receipts, market-data receipts, cross-scale maps, execution/risk/cost/compliance rules, period/regime-change definitions where claimed, and out-of-sample validation. |
| Temporal sheaf / time-indexed state charts | `DASHI.Physics.Closure.TemporalSheafProofObligations`, `Docs/AttractorOrbitClassifier.md`, and `Docs/ClaimComparisonEngine.md` now record temporal qualification as a possible state-space dimension rather than only a flat statement qualifier. | `design/governance + proof obligation`: useful for future temporal semantics where slices become sections over Time and consistency becomes gluing over overlaps. | No theorem currently proves that current PNF slices are sheaves over Time, that `Overlap` is a restriction map, that `MereViol` is a sheaf non-gluability certificate, that exclusive properties form line bundles, that `JFixedPoint` is a time-topology transition, or that `Ultrametric.agda` supplies a metric over temporal sections. Promotion needs typed Time/Interval/Property/Value/Section/Global carriers, overlap/restriction/gluing laws, exclusivity semantics, pre/post sheaf transition maps, a proof that the transition is not merely CRT recurrence, and a temporal section metric. |
| Spacetime sheaf / mereological-space charts | `DASHI.Physics.Closure.TemporalSheafProofObligations`, `Docs/AttractorOrbitClassifier.md`, and `Docs/ClaimComparisonEngine.md` now record spatial containment as a possible second index for temporal sections. | `design/governance + proof obligation`: useful for future semantics where Time and a typed Space/mereological carrier jointly index statement validity, and slice transitions become constrained evolution over spacetime sections. | No theorem currently proves that temporal qualifiers plus mereological/location properties form spacetime, a 3+1 split, Cauchy evolution, a spacetime density matrix, a closed-timelike-curve rejection law, or a `JFixedPoint` singularity. Promotion needs typed Time/Space carriers, containment and spatial-overlap laws, sections over `(Time, Space)`, spacetime gluing, exclusive-coordinate uniqueness, slice/delta/admissibility carriers, evolution validity preservation, and pre/post extension-obstruction witnesses. |

## Ordered Promotion Gates

1. Add an origin receipt surface for the minimal-credible closure path.
   This now has a W8 Agda owner surface and W8b instance:
   `P0BlockadeProofObligations.OriginObservationReceipt` names the carrier,
   carrier transport, origin observation map, signature owner, dynamics witness,
   empirical status/caution, and CRT/J bridge, while
  `MinimalCredibleShiftOriginObservation` points that surface at the
  minimal-credible shift path. The instance remains non-promoting:
  `empiricalStatus = empiricalBlocked`, with
  `missingEmpiricalAdequacyBridge` as the typed missing field.
  `OriginReceiptPromotionExternalObligation` now names the external promotion
  receipt needed to change that status, without changing it.

2. Add an empirical adequacy bridge only when the theorem ingredients are
   actually available. The bridge should consume the fixed-point/certificate
   surface, the chi2 audit, and the orbit-shell comparison, and state exactly
   whether it proves equality, a bound, or only a carrier-mismatch diagnostic.
   The current chi2 audit is explicitly carrier-mismatched, so this gate is not
   dischargeable by packaging alone.

3. Complete the dynamics promotion as a convergence-rate theorem. The existing
   `CanonicalDynamicsLawTheorem` is a good owner surface, but the missing claim
   is a rate and horizon theorem, not another status record.

4. Promote atom/chemistry only through the explicit gates already exposed by
   `AtomicChemistryRecoveryTheorem`. A dynamics/relaxation bridge may compose
   with that carrier, but it must not claim spectra, bonding, wet-lab recovery,
   or textbook chemistry unless the corresponding theorem surface exists.

5. Keep the moonshine scalar bridge honest. `period + 1` and the p47/p59/p71
   positions are formal bridge facts; `c1(j)` representation semantics and
   wall-pressure periodicity are named obligations until proved inside the repo.

## Worker Coordination For Promotion Gates

Promotion gates now have worker-facing owner surfaces:

- Origin receipt:
  owner lane `W8`, source surface `P0BlockadeProofObligations` plus this
  ledger, non-claim boundary: receipt packaging does not strengthen closure.
- Empirical adequacy:
  owner lane `W3`, source surface empirical closure modules and photonuclear
  registry, non-claim boundary: empirical sidecars and carrier-mismatch audits
  are not theorem adequacy.
- Dynamics / natural law:
  owner lane `W2`, source surface `CanonicalDynamicsLawTheorem` and natural
  charge / `p2` modules, non-claim boundary: a status package is not a
  convergence-rate theorem.
- Atom / chemistry:
  owner lane `W4`, source surface `AtomicChemistryRecoveryTheorem` and
  `ChemistryRightLimits*`, non-claim boundary: quotient-sensitive laws are not
  spectra, bonding, wet-lab recovery, or textbook chemistry.
- Continuum / MDL / abstract seam:
  owner lane `W1`, with `W8` for receipt packaging when needed, non-claim
  boundary: fieldwise equalities and retargeting do not prove a CR-flat target
  or aligned carrier.
- GR/QFT consumers:
  owner lane `W5`, source surface known-limits and consumer modules, non-claim
  boundary: coarse/interpretable transport is not full GR/QFT recovery.
- ITIR/PNF consumers:
  owner lane `W6`, source surface interop and residual bridge modules,
  non-claim boundary: no PNF/residual/domain label is semantic authority
  without receipts.

## Non-Claims

- This ledger does not prove the origin thesis.
- It does not turn empirical audits into empirical adequacy theorems.
- It does not turn `AtomicChemistryRecoveryTheorem` into spectra, bonding, or
  chemistry recovery.
- It does not claim a natural, realization-independent dynamics law.
- It does not claim every module in the repo is an instance of one concrete
  fixed-point theorem.

## Review Rule

When adding or promoting a theorem-facing surface, classify it before merging:

- `A` if it names a concrete carrier, map, certificate, and downstream consumer;
- `B` if it proves structural carrier/metric/algebra/seam data needed by `A`;
- `packaging` if it only assembles already-existing surfaces;
- `empirical` if it records measured or validation data without theorem
  derivation;
- `speculative` if it is roadmap language without a theorem owner.
