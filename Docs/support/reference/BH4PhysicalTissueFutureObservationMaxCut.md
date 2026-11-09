# BH4 ↔ physical-tissue future-observation max-cut

Updated 2026-11-07. These two DASHI heads are **separate**, not
a compiled same-object proof:
- developmental-history PR #1471: `chatgpt/biology-history-future-quotient-20261106`;
- Kitzerow source/29×12 BH4 PR #1454:
  `feat/kitzerow-bh4-pathway-ontology-interop`
  (stacked on #1226 and #1159, with historical merge debt).

## Physical theorem and model responsibilities

Let `x` be a source-specific compartment/redox/cell/tissue physical state;
`u` a time-dependent intervention; `K_u` its measured or derived
physical stochastic transition kernel; `O` the measured phenotype;
and `pi` a proposed future-sufficient state projection.

**One selected physical model** must pay:

1. `BH4.sameStateSameCompartmentTime`: explicitly identify original
   BH4 pools, BH2/NAD(P)H, QDPR recycling, TH/TPH/NOS/AGMO demand,
   enzyme abundance, ion/electrochemical state, compartment and clock.
2. `BH4.reactionAndExchangeBalance`: source-pinned Rhea reaction direction
   and measured 29-species exchange + 12-reaction flux intervals,
   and distinct nonfinite chemistry residuals. Use existing
   `BH4SystemStateExact`, `BH4OpenMetabolicNetworkAdapterExact`,
   `BH4JointFluxFeasibilityExact` and `BH4ExchangeIdentifiabilityExact`.
3. `physicalStepRefinesTissue`: for all 27 voxels, the original
   PNP/chemistry/tissue physical step agrees with the nonperiodic
   54-bond biological readout. PR #1471's
   `BiologicalSourcePhysicalTissueSimulationExact` proves the
   arbitrary-history consequence once this one-step source proof exists.
4. `futureDistributionCommutes`: pushforward of the original
   stochastic physical kernel factors through the selected observed
   quotient for each intervention, with properly calibrated conditional
   rates. PR #1471 already proves abstract finite rational-weight
   18-class lumping, including inhomogeneous action histories.
5. `heldoutInterventionDiscriminates`: paired original measurements on
   the *same* samples/compartments/times distinguish allocator against
   parallel redox and context-specific non-allocator models, with
   specimen/experiment disjoint splits and independently replicated tests.

## New exact results, separate branches

- PR #1454: `BH4AllocatorFutureObservationCountermodelExact`
  proves that the same synthesis+recycling supply and an exactly balanced
  selected five-sink budget can produce **different** branch-specific
  responses. Scalar BH4 availability is not future-sufficient for all
  branch observations, even if a mass balance is satisfied.
  `scripts/check_bh4_allocator_future_observer.py` enumerates finite
  nonnegative balanced allocations as a numerical regression.
- PR #1471: `BiologicalSourcePhysicalTissueSimulationExact`
  derives all-action-history 54-bond coarse-phenotype agreement
  pointwise, without function extensionality, from an **explicit**
  PNP-selected physical one-step simulation receipt.

## No unsupported transfers

This bridge is a planned **cross-branch** physical theorem target, not a
claim that Kitzerow's autism/comorbidity hypothesis is confirmed by
planarian experiments, that a dmsC assay measures BH4, or that any
specific person has a disease mechanism. Source-curated Rhea/ChEBI
chemistry predates the proposed allostatic allocation synthesis.

The creator's own public discussion of resource competition, temporal
displacement and the BH4 shunt proposes the mechanistic hypothesis; a
candidate graph is not its kinetic confirmation. In particular 190 SABIO
rows / 932 acquired quantitative values do not automatically establish
same-tissue, same-compartment, same-state 12-reaction and 29-exchange
physiological flux bounds. The author's original chart is not the
independently selected DASHI 12-reaction panel.

**Merge gate:** reconcile the BH4 stacked ancestors with current
developmental biology head, then import both native Agda owners into a
single Golden root; obtain exact-head `parallel_checker` kernel acceptance.
No cross-branch import is added until then. Neither pathway alone
creates an original joint physical dataset, an authenticated source
passage, a reviewed PostgreSQL PNF promotion, or clinical causality.

## Arrow semantics

The arrows in causal/verification diagrams are maps, dependencies
or directed model transformations, not Conway's large-number operators.
Conway's numeric `a -> b` is `a^b`;
`a -> b -> c` is `a ↑^c b`.
This meaning is **not** inherited by a pipeline arrow,
e.g. source → physical state → quotient → observation.


## 2026-11-09 — current-head integration and exact remaining lemmas

Source audit: PR #1471 head observed at `d9f5dd931517a86542b498648e41cb6aea9094cf` before this continuation; PR #1454 at `fdad652d4c9409106d37384cc2bc06112ea60936`. These are **separate draft branches**. This continuation adds `twoNativeCubicalBondTransfersConserveTotal` on PR #1471: a genuine two-step shared-inventory proof using original `Grid.PositiveBond` and the semantic `Cube.Ternary27Point` geometry. This is source-written only: no Agda kernel receipt was obtained in this session.

### Exact maximum-cut register (proposed targets unless an owner is cited)

| Gate | Already source-written / executable | Exact remaining obligation and exit condition |
| --- | --- | --- |
| G0 kernel | Original 3×3×3 field, 54 native bonds, cubical/pants seams, open boundary ledger, selected finite reaction fixtures; two-step shared-state transfer | Run exact-head Agda 2.9 / `parallel_checker` against Golden roots and all transitive imports; archive stdout/stderr and SHA |
| G1 local continuity | `Biological369CubicalOpenSignedChargeExact` establishes **global** open signed charge balance; `check_biological_369_local_charge_continuity.py` tests finite voxelwise cases | `original369LocalSignedContinuityExact`: for every original voxel, integer charge difference + signed incidence-current divergence equals explicit face source/sink, including all native directed histories; verify in Agda |
| G2 original chemistry | `BH4SpatialOriginalQDPRStoichiometryExact` selected five-species QDPR; `check_bh4_original_panel_spatial_events.py` consumes the **original** source certificate when mounted | `original29x12SpatialReactionBalance`: all source-certified 29 species × 12 finite reactions, three nonfinite residuals, and 29 exchange coordinates on **one** 3×3×3 shared inventory, preserving elemental and charge ledgers; no fabricated zero fluxes |
| G3 physical step | Finite nonnegative reaction/transport events and face exchange available | `sameSourcePhysicalReactionTransportStep`: compose source-specific rates, admissible compartments, membrane/vascular permissions, ionic transport, reaction stoichiometry and actual environmental sources into one well-defined evolution |
| G4 same-source refinement | `BiologicalSourcePhysicalTissueSimulationExact` gives all-history consequences **conditional** on one-step premises | `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, `physicalTissueOneStepRefinement`; if old Boolean tissue rule fails, refine observation rather than assert false commutation |
| G5 future sufficiency | Selected 18-class stochastic quotient and BH4 three-state minimal example | `physicalKernelLumpsUnderInterventions` and `physicalFutureQuotientIsMinimal` for actual admissible interventions, transition kernel and observation language |
| G6 evidence | Source-aware BH4 measurement intake and finite diagnostics | `sourceCalibratedParametersAdmissible` and `heldoutFuturePredictionsDiscriminate`: same-sample compartment/time calibration, model uncertainty, alternatives, independent prospective test |
| G7 integration | Separate Golden roots and source provenance | Reconcile stacked #1159/#1226/#1454 with #1471; source-review ITIR #72 without auto-PNF promotion; combined Golden exact-head acceptance |

### Proof dependency and phased deliverables

- **D0 (acceptance):** exact-head checker receipts for both independent roots, then a reconciled joint root. A source-written declaration is never labelled kernel accepted without its receipt.
- **D1 (shared chemistry):** G1 + G2. Reuse original incidence and molecular matrix owners, without replacing the real 3D cube by a semantic 27-vector.
- **D2 (physical evolution):** G3 with explicit admissibility, time, boundary currents, permeability and energy assumptions.
- **D3 (physical-to-observed):** G4 commutation and consequent history transport, or a recorded physical counterexample.
- **D4 (future quotient):** G5 exact lumpability/refinement and minimality relative to the declared interventions.
- **D5 (science):** G6 measured original kinetics and held-out, uncertainty-bounded longitudinal comparison.
- **D6 (governance):** G7 lineage and independently reviewed evidence.

**No closure claimed** for Agda acceptance, entire 29×12 source certificate execution, calibrated physiological flux, full PNP evolution, real phenotype prediction, causal Kitzerow hypothesis, or branch reconciliation. Local charge continuity currently has a Python regression, **not** an Agda proof.


### 2026-11-09 continuation — substantive P0 local components, exact residual

**Source-written Agda work (no kernel receipt yet):**
- `BiologicalSharedFiniteVectorTransferExact.lookupAfterDebit`: indexed voxel post-debit + actual (0/1) local outflow = original amount; and `lookupAfterCredit`: indexed target gains one.
- `BiologicalOriginal54BondSharedVectorExact.originalBondLocalSourceDebitIsPaid` and `originalBondLocalTargetCreditIsPaid`: specialize those results to actual original nearest-neighbour bond endpoints in ternary 3×3×3 geometry.
- `Biological369CubicalBoundaryMaterialExact.lookupAfterFaceInjection` and `originalBoundaryInjectionLocalReceipt`: exactly account at the exterior voxel, using `OnFace`-qualified original events.
- Existing `originalFullSpatialOpenSignedChargeBalance` still supplies **global** signed open charge; the Python regression still checks **voxelwise** charge continuity.

**Do not prematurely close `original369LocalSignedContinuityExact`.** It still needs a single Agda source for per-voxel integer signed currents combining *executed* cation/anion native-bond histories, boundary withdrawals and injections, a signed incidence divergence, and the all-27-voxel step/history induction. The pointwise local source/target/face lemmas above remove its lowest-level arithmetic obligations only. G1 remains PARTIAL.

**Other progress on companion #1454:** `check_bh4_original_panel_spatial_events.py` now composes each certified original finite reaction event with an actual original native-bond transport and its reverse on the **same** 3×3×3×species inventory, checking nonnegative molecular amounts and conserved CHNOP/charge. The full 29×12 execution remains gated on mounted source certificate and does not claim any of the 29 physiological external fluxes. G2 remains PARTIAL.

**Updated immediate proof order:** local all-voxel charge-current ledger → source-certificate 29×12 same-state histories with explicitly separately tracked environmental exchanges → admissible physical step → PNP/BH4/tissue commutation → intervention-safe stochastic quotient → independent measurements. No rate or clinical causal claim arises from this structural conservation work.
