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


## 2026-11-09 synchronized cross-branch remaining maximum cut

PR #1454 and developmental PR #1471 are **not** one compiled physical state. The latter now includes a same-inventory two-native-bond conservation composition (`twoNativeCubicalBondTransfersConserveTotal`), genuine original 1→3 pants geometry, exterior face balances and finite voxelwise charge-continuity regression. **None of these establish the original physiological transport coefficients.**

| Gate | BH4 source state | Remaining lemma / source payment |
| --- | --- | --- |
| G0 | Five-species QDPR, 3D source/target spatial events, selected three-state future minimality | Exact-head Agda/parallel checker receipts and integration with developmental Golden |
| G1 | Original panel consumer `scripts/check_bh4_original_panel_spatial_events.py` reads existing Rhea/ChEBI acquired certificate; rejects fake zeros | `original29x12SpatialReactionBalance` using all 12 finite source columns, 3 nonfinite residuals and explicit 29 environmental exchange coordinates; run only with actual certificate |
| G2 | Finite shared-state transfers and source-qualified reactions | `sameSourcePhysicalReactionTransportStep` with measured rates, compartment/membrane permissions, turnover and signed currents |
| G3 | All-history conditional source bridge and QDPR redox ordering counterexample | `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, `physicalTissueOneStepRefinement` on same physical specimen/state/time |
| G4 | Selected chemical future-minimality counterexample | `physicalKernelLumpsUnderInterventions`, `physicalFutureQuotientIsMinimal` for physically admissible observations |
| G5 | Source-aware measurement intake | `sourceCalibratedParametersAdmissible`, `heldoutFuturePredictionsDiscriminate`; distinguish resource allocation, redox and independent regulation |
| G6 | Separate roadmap and governance owners | Stacked #1159/#1226/#1454 + #1471 reconciliation, source-review ITIR #72, exact-head acceptance |

**Deliverables:** D0 kernel and merged-tree receipt; D1 source-paid 29×12 and local continuity; D2 admissible reaction–transport–PNP dynamics; D3 tissue observation refinement; D4 future-safe minimal quotient; D5 calibrated held-out prediction; D6 governed evidence lineage.

**Integrity controls:** geometry is original ternary 3×3×3 with a 27-vector as chart; a pants interface is not a transport coefficient; BH2 and qDHB are not conflated; an exchange coordinate is not a measured flux; exact integer event checks are not longitudinal experiments; no clinical Kitzerow causal conclusion is certified. Both PRs remain draft until independent proofs and data pay the gates.


### 2026-11-09 P0 reaction/transport composition continuation

`scripts/check_bh4_original_panel_spatial_events.py` now constructs, **per genuine original finite Rhea column**, a chemically allowed starting inventory and executes original reaction → native nearest-neighbour product transfer → reverse nearest-neighbour transfer. It asserts return to the postreaction inventory, exact conservation of C/H/N/O/P and integer charge throughout the shared original 3×3×3 state, and absence of negative molecule counts. QDPR self-test expects one composed history; the strict 29×12 path still requires the actual original acquired certificate and three explicit nonfinite residuals.

This is a stronger executable chronology test than isolated reaction and bond fixtures but is **not** physiological kinetics, membrane permeability, 29 source-paid exchange fluxes, an Agda kernel theorem, or proof of same-specimen tissue dynamics.

PR #1471 now source-writes native-bond source debit/target credit and outer-face local injection identities in Agda; these are prerequisites, **not yet** the full 27-voxel signed charge-current continuity theorem. D1 remains PARTIAL; G1/G2 still OPEN for full physical completion.

**Next exact original-P0 cut:** `original369LocalSignedContinuityExact` followed by `original29x12SpatialReactionBalance`, then `sameSourcePhysicalReactionTransportStep`. Only then seek `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, and `physicalTissueOneStepRefinement` on one selected physical state.
