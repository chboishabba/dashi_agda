# Biocontrol chemistry / calibration continuation

This successor tranche begins from merged PR #931 and keeps the same fail-closed attribution discipline. It does not run GitHub Actions and does not claim fresh Agda/kernel certification.

## Chemistry-indexed observation fibre

The coarse `nutrientResidualHigh/Low` surface is no longer treated as sufficient chemistry. `BiocontrolChemistryObservationFibreExact` retains bulk concentration together with separately payable analyte identity, species/fraction, pH, temperature, hydrology, assay method, uncertainty, sampling window, site identity and provenance.

The repository-native `LocalRefinementRepair` pattern is instantiated directly:

```text
bulk-only observer
  -> consumer counterexample
  -> analyte/species/context refinement
  -> repaired admissibility
  -> repaired consumer adequacy
  -> eligible refined observer
```

The repair stays inside a declared aquatic-chemistry observer neighbourhood. It does not invent a measurement or claim a complete chemical mechanism.

## Calibrated ecological classification

`BiocontrolCalibratedEcologicalClassificationExact` separates physical/chemical observation from ecological classification. A context-erased universal hard threshold is deliberately inadequate for the declared contextual consumer. The local repair retains site, waterbody, season, sampling window, biological context, protocol, threshold provenance, uncertainty handling and local validation.

The intended chain is therefore:

```text
SI semantics
  -> chemistry-indexed observation
  -> source/protocol/context-bound calibration
  -> categorical ecological state
  -> consumer-specific LES reasoning
```

not `number in mg/L -> universal ecological label`. An uncertainty-band result may remain explicitly unresolved.

## Active discriminator search

`BiocontrolChemistryActiveDiscriminatorExact` reuses the generic consumer-collision / experiment-bundle / fibre-refinement machinery. In the finite synthetic witness, equal bulk nutrient mass does not determine nitrogen species; the selected species assay separates that declared collision and refines the live chemistry fibre. A pH probe remains an independent coordinate and is explicitly not substituted for species identity.

The finite nitrate/ammonium witness is DASHI mathematics. It is not asserted as a Springfield Lakes field observation.

## Consumer-indexed Pareto selection

`BiocontrolChemistryObserverParetoExact` adds the missing ranking layer after counterexample-driven repair. The finite observer family is `bulkOnly -> speciesSensitive -> contextualChemistry -> multiCoordinatePanel`.

For the chemical-species/fraction consumer, `bulkOnly` is excluded by the existing equal-bulk-mass/different-species collision before ranking, and `speciesSensitive` is the minimum eligible observer. For contextual ecological classification, `speciesSensitive` is itself inadequate because site/season/window/protocol/uncertainty context is erased; the local repair promotes `contextualChemistry`, which is then the minimum eligible observer for that consumer.

The three Pareto axes are repository-local synthetic design coordinates: observer/assay complexity, contextual-information burden, and retained-coordinate count. They are not dollars, measured field effort, probability, ecological value, scientific truth, ethics, or deployment authority. The richer `multiCoordinatePanel` remains available without receiving automatic preference.

The first source implementation of this owner is commit `e472798201a360c42670e6218f7911cbef9cabe8`, timestamped `2026-09-15T04:57:05Z` / `2026-09-15T14:57:05+10:00`, and is recorded as `sourceCommittedOnly`.

## Pareto-selected assay scheduling

`BiocontrolChemistryParetoExperimentSchedulerExact` welds observer selection back into experiment acquisition:

```text
consumer collision
  -> eligible observer family
  -> consumer-indexed Pareto observer
  -> declared bundle family for that observer
  -> minimum collision-separating bundle
  -> realised observation fibre
```

For the species/fraction consumer, the selected `speciesSensitive` observer schedules the species-sensitive assay already known to separate the equal-bulk/different-species collision. A richer species-plus-pH panel remains declared but is not automatically reacquired. For contextual classification, a second synthetic finite fixture holds chemistry fixed while changing a retained context-classification key; the selected `contextualChemistry` observer therefore schedules the missing context bundle.

Bundle costs remain repository-local search/design ranks. They are not empirical acquisition costs, money, ecological value, scientific truth, probability, ethics, or deployment authority. Selecting a bundle does not create a measurement.

The scheduler regression landed first at `65ea58a031cac445793df81efe4b9cbf492f38fd`; exact lookup of the future production path then returned 404; the owner landed at `deb98096245b319b9c0e467f393d0c065fb1b6fb`, timestamped `2026-09-15T05:05:41Z` / `2026-09-15T15:05:41+10:00`, and is recorded as `sourceCommittedOnly`.

## Acquisition, source qualification, promotion, and selective reopening

`BiocontrolChemistryAcquisitionPromotionExact` inserts the evidence boundary that was still missing after Pareto scheduling. A selected experiment bundle now generates a targeted acquisition obligation rather than being silently reinterpreted as an observation.

The chain is:

```text
selected Pareto bundle
  -> targeted acquisition obligation
  -> same-object source/site/sample/time/protocol/uncertainty qualification
  -> empirical observation payment
  -> separately paid calibration/local validation
  -> calibrated classification
  -> exact dependency-closure reopening
```

The owner defines separate acquisition targets for the species/fraction assay and the contextual-classification record. Both begin as `notLocated` obligations through the repository-native `EvidenceAcquisitionSelectiveReopeningExact` machinery. No canonical `QualifiedObservation` is fabricated in the owner: promotion requires source identity, site identity, sample identity, sampling window, assay/sensor protocol, analyte/context identity, uncertainty, custody/transformation lineage, same-object identity, and a proof that the object is not merely a synthetic fixture.

A `QualifiedClassificationPromotion` additionally requires the existing calibrated-classification receipt to pay empirical observation, threshold calibration, uncertainty handling and local validation, while retaining `createsInterventionAuthority = false`.

Selective reopening reuses the repository-native `AffectedDependencyClosureExact`. The declared finite dependency graph is:

```text
qualified observation
  -> calibrated classification
  -> rebound consumer
```

with no declared edge to the Springfield equipment-selection lane. Thus an acquired observation can reopen the classification and the transitive rebound consumer, while unrelated consumers are not automatically reopened merely because a new record exists.

The regression surface was committed first at `2f0c94c84e5d760512412c56c6de99cd13632343`; exact lookup of `BiocontrolChemistryAcquisitionPromotionExact.agda` then returned 404 before the production owner was added at `3165ff61c335cf5c8a2c189aed8c4380b0886244`, timestamped `2026-09-15T05:46:49Z` / `2026-09-15T15:46:49+10:00`. The chronology receipt remains `sourceCommittedOnly`.

## Springfield Lakes intervention geometry

`SpringfieldLakesInterventionGeometryExact` uses only the two source-bound operational roles already recorded from Ipswich City Council: spider excavator at the hard-access Viewpoint Drive pond and aquatic weed harvester at the Vistula Circuit pond. On that finite carrier, treatment type alone does not determine equipment choice, while treatment plus access geometry does.

This is not a universal equipment-optimisation theorem and does not transfer salvinia efficacy to water hyacinth. The repository easter egg about the spider being "OVER 9000" remains explicitly non-evidentiary.

## Attribution firewall

Attribution remains role-specific and append-only across this and previous rounds:

- BIPM supplies SI dimension/unit/scale semantics only.
- External ecological, chemistry and government sources supply only the empirical, historical, mechanistic, operational or governance premises actually present in those sources.
- Ipswich City Council supplies the Springfield Lakes salvinia equipment/access record only.
- Existing DASHI actual-chemistry/369 owners supply repository-native structural contracts and non-promotion boundaries; importing those contracts does not transfer external authorship or empirical authority.
- Site sensors, assays, operator/laboratory records and runtime acquisition own actual numeric/context observations only when separately acquired with source/site/time/sample/protocol/uncertainty provenance and same-object identity.
- Calibration or threshold sources own only the classification premises they actually justify; BIPM unit authority cannot be promoted into ecological threshold authority.
- DASHI owns the finite counterexamples, synthetic worlds, local-refinement constructions, non-factorability statements, active discriminator adapters, contextual classification firewalls, finite observer family, synthetic cost axes, Pareto/MDL selections, minimal-discriminator proofs, acquisition obligations, dependency graph and selective-reopening theorems.

Citation imports neither proof nor deployment authority. Cross-pollination transfers structure, not authorship, truth, empirical status, geographic applicability, mechanism, causal authority or operational authority. A synthetic repository witness must not be redescribed as a sourced field observation. A source-backed operational analogue must not be promoted across species, site, assay or consumer without a separate paid transfer receipt.

## Certification/status boundary

The local checker and aggregate rollup enumerate the new owners and regressions, but no fresh Agda invocation or GitHub Actions receipt has been produced in this continuation. Source presence, RED/owner ordering, chronology and repository integration therefore remain distinct from typecheck/kernel status.
