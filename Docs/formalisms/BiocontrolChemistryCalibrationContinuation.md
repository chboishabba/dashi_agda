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

not:

```text
number in mg/L -> universal ecological label
```

An uncertainty-band result may remain explicitly unresolved.

## Active discriminator search

`BiocontrolChemistryActiveDiscriminatorExact` reuses the generic consumer-collision / experiment-bundle / fibre-refinement machinery. In the finite synthetic witness, equal bulk nutrient mass does not determine nitrogen species; the selected species assay separates that declared collision and refines the live chemistry fibre. A pH probe remains an independent coordinate and is explicitly not substituted for species identity.

The finite nitrate/ammonium witness is DASHI mathematics. It is not asserted as a Springfield Lakes field observation.

## Consumer-indexed Pareto selection

`BiocontrolChemistryObserverParetoExact` adds the missing ranking layer after counterexample-driven repair. The finite observer family is:

```text
bulkOnly
  -> speciesSensitive
  -> contextualChemistry
  -> multiCoordinatePanel
```

The ranking is consumer-indexed. For the chemical-species/fraction consumer, `bulkOnly` is excluded by the existing equal-bulk-mass/different-species collision before ranking, and `speciesSensitive` is the minimum eligible observer. For contextual ecological classification, `speciesSensitive` is itself inadequate because site/season/window/protocol/uncertainty context is erased; the local repair promotes `contextualChemistry`, which is then the minimum eligible observer for that consumer.

Thus the selection rule is:

```text
live consumer collision
  -> counterexample
  -> local refinement
  -> repaired eligibility
  -> admissible/adequate stratum
  -> MDL/Pareto ranking
  -> selected observer
```

not `pick the cheapest observer globally`, and not `retain every available coordinate by default`.

The three Pareto axes are repository-local synthetic design coordinates: observer/assay complexity, contextual-information burden, and retained-coordinate count. They are not dollars, measured field effort, probability, ecological value, scientific truth, ethics, or deployment authority. In this finite fixture the selected model is componentwise no more costly than every other eligible model on the declared axes, while cheaper but consumer-inadequate models never enter the Pareto comparison.

The richer `multiCoordinatePanel` therefore remains available without receiving automatic preference. `more dimensions -> better` is explicitly blocked.

The first source implementation of this owner is commit `e472798201a360c42670e6218f7911cbef9cabe8`, timestamped `2026-09-15T04:57:05Z` / `2026-09-15T14:57:05+10:00`, and is recorded as `sourceCommittedOnly`; this chronology does not imply Agda typecheck or kernel certification.

## Pareto-selected assay scheduling

`BiocontrolChemistryParetoExperimentSchedulerExact` now welds observer selection back into experiment acquisition rather than leaving the two layers adjacent.

The ordering is fail-closed:

```text
consumer collision
  -> eligible observer family
  -> consumer-indexed Pareto observer
  -> declared bundle family for that observer
  -> minimum collision-separating bundle
  -> realised observation fibre
```

For the species/fraction consumer, the selected `speciesSensitive` observer schedules the species-sensitive assay already known to separate the equal-bulk/different-species collision. A richer species-plus-pH panel remains declared, but the species-only assay has lower repository-local bundle cost and already separates the live collision, so the richer panel is not automatically reacquired.

For the contextual-classification consumer, a second synthetic finite fixture holds the chemistry state fixed while changing a retained context-classification key. The already retained species state therefore remains insufficient for that consumer. The selected `contextualChemistry` observer schedules the missing context bundle, while a richer chemistry-plus-context panel remains available but is not automatically preferred. The context fixture is explicitly DASHI synthesis and is not asserted as a Springfield Lakes field observation.

This produces the end-to-end rule:

```text
Q
  -> minimal eligible / Pareto observer
  -> minimum declared separating assay bundle
  -> realised observation fibre
```

rather than either of the invalid shortcuts:

```text
cheapest assay globally -> answer
```

or

```text
richest panel available -> answer
```

Bundle costs remain repository-local search/design ranks. They are not empirical acquisition costs, money, ecological value, scientific truth, probability, ethics, or deployment authority. Selecting a bundle does not create a measurement: the actual assay/sensor/site/time/protocol/calibration/provenance obligations remain separately unpaid until a source or runtime acquisition pays them.

The scheduler regression landed first at `65ea58a031cac445793df81efe4b9cbf492f38fd`; exact lookup of the future production path then returned 404; the owner landed at `deb98096245b319b9c0e467f393d0c065fb1b6fb`, timestamped `2026-09-15T05:05:41Z` / `2026-09-15T15:05:41+10:00`, and is recorded as `sourceCommittedOnly`.

## Springfield Lakes intervention geometry

`SpringfieldLakesInterventionGeometryExact` uses only the two source-bound operational roles already recorded from Ipswich City Council: spider excavator at the hard-access Viewpoint Drive pond and aquatic weed harvester at the Vistula Circuit pond. On that finite carrier, treatment type alone does not determine equipment choice, while treatment plus access geometry does.

This is not a universal equipment-optimisation theorem and does not transfer salvinia efficacy to water hyacinth.

The repository easter egg about the spider being "OVER 9000" is retained in the source owner with an explicit boundary that it creates no scientific evidence.

## Attribution firewall

Attribution remains role-specific and append-only across this and previous rounds:

- BIPM supplies SI dimension/unit/scale semantics only.
- External ecological, chemistry and government sources supply only the empirical, historical, mechanistic, operational or governance premises actually present in those sources.
- Ipswich City Council supplies the Springfield Lakes salvinia equipment/access record only.
- Existing DASHI actual-chemistry/369 owners supply repository-native structural contracts and non-promotion boundaries; importing those contracts does not transfer external authorship or empirical authority.
- Site sensors, assays and runtime acquisition own actual numeric observations only when separately acquired with site/time/sample/protocol provenance.
- Calibration or threshold sources own only the classification premises they actually justify; BIPM unit authority cannot be promoted into ecological threshold authority.
- DASHI owns the new finite counterexamples, synthetic worlds, local-refinement constructions, non-factorability statements, active discriminator adapters, contextual classification firewalls, finite observer family, synthetic cost axes, Pareto/MDL selections, minimal-discriminator proofs and scheduler weld.

Citation imports neither proof nor deployment authority. Cross-pollination transfers structure, not authorship, truth, empirical status, geographic applicability, mechanism, causal authority or operational authority. A synthetic repository witness must not be redescribed as a sourced field observation. A source-backed operational analogue must not be promoted across species, site, assay or consumer without a separate paid transfer receipt.

## Certification/status boundary

The Pareto regression surface was committed first at `248345e3a691b0a5a45ac1852ac52b8ca1e1acd0`; exact lookup of `BiocontrolChemistryObserverParetoExact.agda` then returned 404 before the production owner was added at `e472798201a360c42670e6218f7911cbef9cabe8`.

The scheduler regression surface was committed first at `65ea58a031cac445793df81efe4b9cbf492f38fd`; exact lookup of `BiocontrolChemistryParetoExperimentSchedulerExact.agda` then returned 404 before the production owner was added at `deb98096245b319b9c0e467f393d0c065fb1b6fb`.

The local checker and aggregate rollup enumerate the new owners and regressions, but no fresh Agda invocation or GitHub Actions receipt has been produced in this continuation. Source presence, RED/owner ordering, chronology and repository integration therefore remain distinct from typecheck/kernel status.
