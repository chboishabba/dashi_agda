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

not:

```text
pick the cheapest observer globally
```

and not:

```text
retain every available coordinate by default
```

The three Pareto axes are repository-local synthetic design coordinates: observer/assay complexity, contextual-information burden, and retained-coordinate count. They are not dollars, measured field effort, probability, ecological value, scientific truth, ethics, or deployment authority. In this finite fixture the selected model is componentwise no more costly than every other eligible model on the declared axes, while cheaper but consumer-inadequate models never enter the Pareto comparison.

The richer `multiCoordinatePanel` therefore remains available without receiving automatic preference. `more dimensions -> better` is explicitly blocked.

## Springfield Lakes intervention geometry

`SpringfieldLakesInterventionGeometryExact` uses only the two source-bound operational roles already recorded from Ipswich City Council: spider excavator at the hard-access Viewpoint Drive pond and aquatic weed harvester at the Vistula Circuit pond. On that finite carrier, treatment type alone does not determine equipment choice, while treatment plus access geometry does.

This is not a universal equipment-optimisation theorem and does not transfer salvinia efficacy to water hyacinth.

The repository easter egg about the spider being "OVER 9000" is retained in the source owner with an explicit boundary that it creates no scientific evidence.

## Attribution firewall

Attribution remains role-specific:

- BIPM supplies SI dimension/unit/scale semantics only.
- External ecological and government sources supply only their source-bounded empirical, historical, operational or governance claims.
- Ipswich City Council supplies the Springfield Lakes salvinia equipment/access record only.
- Existing DASHI actual-chemistry/369 owners supply repository-native structural contracts and non-promotion boundaries.
- DASHI owns the new finite counterexamples, local-refinement constructions, non-factorability statements, active discriminator adapters, contextual classification firewalls, finite observer family, synthetic cost axes and Pareto/MDL selections.

Citation imports neither proof nor deployment authority. Cross-pollination transfers structure, not authorship, empirical status, geographic applicability or causal authority.
