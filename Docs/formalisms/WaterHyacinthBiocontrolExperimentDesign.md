# Water-hyacinth biocontrol externality experiment weld

This bounded tranche makes water-hyacinth control a concrete consumer of the existing LES -> experimental-coordinate -> active proof-search spine. It does not introduce a parallel planner and it does not promote empirical ecological claims into theorem status.

The finite formal core separates target suppression from dissolved-oxygen outcome, biomass fate, nutrient/seedbank residual, restoration trajectory, non-target evidence, and agent interaction. Four explicit consumer collisions are now retained:

1. equal target suppression but different oxygen outcome;
2. equal target suppression plus present oxygen but different restoration outcome;
3. equal present target suppression but different nutrient/seedbank rebound residual;
4. equal target suppression plus equal declared agent-count surface but different agent-interaction outcome.

Thus the concrete non-factorability obligations are not only oxygen/restoration but also rebound and interaction:

```text
Q_oxygen       does not factor through present target suppression
Q_restoration  does not factor through target suppression x present oxygen
Q_rebound      does not factor through present target suppression
Q_interaction  does not factor through target suppression x declared agent count
```

The experiment layer reuses `DASHI.Core.ExperimentalCoordinateDesignExact`: the valuable next coordinate is the one that separates the live consumer-relevant collision. The active-search layer reuses the existing consumer collision, discriminator bundle, realised fibre refinement, and affected-dependency closure machinery. All four externality classes now pass through the same generic search spine rather than an ecological special-case planner.

New externality observations selectively reopen their own outcome certificate and the downstream net-outcome certificate. Host-specificity remains outside the declared oxygen, rebound, restoration and agent-interaction reverse dependency closures.

## Costed search

`BiocontrolCostedExperimentChoiceExact` reuses the repository's `ActionabilityCostedExperimentChoiceExact` and `DiscriminatorSynthesisExact`. Four finite fixture bundles are compared: nutrient+seedbank, oxygen+biomass fate, community composition, and agent interaction. Their natural-number costs are **synthetic search/resource ranks only**. They are not dollars, empirical field costs, welfare weights, experimental ethics, probabilities, or deployment authority.

The key rule is consumer indexed: a globally cheaper measurement is irrelevant when it does not resolve the current consumer obstruction. Thus the fixture can have a nutrient probe cheaper than the oxygen probe while proving that the nutrient probe does not resolve the oxygen obstruction. Minimality is only among declared alternatives that actually resolve the named obstruction.

Each cheapest-choice receipt is now explicitly collision-backed: it carries the finite consumer collision, a separating experiment-bundle witness, and the corresponding `CheapestResolvingMove`. The scheduler therefore no longer operates only over abstract obstruction constructors.

## SI / metrology cross-pollination

`BiocontrolSIQuantityExact` reuses the canonical `DASHI.Physics.Units.SI` owner and the existing `LESEnvironmentSIQuantityBridgeExact`; it does not create a second environmental units ontology.

The physical probe semantics currently retained are:

- dissolved oxygen mass concentration: density dimension, field reading `mg L^-1`, with `1 mg L^-1 = 10^-3 kg m^-3`;
- nutrient mass concentration when the assay is declared on that basis: same density dimension and scale, while analyte/fraction/method remain source-specific;
- removed/retained biomass: mass dimension, gram-scale reading represented as `10^-3 kg`;
- hydrologic inflow/outflow: volumetric-flow dimension in `m^3 s^-1`;
- water temperature nuisance coordinate: thermodynamic-temperature dimension in kelvin.

The metrology boundary is intentionally strict:

```text
same SI dimension != same ecological quantity
unit semantics != acquired field measurement
categorical ecological state != SI physical quantity
BIPM authority over SI != ecological or deployment authority
```

The BIPM SI Brochure (9th edition, revision 4.01, 2026; DOI `10.59161/AUEZ1291`) is represented as a separate `AttributedSource` with its own snowball receipt. It is used only for SI dimensions, units and scale semantics. Numeric ecological observations still require site/time/sensor/assay-specific provenance.

## Attribution and source roles

The ecological source atlas uses `DASHI.Core.AttributedSourceCore` and `DASHI.Core.SnowballAttributionProvenanceInvariantExact`; source identity, source kind, formalisation relationship, visibility, proof non-import and authority non-creation therefore survive downstream snowballing.

The retained ecological source rows are deliberately non-interchangeable:

- CSIRO, *Water hyacinth*, canonical institutional page: Australian programme/agent context.
- Andrew Petroeschevsky (compiler) with Tobias Bickel, Darren Jennings, Stephen Johnson, Reece Luxton and Kay Bailey listed as information/guide revision contributors, *Weed Management Guide - Water Hyacinth*: Australian control mechanisms, Neochetina damage/sinking, decomposition/oxygen warning, seedbank, nutrient context, integrated control and Sandringham Lagoon restoration example. The supplied guide does not expose a publication year in the parsed source, so none is invented.
- Australian Government Department of Agriculture, Fisheries and Forestry, *Biological control agents*: current host-specificity/off-target risk-analysis governance context. It is not used as retroactive proof of safety for historic releases.
- C. J. DeLoach (1976), *Neochetina bruchi, a Biological Control Agent of Waterhyacinth: Host Specificity in Argentina*, Annals of the Entomological Society of America 69(4), 635-642, DOI `10.1093/aesa/69.4.635`: host-specificity calibration only.
- R. Ogutu-Ohwayo, J. S. Balirwa, T. Twongo, R. Mugidde and Odongkara (2002), *Impact of dead and sunken water hyacinth on biotic communities, the aquatic environment and socio-economic activities*, handle `1834/33023`: dead/sunken biomass and aquatic-environment context. Indexed records differ on Odongkara's initial, so the atlas preserves that ambiguity instead of fabricating a reconciliation.
- Ted D. Center et al. (2005), *Herbivory alters competitive interactions between two invasive aquatic plants*, Biological Control 33(2), 173-185, DOI `10.1016/j.biocontrol.2005.02.005`: competition/community-reassembly calibration.
- Desalegn Chala, Diress Tsegaye, Habtamu Alem et al. (2026), *Beyond Removal: Strategies for Sustainable Control of Water Hyacinth in Tropical Freshwater Ecosystems*, Environmental Management 76, article 187, DOI `10.1007/s00267-026-02494-1`: sustainable-control/nutrient-recycling synthesis.
- F. Mariani, E. G. Steen, B. G. Rector, P. D. Pratt and R. Diaz (2026), *Too hot, too tough, too crowded...*, Biological Control 216, 106023, DOI `10.1016/j.biocontrol.2026.106023`: agent-interaction and abiotic-context calibration in a southeastern-US setting; no geographic transfer to Australia is asserted.

These external ecological sources do **not** own the finite non-factorability witnesses, consumer-indexed residual/discriminator construction, selective certificate reopening, SI adapters, or costed experiment-search theorems. Those are repository-native DASHI extensions motivated or calibrated by source material. Conversely, DASHI's formalisation does not manufacture empirical measurements or retroactively strengthen the external sources.

## LES and status boundary

The LES scenario carries the canonical typed ecological source atlas rather than only a prose citation. Water-hyacinth control, restoration, host-specificity evidence, observed post-release safety, and net ecosystem benefit remain distinct coordinates. The canonical fixture records host-specificity support while leaving post-release safety and net ecosystem benefit unresolved; a citation neither imports proof nor creates deployment authority.

Repository first-implementation chronology is recorded independently from validation. The initial externality owner is tied to commit `38aaea92eb21cccc41ec38d03c3a55e5e1ab178e`; the costed-choice owner to `0cd907c423041bade3b5cfa4e5a7d5aeca4b6c45`; and the SI bridge owner to `d3144c596df0c6696ad7f908f69f8669f3ebe52b`. All are recorded as `sourceCommittedOnly`, not as type-check or kernel certification receipts.
