# Acacia BNF Situated-Protein LES Bridge Design

Date: 2026-09-17
Status: approved in-chat architecture; implementation pending written-spec review

## Goal

Extend the existing biological-nitrogen-fixation, situated-protein, and dryland-LES machinery without creating a second biology ontology.

The target composition is:

```text
Acacia/Senegalia senegal rhizobial source atlas
        -> situated nodulation / receptor-state bridge
        -> situated nitrogenase protein witness
        -> existing nitrogenase chemistry / BNF dependency ladder
        -> existing BNF consumer fibres
        -> merged Acacia dryland water-carbon LES surface
```

The bridge must preserve source ownership, same-object identity, observer/evidence role, and consumer-relative adequacy throughout.

## Existing authoritative owners

Implementation must import and reuse, not replace:

- `DASHI.Biology.Agriculture.HungriaBiologicalNitrogenFixationSourceAtlas`
- `DASHI.Biology.Agriculture.HungriaSoybeanBNFExact`
- `DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact`
- `DASHI.Biology.Agriculture.BNFQualifiedInterventionModelExact`
- `DASHI.Biology.Protein.ProteinSituatedHyperfabricExact`
- `DASHI.Environment.AcaciaSenegalDrylandWaterCarbonExact`
- `DASHI.Environment.AcaciaSenegalDrylandTaskFactorisationExact`
- the canonical attribution / external-identity / query-indexed projection machinery already imported by those owners.

The existing nitrogenase ladder remains the dependency spine:

```text
enzyme stoichiometry          paid
reaction enablement           open
bacterial fixed-N flux        open
plant assimilation            open
seasonal crop/plant N demand  open
avoided mineral N             open
```

This tranche may refine evidence for reaction enablement and bacterial fixed-N flux. It must not claim to close plant assimilation, seasonal plant N demand, avoided mineral N, ecosystem nitrogen balance, or restoration/deployment authority unless an exact source/consumer receipt is separately present.

## Source acquisition set

### Acacia / Senegalia symbiosis

1. Fall et al. (2008), `Phenotypic and genotypic characteristics of Acacia senegal (L.) Willd. root-nodulating bacteria isolated from soils in the dryland part of Senegal`, Letters in Applied Microbiology 47(2):85-97. DOI `10.1111/j.1472-765X.2008.02389.x`; PMID `18565139`.
   - Role: host-associated root-nodulating bacterial diversity and environmental stress tolerance.
   - Bounded reading: evidence for diverse A. senegal root-nodulating bacteria, including heat/drought/salinity tolerance phenotypes.
   - Exclusion: rhizobial identity or stress tolerance alone does not establish effective nitrogen-fixation flux in a given nodule/tree/site.

2. Fall et al. (2016), `Rhizobial Inoculation Increases Soil Microbial Functioning and Gum Arabic Production of 13-Year-Old Senegalia senegal (L.) Britton, Trees in the North Part of Senegal`, Frontiers in Plant Science 7:1355. DOI `10.3389/fpls.2016.01355`; PMID `27656192`.
   - Role: mature-tree field inoculation / soil-function / production evidence.
   - Bounded reading: source-bounded inoculation effects on measured soil microbial/mineral-N and gum-production outcomes in the studied trees/sites/seasons.
   - Exclusion: does not make inoculation universally beneficial, does not identify every effect as nitrogenase-mediated, and does not supply deployment authority elsewhere.

3. Faye et al. (2006), `Effect of inoculation with rhizobia on the gum-arabic production of 10-year-old Acacia senegal trees`, Arid Land Research and Management 20(1):79-85. DOI `10.1080/15324980500369475`.
   - Role: mature-tree inoculation / gum-yield evidence.
   - Exclusion: gum-yield response is not a direct nitrogen-fixation-rate measurement.

4. Herrmann et al. (2012), `Seasonal changes of bacterial communities in the rhizosphere of Acacia senegal mature trees inoculated with Ensifer strains in Burkina Faso and Niger`, Agriculture, Ecosystems & Environment 157:47-53. DOI `10.1016/j.agee.2011.12.014`.
   - Role: season/site/rhizosphere-community context.
   - Exclusion: bacterial-community change or inoculation identity does not by itself establish effective nodule fixation.

Additional source acquisition is allowed when it directly pays a named residual such as Acacia-specific nod/nif gene identity, Nod-factor chemistry, nodule oxygen regulation, or direct fixation-rate evidence. It must remain source-indexed rather than being absorbed into a generic Acacia claim.

### Nitrogenase / situated protein

5. Seefeldt, Hoffman & Dean (2009), `Mechanism of Mo-Dependent Nitrogenase`, Annual Review of Biochemistry 78:701-722. DOI `10.1146/annurev.biochem.78.070907.103812`; PMID `19489731`; PMCID `PMC2814439`.
   - Existing mechanistic calibration for limiting Mo-nitrogenase stoichiometry.

6. Warmack & Rees (2024), `Structural evolution of nitrogenase states under alkaline turnover`, Nature Communications 15:10472. DOI `10.1038/s41467-024-54713-0`.
   - Role: turnover-state structural multiplicity.
   - Exclusion: alkaline/acetylene cryo-EM states are not automatically in-vivo legume-nodule states.

7. Narehood et al. (2025), `Structural basis for the conformational protection of nitrogenase from O2`, Nature 637:991-997. DOI `10.1038/s41586-024-08311-1`; PMID `39779844`; PMCID `PMC11812610`.
   - Role: FeSII-mediated oxygen-stress conformational protection.
   - Exclusion: Azotobacter protection mechanism is a situated-protein donor; it must not be silently asserted as the exact Acacia symbiont mechanism.

8. Payá Tormo et al. (published 2025; issue 2026), `Dynamics driving the precursor in NifEN scaffold during nitrogenase FeMo-cofactor assembly`, Nature Chemical Biology 22:813-821. DOI `10.1038/s41589-025-02070-4`; PMID `41238839`; PDB structures include `9I0F`, `9I0G`, `9I0H`.
   - Role: cofactor-assembly structural dynamics / open-closed states / partial unfolding.
   - Exclusion: NifEN maturation-state evidence is not nitrogenase catalytic flux or plant-level BNF.

### Legume receptor / nodulation protein signalling

9. Tsitsikli et al. (2025), `Two residues reprogram immunity receptors for nitrogen-fixing symbiosis`, Nature 648:443-450. DOI `10.1038/s41586-025-09696-3`; PMID `41193803`.
   - Role: exact residue-level evidence that highly related receptor-kinase states can route signalling toward symbiosis versus immunity.
   - Exclusion: Lotus/barley receptor engineering does not establish Acacia receptor sequence, nodulation phenotype, or field fixation rate.

Other receptor/phosphorylation papers may be added only if they pay a specific signalling/nodulation coordinate rather than duplicating this residue-level donor.

## Architecture

### 1. `AcaciaSenegalRhizobialBNFSourceAtlasExact`

A source-only atlas for Acacia/Senegalia BNF-related evidence.

Minimum fields per source:

```text
authors
title
publication
year
DOI / PMID / PMCID where verified
source role
host taxon naming used by source
rhizobial/Ensifer identity if source-resolved
site / geography
experimental or observational role
measurement family
bounded reading
excluded promotion
source owner
```

Do not invent article QIDs. `Acacia senegal` / `Senegalia senegal` synonym handling must be explicit and must not collapse article identity, host-taxon naming convention, or same-object study identity.

### 2. `NitrogenaseSituatedProteinWitnessExact`

Instantiate the existing `ProteinSituatedHyperfabricExact` rather than defining a replacement protein state ontology.

Required situated coordinates include at least:

```text
nitrogenase component identity
cofactor/maturation state
environment / oxygen state
interaction-partner state
turnover / catalytic context
history / stress state
observer / structural method
source provenance
```

Primary finite DASHI collisions:

```text
CatalyticOrProtectedState
  not FactorsThrough
NitrogenaseProteinIdentity
```

and, reusing the existing BNF chemistry boundary,

```text
EffectiveFixedNFlux
  not FactorsThrough
BalancedNitrogenaseStoichiometry
```

The first collision may use source-bounded structural premises but the finite factorisation witness is DASHI synthesis. The second should bind directly to the existing `NitrogenaseChemistryCrossPollinationExact` no-promotion boundary rather than restating the chemistry.

### 3. `LegumeNodulationSituatedProteinBridgeExact`

Keep these coordinates distinct:

```text
Nod-factor / ligand identity
receptor protein identity
residue / motif state
phosphorylation / interaction state where source-paid
symbiotic-vs-immune signalling output
infection-thread / infection state
nodule state
nodule microenvironment
nitrogenase enablement state
```

Required firewalls:

```text
Nod-factor recognition != successful nodulation
successful nodulation != active nitrogenase
active nitrogenase != integrated fixed-N delivery to plant
receptor identity != signalling output
shared receptor family != same mechanism in Acacia
```

The Tsitsikli et al. residue result is a transferable structural donor for consumer-relative protein-state sufficiency. It does not transfer Lotus biology into Acacia.

### 4. `AcaciaSenegalBNFLESCrossPollinationExact`

Join the source atlas and protein/nodulation witnesses to the existing merged Acacia water-carbon LES surface and BNF consumer fibre.

Do not edit #980 semantics to pretend the 2018 Sudan hydrology paper measured BNF. Instead create a provenance-retaining joined observer with independent coordinates for:

```text
SOC
hydraulic capacity
realised soil moisture
runoff
infiltration
ET
drainage
rainfall/site/age
rhizobial partner / inoculation context
nodulation state
nitrogenase situated state
fixed-N evidence
soil/mineral-N evidence
measurement/model/source role
```

Required finite DASHI non-factorability targets:

```text
SoilNOutcome not FactorsThrough TreeIdentity
SoilNOutcome not FactorsThrough NodulePresence
FixedNFlux not FactorsThrough RhizobialIdentity
RestorationDecision not FactorsThrough FixedNMetric
```

Only create a collision when the fixture can state clearly which coordinates are source premises and which differing worlds are DASHI synthetic witnesses.

## Bidirectional cross-pollination rule

The bridge is intentionally reciprocal but non-fusing:

```text
protein / molecular state -> constrains admissible BNF mechanism
BNF / nodule environment -> constrains admissible protein state
LES water / carbon state -> constrains ecological context for nodulation / fixation
BNF / soil-N state -> adds a new LES state coordinate
```

None of these arrows means semantic identity or automatic causal sufficiency.

In particular:

```text
PAWC != realised soil water
nodulation capacity != realised nitrogen fixation
nitrogenase presence != realised fixed-N flux
fixed-N flux != plant assimilation
plant assimilation != ecosystem soil-N outcome
soil-N outcome != restoration/deployment authority
```

## Source and authority firewall

Every new module must keep these layers explicit:

```text
external source proposition
!= source identity metadata
!= DASHI typed reconstruction
!= DASHI synthetic finite collision
!= cross-source synthesis
!= empirical validation in another system
!= deployment / restoration authority
```

DOI, PMID, PMCID, PDB, UniProt, taxon IDs, and QIDs remain identity/provenance coordinates only.

A source from soybean, Lotus, barley, Azotobacter or another organism may donate mechanism-shaped evidence only at the exact abstraction it supports. It cannot silently become an Acacia-specific empirical proposition.

## Testing / regression design

No CI work is requested.

Implementation should use RED-first source-level regression files before each production owner, following current repository practice. The regression surface should pin at minimum:

- verified stable source identifiers;
- Acacia/Senegalia host-name synonym separation;
- source-role and organism-role boundaries;
- nitrogenase situated-protein collision;
- nodulation/signalling no-collapse firewalls;
- explicit reuse of existing nitrogenase chemistry and BNF consumer owners;
- explicit reuse of #980 dryland LES owner;
- no automatic promotion from fixed-N evidence to plant assimilation, soil-N outcome, restoration success or deployment authority.

No Agda/kernel GREEN is to be claimed unless an exact-head execution receipt is actually observed. The user has explicitly asked not to pursue CI for this tranche.

## Integration location

Expected production owners:

```text
DASHI/Biology/Agriculture/AcaciaSenegalRhizobialBNFSourceAtlasExact.agda
DASHI/Biology/Protein/NitrogenaseSituatedProteinWitnessExact.agda
DASHI/Biology/Agriculture/LegumeNodulationSituatedProteinBridgeExact.agda
DASHI/Biology/Agriculture/AcaciaSenegalBNFLESCrossPollinationExact.agda
```

With focused regression owners alongside them and minimal rollup changes under `DASHI.Biology.Agriculture.Everything` and/or an existing protein validation root. Avoid widening global `DASHI/Everything` unless existing rollup policy requires it.

## Non-goals

This tranche will not:

- create a new generic protein ontology;
- create a new generic BNF ontology;
- claim that all legumes use the same rhizobial species, receptor state, oxygen-protection mechanism or fixation rate;
- turn root nodules into proof of active fixation;
- infer fixation rate from `nifH` presence alone;
- infer whole-tree/whole-field nitrogen balance from nitrogenase stoichiometry;
- attribute Acacia water-carbon observations from #980 to BNF unless a source directly supports that connection;
- infer fertilizer replacement, avoided emissions, economic benefit, ecosystem improvement or deployment permission from molecular BNF evidence alone.

## Implementation order after spec approval

1. RED regression for Acacia source atlas; implement atlas.
2. RED regression for nitrogenase situated-protein witness; implement witness over existing protein + nitrogenase chemistry owners.
3. RED regression for legume nodulation situated-protein bridge; implement receptor/signalling/nodule separations.
4. RED regression for Acacia BNF-LES bridge; implement joined observer and finite consumer collisions over merged #980 + existing BNF model.
5. Update focused rollups and source-attribution audit surfaces.
6. Source-level diff/self-review only; do not poll CI or claim kernel certification.
