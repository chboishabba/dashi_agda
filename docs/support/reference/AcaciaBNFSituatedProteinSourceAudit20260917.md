# Acacia BNF Situated-Protein Source / Authority Audit

Date: 2026-09-17
Branch: `agent/acacia-bnf-situated-protein-design`

## Attribution rule

This tranche follows the repository attribution firewall:

`external source proposition != source identity metadata != DASHI typed reconstruction != DASHI synthetic collision != cross-source synthesis != deployment authority`.

Every scientific production owner attaches DOI metadata directly to an Agda source fixture through `DASHI.Core.AttributedSourceCore.mkDOISource`. PMID/PMCID/PDB coordinates are retained when independently verified; unresolved identifiers remain explicitly unresolved/not recorded rather than guessed.

## Acacia / Senegalia sources retained

- Fall et al. 2008 — DOI `10.1111/j.1472-765X.2008.02389.x`; PMID `18565139` — root-nodulating bacterial diversity and stress-tolerance phenotypes.
- Fall et al. 2016 — DOI `10.3389/fpls.2016.01355`; PMID `27656192`; PMCID `PMC5013129` — mature-tree inoculation, soil microbial/mineral-N coordinates, gum production.
- Faye et al. 2006 — DOI `10.1080/15324980500369475` — mature-tree inoculation / gum production; not a direct fixation-rate source.
- Herrmann et al. 2012 — DOI `10.1016/j.agee.2011.12.014` — season/site/rhizosphere-community and soil-inorganic-N context.
- Bakhoum et al. 2015 — DOI `10.1007/s00248-014-0507-1`; PMID `25315832` — Acacia-specific `nodA`, `nodC`, `nifH`, nodulation, biomass, ARA/SARA efficiency tests.
- Nowak et al. 2004 — DOI `10.1016/j.carres.2004.02.013`; PMID `15063192` — LCO/Nod-factor structural characterization in Acacia-nodulating rhizobia.
- Rasanen & Lindstrom 1999 — DOI `10.1111/j.1574-6941.1999.tb00561.x` — temperature-context dependence of infection/nodulation and reversibility.
- Isaac et al. 2011 — DOI `10.1016/j.foreco.2010.11.011` — age/P-indexed natural-population N2-fixation contribution and soil-N context.
- Isaac, Harmand & Drevon 2011 — DOI `10.1016/j.jplph.2010.10.011`; PMID `21211863` — non-limiting-N phosphorus experiment separating growth/mineral-N uptake from atmospheric-N contribution.
- Githae et al. 2013 — DOI `10.1080/15324982.2013.784377` — variety/site-indexed foliar `15N` fixation estimates with nodule observations kept separate.
- Raddad et al. 2005 — DOI `10.1007/s11104-005-2152-4` — eight-provenance, age-indexed foliar `15N`/Ndfa evidence in Blue Nile Sudan.
- Abaker et al. 2018 — DOI `10.7717/peerj.5232`; PMID `30018862`; PMCID `PMC6044267` — soil nutrient/SOC and foliar isotope evidence; source interpretation does not support important BNF contribution to plantation soil N in that Sudan system.
- Isaac, Hinsinger & Harmand 2012 — DOI `10.1016/j.scitotenv.2011.12.071`; PMID `22446108` — controlled Acacia-to-wheat below-ground N-transfer evidence indexed by phosphorus, root-contact regime and observation time.
- Raddad et al. 2006 — DOI `10.1007/s10457-006-9009-6` — four-year Blue Nile treatment nutrient budgets; reported N balance varies by system and omits below-ground tree biomass.
- Deans et al. 1999 — DOI `10.1016/S0378-1127(99)00063-8` — 3–18 year Senegal fallow nutrient accumulation with biomass/fodder export retained as a nutrient-budget coordinate.
- Fall et al. 2012 — DOI `10.1016/j.jenvman.2011.03.038`; PMID `21514716` — mineral-N/microbial observations indexed by distance from tree, soil depth and season.
- El Tahir et al. 2009 — DOI `10.1016/j.jaridenv.2008.11.007` — post-conversion North Kordofan nutrient-stock evidence retaining prior plantation state, conversion regime and subsequent cropping history.
- Basga et al. 2018 — DOI `10.5897/AJAR2018.13283` — North Cameroon post-fallow sorghum/cowpea yield evidence; all replicated crop treatments received a 4 g NPK 20-10-10 microdose per planting hole, so the result is explicitly not an avoided-mineral-N receipt.
- Raddad & Luukkanen 2007 — DOI `10.1016/j.agwat.2006.06.001` — Blue Nile clay-soil water/crop response; early-stage little-water-competition and crop-yield result remains soil/age/crop/management bounded.
- Gaafar et al. 2006 — DOI `10.1007/s10457-005-2918-y` — North Kordofan sandy-soil tree-density/water/gum/crop source providing a contrasting water-competition context.
- Raddad & Luukkanen 2006 — DOI `10.1016/j.foreco.2006.01.036` — eight-provenance delta-13C/water-use/growth/gum source; no cross-paper Ndfa correlation is inferred from provenance labels.

## Measurement-method donor retained

- Pate, Unkovich, Armstrong & Sanford 1994 — DOI `10.1071/AR9940133` — reference-plant selection for `15N` natural-abundance assessment of fixation. This is imported only as observer/method calibration. It is not Acacia evidence and supplies no biological mechanism or field-effect proposition for the Acacia lane.

## Nitrogenase / protein sources retained

- Seefeldt, Hoffman & Dean 2009 — DOI `10.1146/annurev.biochem.78.070907.103812`; PMID `19489731`; PMCID `PMC2814439` — limiting Mo-nitrogenase chemistry/mechanism calibration.
- Warmack & Rees 2024 — DOI `10.1038/s41467-024-54713-0`; PMCID `PMC11612016` — multiple structural states under alkaline/acetylene turnover.
- Narehood et al. 2025 — DOI `10.1038/s41586-024-08311-1`; PMID `39779844`; PMCID `PMC11812610` — FeSII-mediated oxygen-stress conformational protection in `Azotobacter vinelandii`.
- Paya Tormo et al. 2025/2026 — DOI `10.1038/s41589-025-02070-4`; PMID `41238839`; PDB `9I0F`, `9I0G`, `9I0H` — NifEN cofactor-maturation dynamics.
- Tsitsikli et al. 2025 — DOI `10.1038/s41586-025-09696-3`; PMID `41193803` — residue-level receptor signalling specificity in Lotus/barley experiments.

## Existing owners reused

- `ProteinSituatedHyperfabricExact`
- `NitrogenaseChemistryCrossPollinationExact`
- `BNFQualifiedInterventionModelExact`
- `AcaciaSenegalDrylandWaterCarbonExact`
- `AcaciaSenegalDrylandTaskFactorisationExact`

No replacement generic protein, BNF, attribution, factorisation, hydrology or LES ontology is introduced.

## Promotion firewalls checked

The source-written tranche explicitly blocks:

- nodule presence => active nitrogenase;
- `nifH` identity => fixation rate;
- nitrogenase identity => realised functional state;
- balanced stoichiometry => in-vivo fixed-N flux;
- fixed-N flux => plant assimilation;
- plant assimilation => ecosystem soil-N outcome;
- plant fixed-N contribution => interplant N transfer;
- interplant N transfer => positive field N balance;
- above-ground nutrient budget => whole-system nutrient balance;
- positive field N balance => fertilizer substitution;
- co-fertilized crop yield => avoided mineral N;
- fertilizer substitution => restoration/deployment authority;
- soil mineral-N observation => context-free scalar outcome independent of distance/depth/season;
- prior plantation nutrient accumulation => persistent nutrient stock following land-use conversion;
- present land-cover label => sufficient history for a nutrient-stock consumer;
- species/tree density => universal water-competition or crop-yield response across soil contexts;
- early-stage no-yield-penalty result => mature-system no-yield-penalty result;
- crop yield alone => identified water-competition mechanism;
- shared provenance labels across papers => Ndfa/WUE/gum correlation;
- shared provenance labels/site description => same empirical object without an explicit join receipt;
- Lotus/barley receptor result => Acacia same-object mechanism;
- Azotobacter FeSII protection => Acacia nodule protection mechanism;
- Abaker/Berninger/Starr 2018 dryland hydrology DOI `10.1016/j.jaridenv.2017.12.004` => BNF measurement;
- Acacia species identity => one fixed-N contribution across provenance/site/age;
- a provenance label without age/time context => a realised Ndfa/fixed-N contribution;
- raw plant `delta-15N` => Ndfa without the reference/baseline observer context;
- reference-plant/method calibration donor => Acacia biological evidence;
- foliar `15N`/Ndfa estimate => direct molecular nitrogenase flux or whole-season ecosystem N balance.

The generic nitrogenase dependency ladder is not mutated by these acquisitions. In particular, field budget and crop-yield evidence do not close generic `seasonalCropNDemand` or `avoidedMineralN`.

## Current acquisition frontier

A targeted public-literature search did not identify an Acacia/Senegalia same-object field study with an explicit mineral-N counterfactual adequate to close generic `avoidedMineralN`. Basga et al. 2018 is retained specifically as a negative-control receipt because mineral fertilizer was co-applied to every replicated crop treatment. Short-duration seedling N-fertilizer experiments are not promoted to crop-season fertilizer substitution. The Elicit academic-corpus connector was also unavailable because the connected account lacks API access; this is recorded as a search-coverage limitation, not evidence of source absence.

## Certification status

- source-written: yes
- source-order RED receipts: yes for the original four production paths plus focused regression-before-production extensions in the later source-acquisition tranche
- CI queried: no
- Agda/kernel receipt: unobserved in this connector-only session

No build/pass/certified claim is made.
