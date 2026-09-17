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
- Raddad et al. 2005 — DOI `10.1007/s11104-005-2152-4` — eight-provenance, age-indexed foliar `15N`/Ndfa evidence in Blue Nile Sudan; provenance and age remain explicit coordinates and the source's above-ground foliage fixed-N contribution is retained as plant-level evidence rather than direct molecular flux.
- Abaker et al. 2018 — DOI `10.7717/peerj.5232`; PMID `30018862`; PMCID `PMC6044267` — soil nutrient/SOC and foliar isotope evidence; source interpretation does not support important BNF contribution to plantation soil N in that Sudan system.
- Isaac, Hinsinger & Harmand 2012 — DOI `10.1016/j.scitotenv.2011.12.071`; PMID `22446108` — controlled Acacia-to-wheat below-ground N-transfer evidence indexed by phosphorus, root-contact regime and observation time.
- Raddad et al. 2006 — DOI `10.1007/s10457-006-9009-6` — four-year Blue Nile treatment nutrient budgets; reported N balance varies by system and omits below-ground tree biomass.
- Deans et al. 1999 — DOI `10.1016/S0378-1127(99)00063-8` — 3–18 year Senegal fallow nutrient accumulation with biomass/fodder export retained as a nutrient-budget coordinate.
- Fall et al. 2012 — DOI `10.1016/j.jenvman.2011.03.038`; PMID `21514716` — mineral-N/microbial observations indexed by distance from tree, soil depth and season.
- El Tahir et al. 2009 — DOI `10.1016/j.jaridenv.2008.11.007` — post-conversion North Kordofan nutrient-stock evidence retaining prior plantation state, conversion regime and subsequent cropping history.

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

No replacement generic protein, BNF, attribution, factorisation, or LES ontology is introduced.

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
- fertilizer substitution => restoration/deployment authority;
- soil mineral-N observation => context-free scalar outcome independent of distance/depth/season;
- prior plantation nutrient accumulation => persistent nutrient stock following land-use conversion;
- present land-cover label => sufficient history for a nutrient-stock consumer;
- Lotus/barley receptor result => Acacia same-object mechanism;
- Azotobacter FeSII protection => Acacia nodule protection mechanism;
- Abaker/Berninger/Starr 2018 dryland hydrology DOI `10.1016/j.jaridenv.2017.12.004` => BNF measurement;
- Acacia species identity => one fixed-N contribution across provenance/site/age;
- a provenance label without age/time context => a realised Ndfa/fixed-N contribution;
- raw plant `delta-15N` => Ndfa without the reference/baseline observer context;
- reference-plant/method calibration donor => Acacia biological evidence;
- foliar `15N`/Ndfa estimate => direct molecular nitrogenase flux or whole-season ecosystem N balance.

The generic nitrogenase dependency ladder is not mutated by these acquisitions. In particular, field budget evidence does not close generic `seasonalCropNDemand` or `avoidedMineralN`.

## Certification status

- source-written: yes
- source-order RED receipts: yes for the original four production paths plus focused regression-before-production extensions in the later source-acquisition tranche
- CI queried: no
- Agda/kernel receipt: unobserved in this connector-only session

No build/pass/certified claim is made.
