# Queensland nitrogen carryover / transport source addendum

Date: 2026-09-17
Branch: `agent/acacia-bnf-situated-protein-design`

This addendum records the later Queensland acquisition tranche that extends the original Acacia BNF source ledger. It preserves the repository attribution firewall:

`external source proposition != source identity metadata != DASHI typed reconstruction != DASHI cross-source comparison != same-object evidence != deployment authority`.

## Queensland ley BNF -> soil N -> following crop

Owner: `DASHI/Biology/Agriculture/QueenslandLeyBNFCarryoverExact.agda`

- Hossain et al. 1995 — DOI `10.1071/AR9950493` — enriched-15N / natural-abundance estimates of legume fixation at Warra.
- Hossain et al. 1996 I — DOI `10.1071/SR9960273` — soil N/C accretion and potentially mineralisable N.
- Hossain et al. 1996 II — DOI `10.1071/SR9960289` — mineral N availability, following-wheat N uptake/yield/protein.
- Pu et al. 2001 — DOI `10.1023/A:1014462305825` — denitrification, leaching and immobilisation in Queensland pasture systems.
- Bell et al. 2017 — DOI `10.1071/CP16248` — multi-site southern-Queensland ley fixation, mineral-N and following-cereal response.
- Strong et al. 2006 — DOI `10.1071/EA05007` — single-rate fertiliser comparator plus water-limited following-crop assays.
- Dalal et al. 2004 — DOI `10.1071/EA03166` — lucerne-ley duration jointly changes soil-N restoration and soil-water deficit/recharge.

Typed separation:

`N fixed != N accumulated != N mineralised at sowing != crop N uptake != yield response != avoided mineral N`.

A single observed yield equivalence to one fertiliser rate is not an identified fertiliser-replacement value. An explicit mineral-N counterfactual/response design remains required. Water state, rainfall-driven losses, shoot export, initial mineral N, crop identity and season remain indexed.

## Queensland woody-legume <-> grass <-> grazing N transport

Owner: `DASHI/Biology/Agriculture/QueenslandWoodyLegumeGrassNitrogenCyclingExact.agda`

- Burle, Shelton & Dalzell 2003 — Tropical Grasslands 37:119-128; no DOI recorded by this atlas — south-east Queensland Leucaena/signal-grass/soil/cattle/faeces/urine N-pool accounting.
- Radrizzani et al. 2011 — DOI `10.1071/CP10115` — paired Queensland soil organic C / total-N stock observations.
- Conrad et al. 2018 — DOI `10.1016/j.geoderma.2017.10.029` — natural-abundance isotope attribution and soil-N turnover.
- Radrizzani, Shelton & Dalzell 2010 — DOI `10.1071/AN10062` — P/S and companion-grass environmental constraints on Leucaena response/fixation.
- Catchpoole & Blair 1990 II — DOI `10.1071/AR9900531` — controlled split-root labelled transfer; retained as an external mechanism/method donor, not Queensland same-object evidence.
- Catchpoole & Blair 1990 III — DOI `10.1071/AR9900539` — labelled leaf/faeces/urine release and placement; retained as an external route/placement donor.
- Vallis 1983 — DOI `10.1071/AR9830367` — south-eastern Queensland field application of 15N-labelled Siratro/Greenleaf-desmodium residues to Rhodes grass, with labelled-N recovery followed in grass and soil.

Typed transport separation:

`living symbiotic N input != residue-mediated transfer != excreta-mediated transfer != direct below-ground transfer`.

and

`N fixed != N consumed != N excreted/recycled != N soil stock != companion-grass capture`.

The Vallis receipt pays a Queensland **field residue-transfer route** only. It does not pay contemporaneous living-root transfer. Controlled transfer does not imply detectable field transfer, and long-term soil total N does not identify a transfer pathway.

## Queensland Desmanthus <-> Rhizobium <-> grass / soil-N interaction

Owner: `DASHI/Biology/Agriculture/QueenslandDesmanthusGrassBNFInteractionExact.agda`

- Date 1991 — Tropical Grasslands 25:47-55; no DOI recorded by this atlas — accession x Rhizobium-strain x acidic/alkaline-soil effectiveness.
- Bahnisch, Date, Brandon & Pittaway 1998 I — Tropical Grasslands 32:13-19; no DOI recorded by this atlas — eight-Queensland-soil pot study separating inoculation from realised inoculant occupancy and indigenous-rhizobial competition.
- Brandon, Date, Clem, Robertson & Graham 1998 II — Tropical Grasslands 32:20-27; no DOI recorded by this atlas — three-year four-site south-east Queensland field trial with serological occupancy and natural-abundance Ndfa estimates.

Typed separation:

`successful inoculation != high inoculant occupancy != high Ndfa`.

The companion-grass interaction has no context-free sign. Grass may compete for water/nutrients while also drawing down mineral N that otherwise suppresses fixation. Soil fertility, indigenous rhizobia, drought/nodule turnover, life stage and site remain indexed.

## Hyperfabric payment

`DrylandPioneerLegumeGrasslandRegenerationHyperfabricExact` now retains these three Queensland systems as separate comparator objects and adds the following boundaries:

- fixed N does not identify one downstream N-transfer/carryover route;
- residue-mediated field transfer does not imply living-root transfer;
- grass competition has no context-free positive or negative sign;
- N-service optimisation cannot erase soil-water state;
- Queensland agricultural/pasture comparators do not create Acacia/Senegalia same-object evidence;
- quantified fertiliser replacement retains an explicit mineral-N counterfactual requirement.

The canonical Acacia/Senegalia ladder remains unchanged: reaction enablement, bacterial fixed-N flux, generic plant assimilation, seasonal demand and avoided mineral N are not closed by these comparator studies.

## Certification boundary

This addendum records source-written implementation only. No CI query or Agda/kernel typecheck is claimed in this connector-only continuation.