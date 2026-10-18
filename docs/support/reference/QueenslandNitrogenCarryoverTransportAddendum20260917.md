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
- Sierra & Nygren 2006 — DOI `10.1016/j.soilbio.2005.12.012` — Guadeloupe field silvopastoral design excluding above-ground litter/excreta recycling, with natural-abundance 15N, tree fine-root density and explicit reference-plant/isotope-baseline checks. Retained as an external field route-discrimination donor, not Australian same-object evidence.

Typed transport separation:

`living symbiotic N input != residue-mediated transfer != excreta-mediated transfer != direct below-ground transfer`.

and

`N fixed != N consumed != N excreted/recycled != N soil stock != companion-grass capture`.

The Vallis receipt pays a Queensland **field residue-transfer route** only. It does not pay contemporaneous living-root transfer. Sierra & Nygren show a stronger field design shape for isolating below-ground transfer, but in a Guadeloupe Gliricidia-Dichanthium system; the reference-plant/root-invasion problem and isotope baseline remain part of the measurement object. Controlled transfer does not imply detectable field transfer, and long-term soil total N does not identify a transfer pathway.

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

## Factorisation / experiment-design cross-pollination

Owner: `DASHI/Biology/Agriculture/DrylandRegenerationNitrogenFactorisationExact.agda`

The generic `IntersectionalNonFactorability` and Snowball discovery machinery is now applied to four ecology-specific coarse observers:

- fixed-N label -> transport route;
- released-N label -> demand-time crop capture;
- N-service label -> water-coupled outcome;
- carryover label -> quantified fertiliser replacement.

Each coarse observer has a finite non-factorability witness, and each corresponding enriched observer has a finite positive `FactorsThrough` repair. Failed factorisation generates a typed route/timing/water/mineral-N-response axis proposal. These finite worlds and proposals are DASHI synthetic reasoning objects, not empirical source propositions and not evidence that the proposed measurement has been performed.


## First-order residue-N kinetics payment

Owner: `DASHI/Biology/Agriculture/QueenslandLegumeResidueFirstOrderKineticsExact.agda`

Thomson, Cameron, Dalal & Hoult 2007 — DOI `10.1071/EA05290` — materially changes the quantitative frontier. In a 17-week northern-Australian Vertisol glasshouse experiment, the source reports first-order N release from added legume residues. Reported rate constants span `0.045-0.325 week^-1`; corresponding half-times span `2.1-15.4 weeks` at 23 C. Residue identity/chemistry and moisture treatment remain part of the observation.

The source payment is therefore:

```text
residue-mineralisation route
+ finite time unit (weeks)
+ first-order kinetic shape
+ reported source rate/half-time ranges
```

It is **not**:

```text
one universal k
= field living-root transfer
= Acacia/Senegalia same-object kernel
= a constructed Bishop ratio r
= an infinite-horizon geometric-tail theorem
```

The largest reported half-time (15.4 weeks) lies inside the 17-week experimental window, so the source genuinely constrains a decay timescale within the fitted experiment. DASHI nevertheless keeps `finiteFirstOrderFitAuthorizesInfiniteHorizonExtrapolation = false`: extending the fitted first-order law to an infinite tail is a separate modelling/source-authority payment.

This leaves a sharply typed mathematical seam between the continuous source fit and the already-owned discrete convergence machinery:

```text
source first-order k > 0
      ↓  [DASHI constructive compiler now owned]
r = exp(-k Δt), 0 < r < 1
      ↓
discrete polynomial/geometric majorant
      ↓
constructive tail / Cauchy compiler
```

The source first-order shape is paid for the Thomson residue system, and DASHI now separately owns the generic positive-rate x positive-time-step -> Bishop contraction compiler. Selecting/embedding a particular empirical k and time step for asymptotic use, and authorizing extrapolation beyond the fitted window, remain separate application/source payments.


## Route x fallow x recovery join

Owner: `DASHI/Biology/Agriculture/QueenslandLegumeResidueFallowRecoveryExact.agda`

Nguyen, Bell, Janke & Williams 2026 (GRDC Grains Research Update, Goondiwindi; no DOI recorded by this atlas) supplies a UQ Gatton same-experiment join across residue placement, fallow duration and following-crop recovery.

```text
short fallow ~2 months:
  lablab/millet -> barley
  AG / BG / AG&BG / bare-fallow treatments
  soil mineral N at 0, 30, 60 d
  barley receives uniform 50 kg N/ha urea
  AG Ndfr ~11-14 kg N/ha
  AG&BG Ndfr ~20-25 kg N/ha

long fallow ~9 months:
  mungbean -> sorghum
  sorghum receives 0 fertilizer N
  total N uptake ~180-200 kg N/ha, no residue-treatment difference
  AG Ndfr ~9-10 kg N/ha
  AG&BG Ndfr ~14-16 kg N/ha
```

The source explicitly states that complete BG residue-N input could not be directly quantified. Recovery-efficiency calculations therefore assumed BG residue N equal to half the corresponding measured AG residue-N input. DASHI keeps isotope-derived Ndfr and assumption-dependent recovery efficiency as distinct evidence objects.

The observer calibration lane additionally records McNeill & Unkovich 2024 (DOI `10.1007/s11104-024-06515-y`) and Liu et al. 2024 (DOI `10.1016/j.fcr.2024.109412`) without transferring their percentages to Queensland.

## Queensland multi-rate fertilizer counterfactual

Owner: `DASHI/Biology/Agriculture/QueenslandChickpeaWheatFertilizerEquivalentExact.agda`

Dalal et al. 1998 (DOI `10.1071/EA98027`) provides the Queensland evidence shape that the earlier single-rate comparator could not pay. The adjacent wheat experiment applied multiple fresh urea-N rates and used linear/quadratic grain-N response curves to estimate the fertilizer-N equivalent of unfertilized wheat following chickpea.

Usable-season equivalents were:

```text
1989  50.1 kg N/ha
1990  57.9
1992  50.5
1993  47.3
1996  40.0

mean = 49.2 +/- 6.4 kg N/ha
```

1988 was 114.6 kg N/ha under anomalous preceding chickpea/nitrate conditions. 1994 and 1995 were explicitly non-estimable because low in-crop rainfall caused poor fertilizer-N uptake.

Therefore the repository now distinguishes:

```text
explicit multi-rate response curve exists
!=
response curve informative this season
!=
one season-invariant replacement value
!=
Acacia/Senegalia avoided mineral N.
```

## Constructive transport / convergence mathematics

The Moonshine convergence work is now imported as application-neutral Analysis infrastructure and reused by agriculture rather than copied semantically.

Ported to this branch:

- `BishopPolynomialSuccessorFactorLimit{Validation,Exact}`
- `BishopStrictRatioInterpolation{Validation,Exact}`
- `BishopPolynomialGeometricSeriesConvergence{Validation,Exact}`
- `PolynomialGeometricTailDomination{Validation,Exact}`
- `TailModulusCauchyBridge{Validation,Exact}`

New generic owners:

- `DASHI/Analysis/ContractiveCompartmentTail{Validation,Exact}.agda`
- `DASHI/Analysis/BishopContractiveCompartmentSeries{Validation,Exact}.agda`

The first proves, application-neutrally,

```text
actual(n) <= majorant(n)
majorant finite tails vanish
--------------------------------
actual finite tails vanish
```

and exposes a consumer-indexed finite decision horizon:

```text
precision
  -> start N
  -> every finite actual tail beginning at N is SmallAt precision.
```

When the selected backend supplies the existing tail-to-Cauchy bridge, the same receipt compiles to `IsCauchy`.

The Bishop owner specializes the tractable majorant

```text
scale * (n+1)^degree * ratio^(n+1),   0 <= ratio < 1
```

and reuses the constructive arbitrary-degree theorem. It additionally proves that any actual Bishop-real contribution sequence whose absolute terms are pointwise bounded by such a majorant has convergent partial sums and therefore a Cauchy cumulative trajectory.

Agriculture exposes this through:

- `ConstructiveNitrogenTransportKernel{Regression,Exact}.agda`

with literal existing-repository convolution equations

```text
M_t = sum_{j=0}^t F_j K_M(t-j)
C_t = sum_{j=0}^t M_j K_C(t-j)
```

and distinct route coordinates for living below-ground, residue/mineralisation, excreta redistribution and soil-stock release.

This is a mathematical compiler, not a fitted ecological law. None of the Queensland sources is thereby asserted to satisfy a polynomial-geometric kernel. For an empirical application the following remain explicit inputs:

- route identity;
- time discretisation / time unit;
- scale;
- fixed degree;
- contraction ratio with a same-object proof of `0 <= r < 1`;
- pointwise bound from observed/modelled contribution to the majorant;
- consumer-selected smallness semantics where an explicit finite decision horizon is required.

Accordingly, convergence or Cauchy stabilization does not itself imply fertilizer replacement, recovery, deployment authority, or correctness of the selected mechanistic model.

## Certification boundary

This addendum records source-written implementation only. No CI query or Agda/kernel typecheck is claimed in this connector-only continuation.