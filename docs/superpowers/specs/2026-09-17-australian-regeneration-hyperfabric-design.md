# Australian Regeneration Hyperfabric Design

## Goal
Extend the existing Acacia/BNF/LES tranche into a comparative regeneration hyperfabric that treats Australian native legumes/wattles, soil-biota rehabilitation, grassland succession and sorghum-sudangrass nurse/cover interventions as separate empirical systems connected only through typed functional roles and trajectory constraints.

## Constraints
- Preserve `external source proposition != source identity metadata != DASHI reconstruction != synthetic collision != cross-source synthesis != deployment authority`.
- Do not identify Australian Acacia/wattle systems with Senegalia senegal or with agricultural sorghum-sudangrass.
- Do not promote inoculation to effective symbiosis, growth, survival, community recovery or authority.
- Do not promote biomass/ground cover/weed suppression to native regeneration.
- Do not promote present vegetation to recovered soil state or vice versa.
- Reuse canonical `AttributedSourceCore`, LES `TaskFactorisation`, BNF and existing Acacia owners.
- Source-order RED regressions precede production owners; no CI/kernel claims unless observed.

## Source-bearing lanes

### Australian native legume / rhizobial restoration
- Burdon et al. 1999, DOI `10.1046/j.1365-2664.1999.00409.x`: strong within- and among-host variation in native Acacia-rhizobia effectiveness.
- Thrall, Burdon & Woods 2000, DOI `10.1046/j.1365-2664.2000.00470.x`: host/population context in native Australian legumes.
- Murray, Thrall & Woods 2001, DOI `10.1046/j.1442-8903.2001.00086.x`: restoration implications of Acacia-rhizobial interactions.
- Thrall et al. 2005, DOI `10.1111/j.1365-2664.2005.01058.x`: direct-seeding field restoration; establishment/growth/survival remain site/species/environment indexed.

### Australian soil-biota / mine rehabilitation
- Bell et al. 2003, DOI `10.1071/SB02004`: introduced AM inoculum can remain infective without extensive native-plant colonisation or growth benefit where indigenous propagules/context dominate.
- Moreira-Grez et al. 2019, DOI `10.3389/fmicb.2019.01617`: agricultural soil-microbial inoculum can mismatch semi-arid Acacia ancistrocarpa mine rehabilitation.
- Kneller et al. 2018, DOI `10.1016/j.scitotenv.2017.11.219`, PMID `29197793`: topsoil/plant-amendment effects in Pilbara Triodia grassland reconstruction; improved soil C/N or microbial activity does not imply recruitment/survival.

### Australian grassland / old-field succession
- Scott & Morgan 2012, DOI `10.1016/j.jaridenv.2011.08.014`: century-scale semi-arid old-field soil/vegetation recovery trajectory.
- Standish et al. 2007, DOI `10.1111/j.1365-2664.2006.01262.x`: dispersal and recruitment limitation in WA old fields.
- Fensham et al. 2016, DOI `10.1111/1365-2664.12551`: Queensland subtropical grassland passive restoration depends on remnant seed sources and avoidance of deflected succession.
- Parkhurst, Standish & Prober 2022, DOI `10.1002/eap.2547`, PMID `35080806`: available-P agricultural legacy persists more than a decade after planting/restoration.

### Sorghum-sudangrass nurse / cover intervention
- Kaneko et al. 2023, DOI `10.1111/grs.12391`: annual sorghum-sudangrass can increase establishment-year cover/forage during slow perennial brachiariagrass establishment, with treatment/mixture dependence.
- Moore et al. 2021, Agronomy 11:2449: one-time sorghum-sudangrass interseeding increases establishment-year forage but need not create residual vegetation effects.
- Burt et al. 2025, DOI `10.1002/cft2.70055`: sorghum-sudangrass mixtures can alter herbage accumulation and weed suppression; these are agricultural pasture functions, not native restoration endpoints.

## Architecture
Create four source-bearing owners plus one theorem-bearing hyperfabric:
1. `AustralianNativeLegumeRhizobiaRestorationExact`
2. `AustralianWattleSoilBiotaRehabilitationExact`
3. `AustralianGrasslandSuccessionRegenerationExact`
4. `SudangrassNurseCoverCropExact`
5. `DrylandPioneerLegumeGrasslandRegenerationHyperfabricExact`

Each owner has a paired regression module. The hyperfabric exposes reusable roles (`nFixingPioneer`, `temporaryNurse`, `soilBiotaCarrier`, `groundCoverProvider`, `weedCompetitor`, `hydrologicalActor`, `recruitmentFacilitator`) while proving role equivalence does not create same-object identity or transferable response.

## Core exact separations
- inoculation != effective symbiosis != establishment != growth != survival != community recovery
- introduced inoculum != indigenous propagule pool
- inoculum viability != realised colonisation
- soil-function improvement != plant recruitment/survival
- soil recovery != floristic recovery
- passive succession != guaranteed reference-community recovery
- present vegetation != erased agricultural nutrient legacy
- temporary nurse cover != perennial/native regeneration
- biomass != biodiversity
- weed suppression != restoration
- intervention success at t1 != trajectory success at t2
- same functional role != same ecological object

## Integration
Export all ten modules from `DASHI/Biology/Agriculture/Everything.agda`, extend the acquisition ledger/audit, and update PR #993 body without changing the canonical nitrogenase ladder or claiming build certification.
