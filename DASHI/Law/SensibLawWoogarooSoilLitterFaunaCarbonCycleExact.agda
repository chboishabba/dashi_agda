module DASHI.Law.SensibLawWoogarooSoilLitterFaunaCarbonCycleExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooCarbonReplacementPopulationCrossPollinationExact as Carbon
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- SOIL / LITTER / FAUNA / BIOGEOCHEMICAL-CYCLE EXTENSION
--
-- Existing mature habitat is not only standing trees.  It includes detrital
-- inputs, soil-carbon pools, below-ground processes and animal-mediated carbon
-- and regeneration pathways.  This owner adds those dimensions without
-- promoting general mechanism literature into a Woogaroo-specific quantity.
------------------------------------------------------------------------

data EcosystemReplacementClock : Set where
  abovegroundCarbonClock
  soilCarbonClock
  detritalLitterClock
  habitatStructureClock
  populationSupportClock
  bioticProcessClock : EcosystemReplacementClock

record EcosystemReplacementDimension : Set where
  constructor ecosystem-replacement-dimension
  field
    clock : EcosystemReplacementClock
    impactQuestion : String
    replacementQuestion : String
    mechanism : String
    legalUse : String
    boundary : String

open EcosystemReplacementDimension public

soilCarbonDimension : EcosystemReplacementDimension
soilCarbonDimension = ecosystem-replacement-dimension
  soilCarbonClock
  "How much carbon and organic matter are presently stored in the organic horizon and mineral soil beneath the affected forest, and how are those pools maintained by litter/root inputs?"
  "What soil-carbon state exists at the proposed replacement/offset site now, and how long would establishment and continuing litter/root inputs take to recover a comparable soil pool after disturbance?"
  "Long-term experiments show that reducing litter inputs can reduce soil-carbon stocks and that soil responses are not instantaneous or linear."
  "Supports offset time-lag/maturity and s 102 duration/reversibility analysis where soil disturbance or loss of mature litter inputs is factually relevant."
  "Temperate-forest DIRT experiments establish mechanism and timescale sensitivity; they do not quantify Woogaroo soil carbon or prove a Woogaroo-specific recovery time."

litterDimension : EcosystemReplacementDimension
litterDimension = ecosystem-replacement-dimension
  detritalLitterClock
  "What established litter layer, coarse organic material and recurring mature-canopy litter inputs currently support decomposition, soil organic matter and habitat microstructure?"
  "Does the proposed replacement provide the same detrital inputs now, or only after canopy development and species composition mature?"
  "Leaf/root detritus is an upstream input to soil organic matter and decomposition; loss of canopy can change this input stream before a replacement stand matures."
  "Supports habitat-function and restoration-lag analysis; may also inform mature-existing versus planted/regrowth comparisons."
  "Presence of planted stems or rapid canopy growth is not evidence that the detrital/soil system has already reached mature-forest state."

bioticProcessDimension : EcosystemReplacementDimension
bioticProcessDimension = ecosystem-replacement-dimension
  bioticProcessClock
  "Which animal-mediated processes presently move carbon, nutrients and propagules through the landscape, including seed dispersal, browsing/herbivory and movement of organic matter?"
  "Can an offset/revegetation site support equivalent fauna-mediated processes through time, including the animal populations and connectivity needed for those processes?"
  "Zoogeochemistry literature shows animals can materially alter ecosystem carbon exchange/storage through trophic and movement-mediated pathways; defaunation can alter forest composition and carbon storage in some systems."
  "Cross-pollinates offset functional-equivalence work with s 13 population/connectivity and s 102 habitat-function loss."
  "General animal-carbon literature does not establish that any particular Woogaroo species contributes a specified quantity of carbon storage, and tropical defaunation effect sizes must not be transferred directly to subtropical Woogaroo."

habitatProcessDimension : EcosystemReplacementDimension
habitatProcessDimension = ecosystem-replacement-dimension
  habitatStructureClock
  "What habitat functions disappear immediately with clearing: mature food trees, crown structure, shade/microclimate, hollows/coarse material, litter/soil structure and movement continuity?"
  "Which functions exist at the replacement site at the same time, and which require years or decades of ecological development?"
  "Habitat replacement is a trajectory of structures and processes, not a one-time hectare or stem-count equality."
  "Directly informs offset vegetation-maturity/time-lag atoms and the s 13 substitutability counterfactual."
  "Carbon-stock parity, vegetation cover parity or equal hectares do not entail habitat-function parity."

------------------------------------------------------------------------
-- Attribution / identifiers / Dewey.
------------------------------------------------------------------------

soilCarbonQid : Id.ItemId
soilCarbonQid = Id.itemId "Q7554898"

plantLitterQid : Id.ItemId
plantLitterQid = Id.itemId "Q2512035"

carbonCycleQid : Id.ItemId
carbonCycleQid = Id.itemId "Q167751"

seedDispersalQid : Id.ItemId
seedDispersalQid = Id.itemId "Q943313"

soilEcologyDewey : String
soilEcologyDewey = "577.57"

forestEcologyDewey : String
forestEcologyDewey = Carbon.forestEcologyDewey

lajtha2014 : Source.AttributedSource
lajtha2014 = Source.mkDOISource
  "Kate Lajtha; Sarah E. Crow; Yukiko Yano; Sherri S. Kaushal; Elliott Sulzman; Peter Sollins; Jeffrey D. H. Spears"
  "Litter and Root Manipulations Provide Insights into Soil Organic Matter Dynamics and Stability"
  "Soil Science Society of America Journal 78, S261-S269"
  "2014"
  "10.2136/sssaj2013.08.0370nafsc"
  "https://doi.org/10.2136/sssaj2013.08.0370nafsc"
  Source.academicArticleSource
  "Primary DIRT experiment synthesis: after two decades, litter/root exclusion changed soil-carbon pools and respiration, with litter exclusion associated with substantial profile mineral-soil carbon decline. Used for mechanism and lag, not as a Woogaroo quantitative estimate."
  Source.publicAttribution

bowden2014 : Source.AttributedSource
bowden2014 = Source.mkDOISource
  "Richard D. Bowden; Leslie Deem; Alain F. Plante; Clement Peltre; Knute J. Nadelhoffer; Kate Lajtha"
  "Litter Input Controls on Soil Carbon in a Temperate Deciduous Forest"
  "Soil Science Society of America Journal 78, S66-S75"
  "2014"
  "10.2136/sssaj2013.09.0413nafsc"
  "https://doi.org/10.2136/sssaj2013.09.0413nafsc"
  Source.academicArticleSource
  "Primary long-term litter-manipulation result showing reduced litter inputs can lower soil-carbon stocks; used as mechanism/trajectory evidence only."
  Source.publicAttribution

schmitz2018 : Source.AttributedSource
schmitz2018 = Source.mkDOISource
  "Oswald J. Schmitz; Christopher C. Wilmers; Shawn J. Leroux; Christopher E. Doughty; Trisha B. Atwood; Mauro Galetti; Andrew B. Davies; Scott J. Goetz"
  "Animals and the zoogeochemistry of the carbon cycle"
  "Science 362(6419), eaar3213"
  "2018"
  "10.1126/science.aar3213"
  "https://doi.org/10.1126/science.aar3213"
  Source.academicArticleSource
  "Foundational synthesis showing animals can mediate ecosystem carbon exchange/storage and linking animal movement, ecosystem function and remote sensing. Used for process topology, not Woogaroo effect size."
  Source.publicAttribution

brodie2024 : Source.AttributedSource
brodie2024 = Source.mkDOISource
  "Jedediah F. Brodie; Carolina Bello; Carine Emer; Mauro Galetti; Matthew S. Luskin; Anand Osuri; Carlos A. Peres; Annina Stoll; Nacho Villar; Ana Benitez-Lopez"
  "Defaunation impacts on the carbon balance of tropical forests"
  "Conservation Biology 39(1), e14414; online 28 October 2024"
  "2024"
  "10.1111/cobi.14414"
  "https://doi.org/10.1111/cobi.14414"
  Source.academicArticleSource
  "Peer-reviewed review of defaunation mechanisms and carbon consequences in tropical forests, including seed-dispersal/tree-composition pathways. UQ co-authorship is retained as attribution; tropical effect sizes are not transferred to Woogaroo."
  Source.publicAttribution

soilFaunaCarbonSourceAtlas : Source.AttributedSourceAtlas
soilFaunaCarbonSourceAtlas = Source.mkSourceAtlas
  "Woogaroo soil, litter, fauna and carbon-cycle source atlas"
  "DASHI.Law.SensibLawWoogarooSoilLitterFaunaCarbonCycleExact"
  (lajtha2014 ∷ bowden2014 ∷ schmitz2018 ∷ brodie2024 ∷ [])
  "Primary and peer-reviewed mechanism sources. They establish separable ecosystem processes and plausible replacement lags, not Springview-specific stock, fauna contribution, offset parity or legal conclusion."

soilCoordinate : Ibrahim.DashiKnowledgeCoordinate
soilCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooSoilLitterFaunaCarbonCycleExact.agda"
  "soil carbon / litter input / below-ground replacement trajectory"
  soilEcologyDewey
  (Id.rawItemId soilCarbonQid)
  "doi:10.2136/sssaj2013.08.0370nafsc; doi:10.2136/sssaj2013.09.0413nafsc"

faunalCarbonCoordinate : Ibrahim.DashiKnowledgeCoordinate
faunalCarbonCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooSoilLitterFaunaCarbonCycleExact.agda"
  "animal-mediated carbon cycling / seed dispersal / ecosystem process"
  forestEcologyDewey
  (Id.rawItemId carbonCycleQid)
  "doi:10.1126/science.aar3213; doi:10.1111/cobi.14414; seed-dispersal Q943313"

soilCrossPollinatesCarbon : Ibrahim.DashiFirstLinkEdge
soilCrossPollinatesCarbon = Ibrahim.dashi-first-link-edge
  soilCoordinate Carbon.carbonCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Standing biomass carbon and soil/detrital carbon are coupled but distinct state variables with distinct disturbance/recovery dynamics."
  true

faunaCrossPollinatesPopulation : Ibrahim.DashiFirstLinkEdge
faunaCrossPollinatesPopulation = Ibrahim.dashi-first-link-edge
  faunalCarbonCoordinate Carbon.logisticCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Animal populations are not only habitat consumers; some also mediate regeneration, nutrient and carbon pathways. Population loss and ecosystem-process loss therefore remain separable coordinates."
  true

------------------------------------------------------------------------
-- Legal/atom intersections.
------------------------------------------------------------------------

record EcosystemAtomBinding : Set where
  constructor ecosystem-atom-binding
  field
    clock : EcosystemReplacementClock
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    methodPaid : Bool
    sameObjectPaid : Bool
    note : String

open EcosystemAtomBinding public

soilLagToOffset : EcosystemAtomBinding
soilLagToOffset = ecosystem-atom-binding
  soilCarbonClock
  Atom.offsetRestorationLagAtom
  Atom.epbc8575OffsetAdequacyConsumer
  true false
  "General science pays the need to treat soil/detrital recovery as potentially time-lagged; exact impact/offset soil states are not yet measured."

habitatProcessToOffset : EcosystemAtomBinding
habitatProcessToOffset = ecosystem-atom-binding
  habitatStructureClock
  Atom.offsetVegetationMaturityAtom
  Atom.epbc8575OffsetAdequacyConsumer
  true false
  "Mature habitat is a bundle of structures/processes, not area alone; exact functional equivalence remains open."

bioticProcessToS13 : EcosystemAtomBinding
bioticProcessToS13 = ecosystem-atom-binding
  bioticProcessClock
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  true false
  "Animal-mediated ecological process can inform the without-site/substitutability counterfactual when locally demonstrated, but general zoogeochemistry does not prove Springview essentiality."

habitatProcessToS102 : EcosystemAtomBinding
habitatProcessToS102 = ecosystem-atom-binding
  habitatStructureClock
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  true false
  "Immediate loss of mature habitat structures and process networks may inform magnitude, duration and reversibility; expert/current same-object payment remains open."

------------------------------------------------------------------------
-- Replacement state: six clocks must not collapse into one.
------------------------------------------------------------------------

record EcosystemReplacementState : Set where
  constructor ecosystem-replacement-state
  field
    abovegroundCarbonMeasured : Bool
    soilCarbonMeasured : Bool
    litterDetritalStateMeasured : Bool
    habitatStructureMeasured : Bool
    populationSupportMeasured : Bool
    bioticProcessMeasured : Bool
    exactOffsetIdentityPaid : Bool
    note : String

currentEcosystemReplacementState : EcosystemReplacementState
currentEcosystemReplacementState = ecosystem-replacement-state
  false false false false false false false
  "Method/source topology is paid. Woogaroo and final-offset same-object measurements are not. Preserve six separate clocks: above-ground carbon, soil carbon, detrital/litter system, habitat structure, population support and animal-mediated ecosystem process."

------------------------------------------------------------------------
-- WrongType / no-promotion boundaries.
------------------------------------------------------------------------

data AbovegroundCarbonParityEqualsSoilParity : Set where
data SoilCarbonParityEqualsHabitatParity : Set where
data PlantedTreesEqualMatureLitterSystem : Set where
data FaunaPresenceEqualsZoogeochemicalFunction : Set where
data TropicalDefaunationEffectEqualsWoogarooEffect : Set where
data SeedDispersalMechanismEqualsS13Essentiality : Set where
data CarbonCycleParityEqualsOffsetAdequacy : Set where

abovegroundDoesNotPaySoil : AbovegroundCarbonParityEqualsSoilParity → ⊥
abovegroundDoesNotPaySoil ()

soilDoesNotPayHabitat : SoilCarbonParityEqualsHabitatParity → ⊥
soilDoesNotPayHabitat ()

plantingDoesNotCreateMatureDetritus : PlantedTreesEqualMatureLitterSystem → ⊥
plantingDoesNotCreateMatureDetritus ()

faunaPresenceDoesNotProveProcessMagnitude : FaunaPresenceEqualsZoogeochemicalFunction → ⊥
faunaPresenceDoesNotProveProcessMagnitude ()

tropicalEffectDoesNotTransfer : TropicalDefaunationEffectEqualsWoogarooEffect → ⊥
tropicalEffectDoesNotTransfer ()

seedDispersalDoesNotProveS13 : SeedDispersalMechanismEqualsS13Essentiality → ⊥
seedDispersalDoesNotProveS13 ()

carbonCycleDoesNotPayOffsetAdequacy : CarbonCycleParityEqualsOffsetAdequacy → ⊥
carbonCycleDoesNotPayOffsetAdequacy ()
