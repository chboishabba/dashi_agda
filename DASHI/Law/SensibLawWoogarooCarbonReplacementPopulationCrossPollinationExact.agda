module DASHI.Law.SensibLawWoogarooCarbonReplacementPopulationCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as WoogarooIbrahim
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom
import DASHI.Law.SensibLawWoogarooPopulationConnectivityAcquisitionExact as Population

data ReplacementDimension : Set where
  standingCarbonStock
  annualCarbonAccumulation
  canopyStructuralMaturity
  habitatFunction
  populationCarryingCapacity
  realisedConnectivity
  geneFlow
  restorationTimeLag : ReplacementDimension

record ReplacementCoordinate : Set where
  constructor replacement-coordinate
  field
    dimension : ReplacementDimension
    impactSideQuestion : String
    offsetSideQuestion : String
    parityQuestion : String
    legalConsumer : String
    boundary : String

open ReplacementCoordinate public

carbonStockCoordinate : ReplacementCoordinate
carbonStockCoordinate = replacement-coordinate
  standingCarbonStock
  "How much live/dead/soil carbon is presently stored in the affected mature/native vegetation?"
  "How much carbon does the proposed offset presently store, and what trajectory is credibly expected under the actual management plan?"
  "When, if ever, does the offset recover the carbon stock lost at the impact site after accounting for initial emissions/disturbance and uncertainty?"
  "Supporting input to EPBC offset maturity/restoration-lag analysis; not by itself the protected-matter habitat test."
  "A high future growth rate is not the same quantity as present standing carbon stock."

carbonFluxCoordinate : ReplacementCoordinate
carbonFluxCoordinate = replacement-coordinate
  annualCarbonAccumulation
  "What is the current annual carbon accumulation of the affected trees/stand?"
  "What annual accumulation is expected at the offset through establishment, rapid growth and later maturation?"
  "Compare time-integrated stock trajectories, not one-year sequestration rates alone."
  "Supporting carbon/time-lag evidence only."
  "Young stands can have high stand-level sequestration rates while large individual trees may accumulate large absolute amounts; neither fact alone establishes replacement."

structuralMaturityCoordinate : ReplacementCoordinate
structuralMaturityCoordinate = replacement-coordinate
  canopyStructuralMaturity
  "What mature structural features are present now: large trees, crown volume, hollows, coarse woody debris, canopy layering and established food/resource trees?"
  "Which of those structures exist now at the offset, which must be created, and over what credible time horizon?"
  "Can the replacement deliver the same protected-matter attribute within the period relevant to the affected wildlife?"
  "EPBC offsetVegetationMaturityAtom + offsetRestorationLagAtom; also informs s 13 substitutability."
  "Planted trees are not immediate substitutes for mature structural habitat merely because vegetation cover or stem count increases."

populationCapacityCoordinate : ReplacementCoordinate
populationCapacityCoordinate = replacement-coordinate
  populationCarryingCapacity
  "What current food, refuge, movement and breeding/dispersal resources does the impact landscape contribute to the relevant Koala population?"
  "How does the offset's capacity to support that population change through time as vegetation establishes and matures?"
  "Does the population experience an interim or permanent reduction in usable carrying capacity even if long-run vegetation growth is positive?"
  "NCA s 13 habitatPopulationEssentialityAtom; supporting s 102 seriousness/duration analysis."
  "Positive vegetation growth does not imply equal population-support capacity; carrying capacity remains a separate state coordinate."

connectivityCoordinate : ReplacementCoordinate
connectivityCoordinate = replacement-coordinate
  realisedConnectivity
  "Does the current habitat function as a movement/gene-flow connection in the existing population network?"
  "Is the offset geographically and functionally capable of preserving the same movement/gene-flow relation?"
  "Can any lost network function be restored before demographic/genetic isolation effects occur?"
  "NCA s 13 essentiality/substitutability and s 102 causal seriousness."
  "Area or carbon parity does not imply realised connectivity or gene-flow parity."

record LogisticCrossPollination : Set where
  constructor logistic-cross-pollination
  field
    canonicalOwner : String
    populationStateExplicit : Bool
    growthDirectionNotPopulationState : Bool
    carryingCapacityTimeVaryingAllowed : Bool
    habitatMaturityMayChangeCapacity : Bool
    positiveRegrowthImpliesPopulationRecovery : Bool
    carbonParityImpliesPopulationParity : Bool

canonicalWoogarooLogisticCrossPollination : LogisticCrossPollination
canonicalWoogarooLogisticCrossPollination = logistic-cross-pollination
  "DASHI/Biology/LogisticPopulationDirectionalEvidenceExact.agda"
  true true true true false false

carbonSequestrationQid : Id.ItemId
carbonSequestrationQid = Id.itemId "Q15305550"

oldGrowthForestQid : Id.ItemId
oldGrowthForestQid = Id.itemId "Q208478"

forestEcologyQid : Id.ItemId
forestEcologyQid = Id.itemId "Q2249329"

restorationEcologyQid : Id.ItemId
restorationEcologyQid = Id.itemId "Q2428433"

logisticEquationQid : Id.ItemId
logisticEquationQid = Id.itemId "Q736352"

forestEcologyDewey : String
forestEcologyDewey = "577.3"

fragmentationDewey : String
fragmentationDewey = WoogarooIbrahim.fragmentationDewey

populationGeneticsDewey : String
populationGeneticsDewey = WoogarooIbrahim.populationGeneticsDewey

conservationDewey : String
conservationDewey = WoogarooIbrahim.conservationDewey

stephenson2014 : Source.AttributedSource
stephenson2014 = Source.mkDOISource
  "N. L. Stephenson; A. J. Das; R. Condit; S. E. Russo; P. J. Baker; et al."
  "Rate of tree carbon accumulation increases continuously with tree size"
  "Nature 507, 90-93"
  "2014"
  "10.1038/nature12914"
  "https://doi.org/10.1038/nature12914"
  Source.academicArticleSource
  "Global individual-tree analysis showing that absolute mass/carbon accumulation commonly increases with tree size. Used to reject the simplistic premise that large old trees are merely inert carbon stores. It does not establish stand-level sequestration superiority for every old forest or the age of any Woogaroo tree."
  Source.publicAttribution

luyssaert2008 : Source.AttributedSource
luyssaert2008 = Source.mkDOISource
  "Sebastiaan Luyssaert; E.-Detlef Schulze; Annett Boerner; Alexander Knohl; Beverly E. Law; Philippe Ciais; John Grace"
  "Old-growth forests as global carbon sinks"
  "Nature 455, 213-215"
  "2008"
  "10.1038/nature07276"
  "https://doi.org/10.1038/nature07276"
  Source.academicArticleSource
  "Global synthesis supporting continued carbon accumulation in many old forests and the importance of large accumulated stocks. Quantitative old-growth sink estimates are contested in later literature, so this source is carried with its criticism rather than promoted as universal."
  Source.publicAttribution

gundersen2021 : Source.AttributedSource
gundersen2021 = Source.mkDOISource
  "Per Gundersen; Emil E. Thybring; Thomas Nord-Larsen; Lars Vesterdal; Knute J. Nadelhoffer; Vivian K. Johannsen"
  "Old-growth forest carbon sinks overestimated"
  "Nature 591, E21-E23"
  "2021"
  "10.1038/s41586-021-03266-z"
  "https://doi.org/10.1038/s41586-021-03266-z"
  Source.academicArticleSource
  "Direct scientific challenge to the magnitude of old-growth sink estimates. Preserved so the Woogaroo model distinguishes high standing stock from uncertain net ecosystem sink rate."
  Source.publicAttribution

keith2014 : Source.AttributedSource
keith2014 = Source.mkDOISource
  "Heather Keith; Brendan G. Mackey; David B. Lindenmayer"
  "Managing temperate forests for carbon storage: impacts of logging versus forest protection on carbon stocks"
  "Ecosphere 5"
  "2014"
  "10.1890/ES14-00051.1"
  "https://doi.org/10.1890/ES14-00051.1"
  Source.academicArticleSource
  "Australian native-forest case study showing substantially larger biomass carbon stocks in old-growth than logged forest in its montane-ash study system. Regional comparator only; not evidence that the same ratio applies at Woogaroo."
  Source.publicAttribution

crouzeilles2016 : Source.AttributedSource
crouzeilles2016 = Source.mkDOISource
  "Renato Crouzeilles; Michael Curran; Mariana S. Ferreira; David B. Lindenmayer; Carlos E. V. Grelle; Jose M. Rey Benayas"
  "A global meta-analysis on the ecological drivers of forest restoration success"
  "Nature Communications 7, 11666"
  "2016"
  "10.1038/ncomms11666"
  "https://doi.org/10.1038/ncomms11666"
  Source.academicArticleSource
  "Meta-analysis showing restoration success depends strongly on time, disturbance and landscape context and that restored forests do not automatically recover old-growth biodiversity/vegetation structure. Used for restoration-lag and substitutability questions, not for a Woogaroo-specific recovery time."
  Source.publicAttribution

macintosh2024 : Source.AttributedSource
macintosh2024 = Source.mkDOISource
  "Andrew Macintosh; Don Butler; Pablo Larraondo; Dean Ansell; Marie Waschka; Megan C. Evans; David Lindenmayer; Philip Gibbons; David Eldridge; Rod Fensham; Paul Summerfield"
  "Australian human-induced native forest regeneration carbon offset projects have limited impact on changes in woody vegetation cover and carbon removals"
  "Communications Earth & Environment 5, 149"
  "2024"
  "10.1038/s43247-024-01313-x"
  "https://doi.org/10.1038/s43247-024-01313-x"
  Source.academicArticleSource
  "Australian offset-integrity comparator showing why claimed regeneration/removal outcomes require measurement rather than assumption. It concerns a different carbon-offset method and does not establish anything about the identity or adequacy of Springview's proposed biodiversity offsets."
  Source.publicAttribution

dcceewOffsetGuide : Source.AttributedSource
dcceewOffsetGuide = Source.mkNoDOISource
  "Department of Climate Change, Energy, the Environment and Water"
  "Offsets assessment guide"
  "EPBC environmental offsets guidance"
  "2023"
  "https://www.dcceew.gov.au/environment/epbc/approvals/offsets/guidance/offsets-assessment-guide"
  Source.governmentSource
  "Primary Commonwealth guidance making time until ecological benefit, risk of loss, future quality with/without offset and confidence explicit inputs. This is the direct legal-policy bridge for maturity/time-lag analysis; it does not say carbon stock alone determines offset adequacy."
  Source.publicAttribution

carbonReplacementSourceAtlas : Source.AttributedSourceAtlas
carbonReplacementSourceAtlas = Source.mkSourceAtlas
  "Woogaroo carbon replacement / forest maturity / population-capacity source atlas"
  "DASHI.Law.SensibLawWoogarooCarbonReplacementPopulationCrossPollinationExact"
  (stephenson2014 ∷ luyssaert2008 ∷ gundersen2021 ∷ keith2014 ∷
   crouzeilles2016 ∷ macintosh2024 ∷ dcceewOffsetGuide ∷ [])
  "Snowball separates individual-tree carbon accumulation, stand-level carbon stock/sink, restoration trajectory, biodiversity structure, population capacity and official offset-policy timing. General science supplies mechanism/method only; Springview/offset parity remains a same-object quantitative task."

carbonCoordinate : Ibrahim.DashiKnowledgeCoordinate
carbonCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooCarbonReplacementPopulationCrossPollinationExact.agda"
  "forest carbon stock / accumulation / replacement trajectory"
  forestEcologyDewey
  (Id.rawItemId carbonSequestrationQid)
  "doi:10.1038/nature12914; doi:10.1038/nature07276; doi:10.1890/ES14-00051.1"

restorationCoordinate : Ibrahim.DashiKnowledgeCoordinate
restorationCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooCarbonReplacementPopulationCrossPollinationExact.agda"
  "restoration maturity and time-to-function"
  forestEcologyDewey
  (Id.rawItemId restorationEcologyQid)
  "doi:10.1038/ncomms11666; DCCEEW offsets assessment guide"

logisticCoordinate : Ibrahim.DashiKnowledgeCoordinate
logisticCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Biology/LogisticPopulationDirectionalEvidenceExact.agda"
  "population growth / carrying-capacity model discipline"
  populationGeneticsDewey
  (Id.rawItemId logisticEquationQid)
  "canonical in-repo logistic-population owner; model coordinate only"

restorationSupportsOffsetLag : Ibrahim.DashiFirstLinkEdge
restorationSupportsOffsetLag = Ibrahim.dashi-first-link-edge
  restorationCoordinate carbonCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Restoration trajectories determine whether future vegetation can repay present carbon/structural loss and on what timescale; neither coordinate supplies Springview-specific parity without exact data."
  true

logisticSupportsPopulationCounterfactual : Ibrahim.DashiFirstLinkEdge
logisticSupportsPopulationCounterfactual = Ibrahim.dashi-first-link-edge
  logisticCoordinate WoogarooIbrahim.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Population/logistic machinery reinforces that growth direction, carrying capacity and population state are different variables; habitat maturation can change population-support capacity through time."
  true

record CarbonPopulationAtomBinding : Set where
  constructor carbon-population-atom-binding
  field
    dimension : ReplacementDimension
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    methodPaid : Bool
    sameObjectPaid : Bool
    note : String

open CarbonPopulationAtomBinding public

maturityToOffset : CarbonPopulationAtomBinding
maturityToOffset = carbon-population-atom-binding
  canopyStructuralMaturity
  Atom.offsetVegetationMaturityAtom
  Atom.epbc8575OffsetAdequacyConsumer
  true false
  "Science and policy make maturity/quality distinct from area; exact impact- and offset-side maturity remain to be measured."

lagToOffset : CarbonPopulationAtomBinding
lagToOffset = carbon-population-atom-binding
  restorationTimeLag
  Atom.offsetRestorationLagAtom
  Atom.epbc8575OffsetAdequacyConsumer
  true false
  "Official offsets guidance explicitly uses time until ecological benefit; exact Springview offset lag remains open."

capacityToS13 : CarbonPopulationAtomBinding
capacityToS13 = carbon-population-atom-binding
  populationCarryingCapacity
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  true false
  "Population-support capacity through time informs the without-site/substitutability counterfactual but does not itself prove statutory essentiality."

maturityToS102 : CarbonPopulationAtomBinding
maturityToS102 = carbon-population-atom-binding
  canopyStructuralMaturity
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  true false
  "Long replacement time and irreversible mature-structure loss may inform duration/reversibility of effect; they do not independently satisfy s 102."

record CarbonReplacementAcquisition : Set where
  constructor carbon-replacement-acquisition
  field
    impactCurrentCarbonStock : Bool
    impactCurrentStructuralMaturity : Bool
    offsetCurrentCarbonStock : Bool
    offsetCurrentStructuralMaturity : Bool
    offsetGrowthTrajectory : Bool
    timeToCarbonStockParity : Bool
    timeToHabitatFunctionParity : Bool
    timeToPopulationCapacityParity : Bool
    exactOffsetIdentityRequiredFirst : Bool
    note : String

currentCarbonReplacementAcquisition : CarbonReplacementAcquisition
currentCarbonReplacementAcquisition = carbon-replacement-acquisition
  false false false false false false false false true
  "Do not calculate replacement time until exact offset parcels and impact-side reference state are identified. Once paid, estimate separate trajectories for carbon stock, structural habitat quality and population-support function; there may be no single replacement time."

populationAcquisitionReuse : Population.AcquisitionLeafReceipt
populationAcquisitionReuse = Population.counterfactualLeaf

data LargeOldTreeMeansOldStandAlwaysHigherAnnualSink : Set where
data YoungForestFastGrowthMeansCarbonStockReplaced : Set where
data CarbonStockParityMeansHabitatParity : Set where
data CarbonParityMeansPopulationCapacityParity : Set where
data PlantedForestMeansMatureForest : Set where
data EqualAreaMeansEqualOffsetFunction : Set where
data CarbonScienceMeansOffsetLegallyAdequate : Set where
data PositivePopulationGrowthMeansCarryingCapacityRecovered : Set where
data OneReplacementTimeFitsAllDimensions : Set where

largeTreeResultDoesNotUniversaliseStandSink : LargeOldTreeMeansOldStandAlwaysHigherAnnualSink → ⊥
largeTreeResultDoesNotUniversaliseStandSink ()

fastGrowthDoesNotRepayStockAutomatically : YoungForestFastGrowthMeansCarbonStockReplaced → ⊥
fastGrowthDoesNotRepayStockAutomatically ()

carbonParityDoesNotCreateHabitatParity : CarbonStockParityMeansHabitatParity → ⊥
carbonParityDoesNotCreateHabitatParity ()

carbonParityDoesNotCreatePopulationParity : CarbonParityMeansPopulationCapacityParity → ⊥
carbonParityDoesNotCreatePopulationParity ()

plantingDoesNotCreateMaturity : PlantedForestMeansMatureForest → ⊥
plantingDoesNotCreateMaturity ()

areaDoesNotCreateFunctionalEquivalence : EqualAreaMeansEqualOffsetFunction → ⊥
areaDoesNotCreateFunctionalEquivalence ()

carbonScienceDoesNotCreateLegalAdequacy : CarbonScienceMeansOffsetLegallyAdequate → ⊥
carbonScienceDoesNotCreateLegalAdequacy ()

positiveGrowthDoesNotIdentifyRecoveredCapacity : PositivePopulationGrowthMeansCarryingCapacityRecovered → ⊥
positiveGrowthDoesNotIdentifyRecoveredCapacity ()

noSingleReplacementClock : OneReplacementTimeFitsAllDimensions → ⊥
noSingleReplacementClock ()
