module DASHI.Environment.PlasmaActivatedWaterPrimaryPlantNitrogenSourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- PRIMARY PAW -> PLANT-NITROGEN EVIDENCE REGISTRY
--
-- Attribution invariant:
-- primary empirical result != DASHI PAW/N weld != transport != recommendation.
--
-- Reviews remain in PlasmaActivatedWaterAgricultureSourceRegistryExact.
-- This owner adds primary experimental carriers for exact snowball payments.
------------------------------------------------------------------------

data PAWPlantPrimaryRole : Set where
  plasmaNitrateHydroponicComparator
  pawRootNitrogenUptakeMechanism : PAWPlantPrimaryRole

data PAWPlantPrimaryDesign : Set where
  controlledHydroponicNitrateSubstitution
  phytofluidicRootUptakeExperiment : PAWPlantPrimaryDesign

record PAWPlantPrimarySource : Set where
  constructor paw-plant-primary-source
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    role : PAWPlantPrimaryRole
    design : PAWPlantPrimaryDesign
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open PAWPlantPrimarySource public

ruamrungsriHydroponicLettuce2023 : PAWPlantPrimarySource
ruamrungsriHydroponicLettuce2023 = paw-plant-primary-source
  "Soraya Ruamrungsri; Choncharoen Sawangrat; Kanokwan Panjama; Phanumas Sojithamporn; Suchanuch Jaipinta; Wimada Srisuwan; Malinee Intanoo; Chaiartid Inkham; Sa-nguansak Thanapornpoonpong"
  "Effects of Using Plasma-Activated Water as a Nitrate Source on the Growth and Nutritional Quality of Hydroponically Grown Green Oak Lettuces"
  "Horticulturae 9(2):248"
  2023
  "DOI 10.3390/horticulturae9020248"
  plasmaNitrateHydroponicComparator
  controlledHydroponicNitrateSubstitution
  "Green oak lettuce was grown hydroponically under no-nitrate, commercial-nitrate and plasma-generated-nitrate nutrient solutions, providing a direct bounded comparator for plasma nitrate as a hydroponic nitrogen source under the reported reactor and nutrient-solution conditions."
  "Does not establish equivalence for every PAW chemistry, crop, nitrate concentration, reactor, aquaponic system, soil system or whole fertiliser formulation; plant response and nutrient quality remain outcome-specific."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

panjaRootNitrogen2026 : PAWPlantPrimarySource
panjaRootNitrogen2026 = paw-plant-primary-source
  "Suraj Panja; Sumit Kumar Mehta; Jinmay Kalita; Deepak Panchal; Xuehua Zhang; Pranab Kumar Mondal"
  "How plasma activated water promotes plant root growth through interfacial modulation of nitrogen uptake"
  "Journal of Colloid and Interface Science 715:140281"
  2026
  "DOI 10.1016/j.jcis.2026.140281; PMID 41832826"
  pawRootNitrogenUptakeMechanism
  phytofluidicRootUptakeExperiment
  "Brassica juncea roots in a phytofluidic device were exposed to graded microbubble-enhanced PAW; the study reports PAW-dependent nitrogen-uptake kinetics and root development, with improved responses up to about 20 percent PAW and inhibited development at higher fractions under the reported chemistry."
  "Does not establish monotonic benefit, universal Michaelis-Menten parameters, field transport, net seasonal nitrogen uptake, aquaponic safety, or equivalence between PAW percentage and nitrate dose across reactors."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

canonicalPAWPlantPrimarySources : List PAWPlantPrimarySource
canonicalPAWPlantPrimarySources =
  ruamrungsriHydroponicLettuce2023 ∷
  panjaRootNitrogen2026 ∷ []

------------------------------------------------------------------------
-- Non-laundering barriers.
------------------------------------------------------------------------

data PlasmaNitrateComparatorMeansAllPAWPermission : Set where
data RootUptakeMechanismMeansFieldEffectPermission : Set where
data TwentyPercentMeansUniversalOptimumPermission : Set where
data PrimaryPAWStudyMeansRecommendationPermission : Set where

plasmaNitrateComparatorDoesNotPayAllPAW :
  PlasmaNitrateComparatorMeansAllPAWPermission → ⊥
plasmaNitrateComparatorDoesNotPayAllPAW ()

rootUptakeMechanismDoesNotPayFieldEffect :
  RootUptakeMechanismMeansFieldEffectPermission → ⊥
rootUptakeMechanismDoesNotPayFieldEffect ()

twentyPercentDoesNotBecomeUniversalOptimum :
  TwentyPercentMeansUniversalOptimumPermission → ⊥
twentyPercentDoesNotBecomeUniversalOptimum ()

primaryPAWStudyDoesNotPayRecommendation :
  PrimaryPAWStudyMeansRecommendationPermission → ⊥
primaryPAWStudyDoesNotPayRecommendation ()

record PAWPlantPrimaryAttributionBoundary : Set where
  constructor paw-plant-primary-attribution-boundary
  field
    primaryResultAndDashiWeldRemainDistinct : Bool
    reactorChemistryAndPAWLabelRemainDistinct : Bool
    hydroponicComparatorAndFieldTransportRemainDistinct : Bool
    rootMechanismAndSeasonOutcomeRemainDistinct : Bool
    sourceOwnershipRemainsExternal : Bool
    primaryResultAutomaticallyPaysRecommendation : Bool

canonicalPAWPlantPrimaryAttributionBoundary : PAWPlantPrimaryAttributionBoundary
canonicalPAWPlantPrimaryAttributionBoundary =
  paw-plant-primary-attribution-boundary true true true true true false
