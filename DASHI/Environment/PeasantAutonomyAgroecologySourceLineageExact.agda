module DASHI.Environment.PeasantAutonomyAgroecologySourceLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.SustainableAgricultureManagementSourceRegistryExact as Sources
import DASHI.Environment.PluralSustainableLandManagementTraditionsExact as Plural

------------------------------------------------------------------------
-- PEASANT / AUTONOMY AGROECOLOGY SOURCE LINEAGE
--
-- Social-movement self-description and technical agronomy are different
-- evidence fibres.  The source owner is retained at the proposition level.
------------------------------------------------------------------------

data AgrarianClaimKind : Set where
  foodSovereigntyClaim
  peasantAgroecologyClaim
  landTerritoryClaim
  seedSovereigntyClaim
  nativeMaizeMilpaClaim
  autonomousGovernanceClaim
  technicalOutcomeClaim
  causalEffectClaim
  portableRecommendationClaim : AgrarianClaimKind

record AgrarianAttributedClaim : Set where
  constructor agrarian-attributed-claim
  field
    claimKind : AgrarianClaimKind
    stage : Sources.ClaimStage
    source : Plural.TraditionSource
    proposition : String
    exactOrBestLocator : String
    claimOwner : Attribution.ClaimOwner
    excludedInference : String

open AgrarianAttributedClaim public

viaCampesinaFoodSovereigntyClaim : AgrarianAttributedClaim
viaCampesinaFoodSovereigntyClaim = agrarian-attributed-claim
  foodSovereigntyClaim
  Sources.externalSourceClaim
  Plural.viaCampesinaFoodSovereignty
  "Food sovereignty is treated as a people/producer-centred governance and rights framework over food systems, land, water and seeds."
  "Declaration of Nyéléni, 27 February 2007"
  Attribution.externalSourceOwner
  "Does not imply one technical farm method, one political programme outside its source scope, or a quantified biophysical outcome."

viaCampesinaAgroecologyClaim : AgrarianAttributedClaim
viaCampesinaAgroecologyClaim = agrarian-attributed-claim
  peasantAgroecologyClaim
  Sources.externalSourceClaim
  Plural.viaCampesinaPeasantAgroecology
  "Peasant agroecology is represented as involving knowledge, territories, seeds, biodiversity, collective organisation and food sovereignty rather than a technique list alone."
  "Nyéléni 2015 Declaration of the International Forum for Agroecology"
  Attribution.externalSourceOwner
  "Does not prove the effect of a particular cover crop, inoculant, tillage, grazing or agroforestry intervention."

zapatistaAgroecologySecondaryClaim : AgrarianAttributedClaim
zapatistaAgroecologySecondaryClaim = agrarian-attributed-claim
  nativeMaizeMilpaClaim
  Sources.externalSourceClaim
  Plural.zapatistaAgroecologyScholarship
  "Secondary scholarship reports agroecological organisation, native-maize/milpa diversification, seed banks and seed-sovereignty practices in Zapatista autonomous communities."
  "Chiapas agroecology and seed-sovereignty scholarship; exact primary EZLN locator remains unresolved claim-by-claim"
  Attribution.externalSourceOwner
  "Must not be rendered as a direct EZLN quotation or as proof that every Zapatista community uses one identical agricultural system."

zapatistaPrimarySourceResidual : AgrarianAttributedClaim
zapatistaPrimarySourceResidual = agrarian-attributed-claim
  autonomousGovernanceClaim
  Sources.dashiReconstruction
  Plural.zapatistaSeedSovereignty
  "Repository records a primary-source residual for exact EZLN/autonomous-community locators governing specific agrarian propositions."
  "Primary source still to be recovered for each proposition"
  Attribution.dashiFormalisationOwner
  "Secondary scholarly evidence remains usable as secondary evidence but cannot be silently upgraded to primary movement authorship."

------------------------------------------------------------------------
-- Community/movement ownership must not be collapsed into individual authors.
------------------------------------------------------------------------

data CollectiveMovementMeansNamedIndividualAuthorPermission : Set where

data SecondaryScholarMeansMovementSpeakerPermission : Set where

data PoliticalFrameworkMeansAgronomicMechanismPermission : Set where

data SeedSovereigntyMeansYieldEffectPermission : Set where

data FoodSovereigntyMeansFoodSecurityOutcomePermission : Set where

data AutonomousPracticeMeansUniversalZapatistaPracticePermission : Set where

collectiveMovementDoesNotCreateNamedIndividualAuthor :
  CollectiveMovementMeansNamedIndividualAuthorPermission → ⊥
collectiveMovementDoesNotCreateNamedIndividualAuthor ()

secondaryScholarDoesNotBecomeMovementSpeaker : SecondaryScholarMeansMovementSpeakerPermission → ⊥
secondaryScholarDoesNotBecomeMovementSpeaker ()

politicalFrameworkDoesNotProveAgronomicMechanism : PoliticalFrameworkMeansAgronomicMechanismPermission → ⊥
politicalFrameworkDoesNotProveAgronomicMechanism ()

seedSovereigntyDoesNotProveYieldEffect : SeedSovereigntyMeansYieldEffectPermission → ⊥
seedSovereigntyDoesNotProveYieldEffect ()

foodSovereigntyDoesNotByItselfProveFoodSecurityOutcome :
  FoodSovereigntyMeansFoodSecurityOutcomePermission → ⊥
foodSovereigntyDoesNotByItselfProveFoodSecurityOutcome ()

autonomousPracticeDoesNotGeneraliseAcrossAllZapatistaCommunities :
  AutonomousPracticeMeansUniversalZapatistaPracticePermission → ⊥
autonomousPracticeDoesNotGeneraliseAcrossAllZapatistaCommunities ()

record PeasantAutonomyAttributionBoundary : Set where
  constructor peasant-autonomy-attribution-boundary
  field
    movementSelfDescriptionAndScholarshipRemainDistinct : Bool
    collectiveAndIndividualAuthorshipRemainDistinct : Bool
    movementFrameworkAndTechnicalMethodRemainDistinct : Bool
    primarySourceResidualMayRemainExplicit : Bool
    secondarySourceMustNotBePromotedToPrimary : Bool
    dashiCrossSourceInferenceRemainsDashiOwned : Bool

canonicalPeasantAutonomyAttributionBoundary : PeasantAutonomyAttributionBoundary
canonicalPeasantAutonomyAttributionBoundary =
  peasant-autonomy-attribution-boundary true true true true true true
