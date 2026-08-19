module DASHI.Education.EarlyLearningEntitlementRouteSeparationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.EarlyLearningChoicePNFHyperfabricBridge as Choice

------------------------------------------------------------------------
-- UNIVERSAL ENTITLEMENT != UNIFORM DELIVERY
--
-- A universal child entitlement to accessible early learning can coexist with
-- different delivery architectures.  Thus universalism is not identified with
-- compulsory centre attendance, and a parallel family-care option is not
-- identified with removal of the professional floor.
------------------------------------------------------------------------

data DeliveryArchitecture : Set where
  universalProfessionalArchitecture
  universalPlusParallelFamilyArchitecture
  substitutionaryExitArchitecture : DeliveryArchitecture

universalEntitlement : DeliveryArchitecture → Bool
universalEntitlement universalProfessionalArchitecture = true
universalEntitlement universalPlusParallelFamilyArchitecture = true
universalEntitlement substitutionaryExitArchitecture = false

parallelFamilyRoute : DeliveryArchitecture → Bool
parallelFamilyRoute universalProfessionalArchitecture = false
parallelFamilyRoute universalPlusParallelFamilyArchitecture = true
parallelFamilyRoute substitutionaryExitArchitecture = true

professionalFloor : DeliveryArchitecture → Bool
professionalFloor universalProfessionalArchitecture = true
professionalFloor universalPlusParallelFamilyArchitecture = true
professionalFloor substitutionaryExitArchitecture = false

sameEntitlementDifferentRoutes :
  parallelFamilyRoute universalProfessionalArchitecture ≡
  parallelFamilyRoute universalPlusParallelFamilyArchitecture → ⊥
sameEntitlementDifferentRoutes ()

entitlementRouteNonFactorability :
  Intersection.NonFactorabilityWitness universalEntitlement parallelFamilyRoute
entitlementRouteNonFactorability =
  Intersection.nonFactorabilityWitness
    universalProfessionalArchitecture
    universalPlusParallelFamilyArchitecture
    refl
    sameEntitlementDifferentRoutes

universalEntitlementCannotDetermineDeliveryRoute :
  Intersection.FactorsThrough universalEntitlement parallelFamilyRoute → ⊥
universalEntitlementCannotDetermineDeliveryRoute =
  Intersection.witnessRulesOutEveryFlatFactorisation
    entitlementRouteNonFactorability

sameParallelRouteDifferentProfessionalFloor :
  professionalFloor universalPlusParallelFamilyArchitecture ≡
  professionalFloor substitutionaryExitArchitecture → ⊥
sameParallelRouteDifferentProfessionalFloor ()

parallelRouteFloorNonFactorability :
  Intersection.NonFactorabilityWitness parallelFamilyRoute professionalFloor
parallelRouteFloorNonFactorability =
  Intersection.nonFactorabilityWitness
    universalPlusParallelFamilyArchitecture
    substitutionaryExitArchitecture
    refl
    sameParallelRouteDifferentProfessionalFloor

parallelFamilyOptionCannotDetermineProfessionalFloor :
  Intersection.FactorsThrough parallelFamilyRoute professionalFloor → ⊥
parallelFamilyOptionCannotDetermineProfessionalFloor =
  Intersection.witnessRulesOutEveryFlatFactorisation
    parallelRouteFloorNonFactorability

------------------------------------------------------------------------
-- Reuse the older addition/substitution theorem directly.
------------------------------------------------------------------------

expandedChoiceStillCannotDetermineProfessionalFloor :
  Intersection.FactorsThrough
    Choice.expandedChoiceProjection Choice.professionalFloorRetained → ⊥
expandedChoiceStillCannotDetermineProfessionalFloor =
  Choice.expandedChoiceReweightingCannotRecoverMissingProfessionalFloor

------------------------------------------------------------------------
-- Nordic comparative evidence motivates architecture TYPES, not permanent
-- country essences.  Cash-for-childcare schemes have been introduced, amended,
-- reduced and abolished at different times across Nordic welfare states.  The
-- theorem therefore keeps the two policy shapes independent of country names.
------------------------------------------------------------------------

data NordicPolicyArchitecture : Set where
  universalAccessWithoutParallelCashCare
  universalAccessWithParallelCashCare : NordicPolicyArchitecture

nordicUniversalEntitlement : NordicPolicyArchitecture → Bool
nordicUniversalEntitlement universalAccessWithoutParallelCashCare = true
nordicUniversalEntitlement universalAccessWithParallelCashCare = true

nordicParallelCashCare : NordicPolicyArchitecture → Bool
nordicParallelCashCare universalAccessWithoutParallelCashCare = false
nordicParallelCashCare universalAccessWithParallelCashCare = true

nordicArchitecturesDifferAtParallelRoute :
  nordicParallelCashCare universalAccessWithoutParallelCashCare ≡
  nordicParallelCashCare universalAccessWithParallelCashCare → ⊥
nordicArchitecturesDifferAtParallelRoute ()

nordicUniversalismDoesNotDetermineCashCareArchitecture :
  Intersection.FactorsThrough
    nordicUniversalEntitlement nordicParallelCashCare → ⊥
nordicUniversalismDoesNotDetermineCashCareArchitecture =
  Intersection.witnessRulesOutEveryFlatFactorisation
    (Intersection.nonFactorabilityWitness
      universalAccessWithoutParallelCashCare
      universalAccessWithParallelCashCare
      refl
      nordicArchitecturesDifferAtParallelRoute)

record EntitlementRouteBoundary : Set where
  constructor entitlementRouteBoundary
  field
    universalEntitlementMeansUniformRoute : Bool
    universalEntitlementMeansUniformRouteIsFalse :
      universalEntitlementMeansUniformRoute ≡ false
    parallelFamilySupportMeansProfessionalExit : Bool
    parallelFamilySupportMeansProfessionalExitIsFalse :
      parallelFamilySupportMeansProfessionalExit ≡ false
    entitlementAndRouteRemainIndependentCoordinates : Bool
    entitlementAndRouteRemainIndependentCoordinatesIsTrue :
      entitlementAndRouteRemainIndependentCoordinates ≡ true
    architectureTypeEqualsPermanentCountryIdentity : Bool
    architectureTypeEqualsPermanentCountryIdentityIsFalse :
      architectureTypeEqualsPermanentCountryIdentity ≡ false

canonicalEntitlementRouteBoundary : EntitlementRouteBoundary
canonicalEntitlementRouteBoundary =
  entitlementRouteBoundary false refl false refl true refl false refl
