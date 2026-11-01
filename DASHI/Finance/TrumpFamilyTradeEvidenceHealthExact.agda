module DASHI.Finance.TrumpFamilyTradeEvidenceHealthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- TRADE-EVIDENCE HEALTH
--
-- A deliberately small specialization of the repository's evidence-health
-- discipline.  Health is not source count.  It tracks exact object identity,
-- point-in-time admissibility, upstream independence, unresolved contradiction
-- and primary-source payment separately.
------------------------------------------------------------------------

record TradeEvidenceHealth : Set where
  constructor trade-evidence-health
  field
    exactClaimIdentityPaid : Bool
    primarySourcePaid : Bool
    pointInTimeAdmissibilityPaid : Bool
    independentCorroborationPaid : Bool
    contradictionUnresolved : Bool
    sourceGenealogyRetained : Bool

open TradeEvidenceHealth public

data HealthClass : Set where
  weakHealth strongHealth : HealthClass

data SourceCount : Set where
  twoVisibleSources : SourceCount

data HealthWorld : Set where
  derivativePairWorld independentPairWorld : HealthWorld

visibleSourceCount : HealthWorld → SourceCount
visibleSourceCount derivativePairWorld = twoVisibleSources
visibleSourceCount independentPairWorld = twoVisibleSources

healthClass : HealthWorld → HealthClass
healthClass derivativePairWorld = weakHealth
healthClass independentPairWorld = strongHealth

sameVisibleCount :
  visibleSourceCount derivativePairWorld ≡ visibleSourceCount independentPairWorld
sameVisibleCount = refl

healthClassesDiffer :
  healthClass derivativePairWorld ≡ healthClass independentPairWorld → ⊥
healthClassesDiffer ()

sourceCountCannotDetermineEvidenceHealth :
  ((x y : HealthWorld) →
    visibleSourceCount x ≡ visibleSourceCount y →
    healthClass x ≡ healthClass y) → ⊥
sourceCountCannotDetermineEvidenceHealth factor =
  healthClassesDiffer (factor derivativePairWorld independentPairWorld refl)

record PromotionEligibleHealth (h : TradeEvidenceHealth) : Set where
  constructor promotion-eligible-health
  field
    exactIdentityPaid : exactClaimIdentityPaid h ≡ true
    primaryPaid : primarySourcePaid h ≡ true
    pointInTimePaid : pointInTimeAdmissibilityPaid h ≡ true
    genealogyPaid : sourceGenealogyRetained h ≡ true
    contradictionClosedForConsumedProposition : contradictionUnresolved h ≡ false

open PromotionEligibleHealth public

------------------------------------------------------------------------
-- Even strong evidentiary health does not manufacture legal or causal claims.
------------------------------------------------------------------------

data HealthyEvidenceMeansCausationPermission : Set where
data HealthyEvidenceMeansIllegalityPermission : Set where
data HealthyEvidenceMeansMotivePermission : Set where

evidenceHealthDoesNotCreateCausation : HealthyEvidenceMeansCausationPermission → ⊥
evidenceHealthDoesNotCreateCausation ()

evidenceHealthDoesNotCreateIllegality : HealthyEvidenceMeansIllegalityPermission → ⊥
evidenceHealthDoesNotCreateIllegality ()

evidenceHealthDoesNotCreateMotive : HealthyEvidenceMeansMotivePermission → ⊥
evidenceHealthDoesNotCreateMotive ()

record TradeEvidenceHealthBoundary : Set where
  constructor trade-evidence-health-boundary
  field
    sourceCountDoesNotDetermineHealth : Bool
    exactIdentityIsIndependentCoordinate : Bool
    pointInTimeAdmissibilityIsIndependentCoordinate : Bool
    genealogyIsIndependentCoordinate : Bool
    contradictionStatusIsIndependentCoordinate : Bool
    healthDoesNotCreateCausationIllegalityOrMotive : Bool

canonicalTradeEvidenceHealthBoundary : TradeEvidenceHealthBoundary
canonicalTradeEvidenceHealthBoundary =
  trade-evidence-health-boundary true true true true true true
