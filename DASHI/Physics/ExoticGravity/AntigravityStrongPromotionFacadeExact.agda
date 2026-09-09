module DASHI.Physics.ExoticGravity.AntigravityStrongPromotionFacadeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityResearchPromotionCutExact as Legacy
import DASHI.Physics.ExoticGravity.AntigravityClaimScopedComparativeAnomalyExact as Strong
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- STRONG PROMOTION FACADE
--
-- New consumers require the exact claim-scoped calibration/comparison weld.
-- Thus provenance, derivation, calibration, consumer adequacy, and comparison
-- all remain attached to the same antigravity claim.  No legacy -> strong
-- automatic upgrade exists.
------------------------------------------------------------------------

record StrongComparativeAnomaly
    (claim : Anti.AntigravityClaim) : Set₁ where
  constructor strong-comparative-anomaly
  field
    receipt : Strong.ClaimScopedComparativeAnomalyReceipt claim

open StrongComparativeAnomaly public

data StrongResearchStatus : Set where
  fullyDerivedComparativeTension : StrongResearchStatus
  mechanismAttributionStillOpen : StrongResearchStatus
  crossApparatusGeneralityStillOpen : StrongResearchStatus
  lawScopeStillOpen : StrongResearchStatus

statusFromStrongComparativeAnomaly :
  {claim : Anti.AntigravityClaim} →
  StrongComparativeAnomaly claim → StrongResearchStatus
statusFromStrongComparativeAnomaly strong = fullyDerivedComparativeTension

------------------------------------------------------------------------
-- No automatic upgrade from the weaker merged receipt.
------------------------------------------------------------------------

data LegacyToStrongUpgradeAuthority : Set where

legacyReceiptCannotAutoUpgrade :
  {claim : Anti.AntigravityClaim} →
  Legacy.ComparativeAnomalyReceipt claim →
  LegacyToStrongUpgradeAuthority →
  StrongComparativeAnomaly claim
legacyReceiptCannotAutoUpgrade legacy ()

------------------------------------------------------------------------
-- Strong post-comparison residuals remain ordinary research obligations.
------------------------------------------------------------------------

data StrongPostComparisonResidual : Set where
  missingMechanismSpecificAttribution : StrongPostComparisonResidual
  missingIndependentCrossApparatusReplication : StrongPostComparisonResidual
  missingAlternativeLawScope : StrongPostComparisonResidual
  unresolvedOrdinaryModelRevision : StrongPostComparisonResidual

producerForStrongPostComparisonResidual :
  StrongPostComparisonResidual → Search.ProducerClass
producerForStrongPostComparisonResidual missingMechanismSpecificAttribution =
  Search.discriminatorProducer
producerForStrongPostComparisonResidual missingIndependentCrossApparatusReplication =
  Search.empiricalEvidenceProducer
producerForStrongPostComparisonResidual missingAlternativeLawScope =
  Search.propositionSourceProducer
producerForStrongPostComparisonResidual unresolvedOrdinaryModelRevision =
  Search.contradictionProducer

record StrongPromotionBoundary : Set where
  constructor strong-promotion-boundary
  field
    newConsumersRequireFullyDerivedReceipt : Bool
    newConsumersRequireTypedCalibration : Bool
    newConsumersRequireConsumerScopedCalibration : Bool
    exactClaimScopedCutIdentityRequired : Bool
    calibrationStringAloneSufficient : Bool
    legacyComparativeReceiptAutomaticallyUpgrades : Bool
    fullyDerivedComparativeTensionEqualsUniqueMechanism : Bool
    fullyDerivedComparativeTensionEqualsUniversalAntigravityLaw : Bool
    postComparisonResidualsRemainOpen : Bool

canonicalStrongPromotionBoundary : StrongPromotionBoundary
canonicalStrongPromotionBoundary =
  strong-promotion-boundary true true true true false false false false true
