module DASHI.Physics.ExoticGravity.AntigravityStrongPromotionFacadeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityResearchPromotionCutExact as Legacy
import DASHI.Physics.ExoticGravity.AntigravityCalibratedFullyDerivedExperimentalCutExact as Strong
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- STRONG PROMOTION FACADE
--
-- The merged legacy ComparativeAnomalyReceipt remains available for backwards
-- compatibility.  New consumers must enter through the calibrated,
-- provenance-bound, fully-derived receipt.  No legacy -> strong upgrade is
-- supplied.
------------------------------------------------------------------------

record StrongComparativeAnomaly
    (claim : Anti.AntigravityClaim) : Set₁ where
  constructor strong-comparative-anomaly
  field
    receipt : Strong.CalibratedFullyDerivedComparativeAnomalyReceipt claim

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
-- Strong post-comparison residuals remain ordinary research obligations, not a
-- declaration of a new universal law.
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
    calibrationStringAloneSufficient : Bool
    legacyComparativeReceiptAutomaticallyUpgrades : Bool
    fullyDerivedComparativeTensionEqualsUniqueMechanism : Bool
    fullyDerivedComparativeTensionEqualsUniversalAntigravityLaw : Bool
    postComparisonResidualsRemainOpen : Bool

canonicalStrongPromotionBoundary : StrongPromotionBoundary
canonicalStrongPromotionBoundary =
  strong-promotion-boundary true true false false false false true
