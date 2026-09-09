module DASHI.Physics.ExoticGravity.AntigravityStrongPromotionFacadeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityResearchPromotionCutExact as Legacy
import DASHI.Physics.ExoticGravity.AntigravityFullyDerivedExperimentalCutExact as Strong
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- STRONG PROMOTION FACADE
--
-- The merged legacy ComparativeAnomalyReceipt remains available for backwards
-- compatibility, but new follow-up consumers must enter through the fully
-- derived/provenanced receipt.  No automatic legacy -> strong promotion exists.
------------------------------------------------------------------------

record StrongComparativeAnomaly
    (claim : Anti.AntigravityClaim) : Set where
  constructor strong-comparative-anomaly
  field
    receipt : Strong.FullyDerivedComparativeAnomalyReceipt claim

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
    legacyComparativeReceiptAutomaticallyUpgrades : Bool
    fullyDerivedComparativeTensionEqualsUniqueMechanism : Bool
    fullyDerivedComparativeTensionEqualsUniversalAntigravityLaw : Bool
    postComparisonResidualsRemainOpen : Bool

canonicalStrongPromotionBoundary : StrongPromotionBoundary
canonicalStrongPromotionBoundary =
  strong-promotion-boundary true false false false true
