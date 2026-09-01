module DASHI.Governance.SexedHistoricalAssociatorSupportedReopeningExact where

------------------------------------------------------------------------
-- ASSOCIATOR-SUPPORTED CHANGE / SELECTIVE REOPENING
--
-- The coalition associator already witnesses that two admitted bracketings of
-- the same local participants can yield different global relational signatures.
-- This owner extracts a finite support for that difference and feeds only the
-- supported coordinates into the existing proof-bearing distributed dependency
-- closure.
--
-- Yijing moving-line structure is reused only as a sparse-change/provenance
-- precedent.  No divinatory prediction, causal mechanism, or received hexagram
-- semantics are promoted into the historical model.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Governance.SexedHistoricalCoalitionAssociatorYijingExact as Associator
import DASHI.Governance.SexedHistoricalDistributedCompatibilityReopeningExact as Distributed

------------------------------------------------------------------------
-- 1. Exact finite support of the canonical associator signature defect.
--
-- In the current six-line fixture the left/right signatures differ only at
-- lines 1 and 4.  Lines 2,3,5,6 agree.  We retain this as a typed support rather
-- than treating the whole signature as changed.
------------------------------------------------------------------------

data SignatureLine : Set where
  line1 line2 line3 line4 line5 line6 : SignatureLine

data InAssociatorSupport : SignatureLine → Set where
  line1Supported : InAssociatorSupport line1
  line4Supported : InAssociatorSupport line4

line2OutsideSupport : InAssociatorSupport line2 → ⊥
line2OutsideSupport ()

line3OutsideSupport : InAssociatorSupport line3 → ⊥
line3OutsideSupport ()

line5OutsideSupport : InAssociatorSupport line5 → ⊥
line5OutsideSupport ()

line6OutsideSupport : InAssociatorSupport line6 → ⊥
line6OutsideSupport ()

record AssociatorSupportReceipt : Set where
  constructor associator-support-receipt
  field
    line1Changed : InAssociatorSupport line1
    line4Changed : InAssociatorSupport line4
    line2Unchanged : InAssociatorSupport line2 → ⊥
    line3Unchanged : InAssociatorSupport line3 → ⊥
    line5Unchanged : InAssociatorSupport line5 → ⊥
    line6Unchanged : InAssociatorSupport line6 → ⊥

canonicalAssociatorSupport : AssociatorSupportReceipt
canonicalAssociatorSupport =
  associator-support-receipt
    line1Supported line4Supported
    line2OutsideSupport line3OutsideSupport line5OutsideSupport line6OutsideSupport

------------------------------------------------------------------------
-- 2. Support-to-artifact chart.
--
-- This chart is a DASHI comparison fixture only.  It says which historical
-- certificates the two changed relational coordinates are taken to interrogate
-- in this finite example; it is not an empirical universal mapping of Yijing
-- line positions to social institutions.
------------------------------------------------------------------------

supportArtifact : SignatureLine → Distributed.DistributedArtifact
supportArtifact line1 = Distributed.feminineLocalCertificate
supportArtifact line2 = Distributed.sourceAttributionCertificate
supportArtifact line3 = Distributed.masculineLocalCertificate
supportArtifact line4 = Distributed.institutionalLocalCertificate
supportArtifact line5 = Distributed.sourceAttributionCertificate
supportArtifact line6 = Distributed.sourceAttributionCertificate

line1TargetsFeminineLocal :
  supportArtifact line1 ≡ Distributed.feminineLocalCertificate
line1TargetsFeminineLocal = refl

line4TargetsInstitutionalLocal :
  supportArtifact line4 ≡ Distributed.institutionalLocalCertificate
line4TargetsInstitutionalLocal = refl

------------------------------------------------------------------------
-- 3. Supported coordinates induce only their proof-bearing dependency cones.
------------------------------------------------------------------------

line1ReopensGlobalCompatibility :
  Dependency.ReopeningObligation
    Distributed.Depends
    (supportArtifact line1)
    Distributed.globalCompatibilityCertificate
line1ReopensGlobalCompatibility =
  Dependency.oneEdgeCreatesReopeningObligation
    Distributed.feminineLocalAffectsCompatibility

line4ReopensGlobalCompatibility :
  Dependency.ReopeningObligation
    Distributed.Depends
    (supportArtifact line4)
    Distributed.globalCompatibilityCertificate
line4ReopensGlobalCompatibility =
  Distributed.institutionalChangeReopensGlobalCompatibility

line1ReopensGlobalContinuation :
  Dependency.ReopeningObligation
    Distributed.Depends
    (supportArtifact line1)
    Distributed.globalContinuationCertificate
line1ReopensGlobalContinuation =
  Dependency.obligationsCompose
    line1ReopensGlobalCompatibility
    (Dependency.oneEdgeCreatesReopeningObligation
      Distributed.compatibilityAffectsGlobalContinuation)

line4ReopensGlobalContinuation :
  Dependency.ReopeningObligation
    Distributed.Depends
    (supportArtifact line4)
    Distributed.globalContinuationCertificate
line4ReopensGlobalContinuation =
  Distributed.institutionalChangeReopensGlobalContinuation

line1ReopensCollectiveFuture :
  Dependency.ReopeningObligation
    Distributed.Depends
    (supportArtifact line1)
    Distributed.collectiveFutureConeCertificate
line1ReopensCollectiveFuture =
  Dependency.obligationsCompose
    line1ReopensGlobalContinuation
    (Dependency.oneEdgeCreatesReopeningObligation
      Distributed.globalContinuationAffectsFutureCone)

line4ReopensCollectiveFuture :
  Dependency.ReopeningObligation
    Distributed.Depends
    (supportArtifact line4)
    Distributed.collectiveFutureConeCertificate
line4ReopensCollectiveFuture =
  Dependency.obligationsCompose
    line4ReopensGlobalContinuation
    (Dependency.oneEdgeCreatesReopeningObligation
      Distributed.globalContinuationAffectsFutureCone)

------------------------------------------------------------------------
-- 4. The associator support is narrower than global invalidation.
------------------------------------------------------------------------

data SupportForcesSourceAttributionReopening : Set where

data SupportForcesMasculineLocalReopening : Set where

data AssociatorSupportMeansEveryCoordinateChanged : Set where

data MovingMaskIsHistoricalCausalMechanism : Set where

data LinePositionHasIntrinsicSocialMeaning : Set where

data DifferenceSupportProvesEmpiricalCause : Set where

data UnchangedCoordinateMeansHistoricallyIrrelevant : Set where

supportDoesNotForceSourceAttributionReopening :
  SupportForcesSourceAttributionReopening → ⊥
supportDoesNotForceSourceAttributionReopening ()

supportDoesNotForceMasculineLocalReopening :
  SupportForcesMasculineLocalReopening → ⊥
supportDoesNotForceMasculineLocalReopening ()

associatorSupportDoesNotMeanEveryCoordinateChanged :
  AssociatorSupportMeansEveryCoordinateChanged → ⊥
associatorSupportDoesNotMeanEveryCoordinateChanged ()

movingMaskIsNotHistoricalCausalMechanism :
  MovingMaskIsHistoricalCausalMechanism → ⊥
movingMaskIsNotHistoricalCausalMechanism ()

linePositionHasNoIntrinsicSocialMeaningHere :
  LinePositionHasIntrinsicSocialMeaning → ⊥
linePositionHasNoIntrinsicSocialMeaningHere ()

differenceSupportDoesNotProveEmpiricalCause :
  DifferenceSupportProvesEmpiricalCause → ⊥
differenceSupportDoesNotProveEmpiricalCause ()

unchangedCoordinateDoesNotMeanHistoricallyIrrelevant :
  UnchangedCoordinateMeansHistoricallyIrrelevant → ⊥
unchangedCoordinateDoesNotMeanHistoricallyIrrelevant ()

------------------------------------------------------------------------
-- 5. Continuity with the associator/Yijing owner.
------------------------------------------------------------------------

canonicalAssociatorResidualStillPresent :
  Associator.CoalitionAssociatorResidual
    Associator.leftBracketedGlobal Associator.rightBracketedGlobal
canonicalAssociatorResidualStillPresent =
  Associator.canonicalCoalitionAssociator

canonicalBracketSignatureStillDiffers :
  Associator.leftBracketSignature ≡ Associator.rightBracketSignature → ⊥
canonicalBracketSignatureStillDiffers =
  Associator.coalitionBracketProducesDifferentRelationalSignature

------------------------------------------------------------------------
-- 6. Boundary receipt.
------------------------------------------------------------------------

record AssociatorSupportedReopeningBoundary : Set where
  constructor associator-supported-reopening-boundary
  field
    finiteAssociatorSupportRetained : Bool
    onlyLinesOneAndFourSupportedInCanonicalFixture : Bool
    supportedLocalCertificatesCanReopenGlobalCompatibility : Bool
    supportedChangesCanReachCollectiveFutureTransitively : Bool
    sourceAttributionReopensAutomatically : Bool
    everyLocalCertificateReopens : Bool
    yijingMovingMaskIsHistoricalMechanism : Bool
    linePositionsCarryIntrinsicSocialMeaning : Bool
    supportEqualsEmpiricalCausation : Bool

canonicalAssociatorSupportedReopeningBoundary :
  AssociatorSupportedReopeningBoundary
canonicalAssociatorSupportedReopeningBoundary =
  associator-supported-reopening-boundary
    true true true true false false false false false
