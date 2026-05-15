module DASHI.Core.TypedResidualBasisDecomposition where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Typed Residual Basis Decomposition (TRBD).
--
-- TRBD is the reusable protocol for diagnostics of the form:
--
--   residual -> projection onto a typed basis -> named obstruction ->
--   coverage/perpendicular residual -> promotion decision.
--
-- Numeric projection is performed by an external runner over the relevant
-- metric/covariance.  This module records the typed basis provenance, frozen
-- numeric receipt strings, and promotion boundary.

data BasisSourceType : Set where
  causalBasis :
    BasisSourceType

  structuralBasis :
    BasisSourceType

  symmetryBasis :
    BasisSourceType

  mdlBasis :
    BasisSourceType

  fittedBasis :
    BasisSourceType

NotFittedBasisSource : BasisSourceType → Set
NotFittedBasisSource fittedBasis = ⊥
NotFittedBasisSource _ = ⊤

BasisName : Set
BasisName = String

record TypedBasis (X : Set) : Setω where
  field
    basisName :
      BasisName

    basisVectors :
      List X

    basisSource :
      BasisSourceType

    notFitted :
      NotFittedBasisSource basisSource

    basisSourceDescription :
      String

    basisPromotionBoundary :
      List String

open TypedBasis public

data ObstructionStatus : Set where
  pass :
    ObstructionStatus

  obstructionTypedClean :
    BasisName →
    ObstructionStatus

  obstructionTypedPartial :
    BasisName →
    ObstructionStatus

  obstructionUntyped :
    ObstructionStatus

TRBDPromotionEligible : ObstructionStatus → Set
TRBDPromotionEligible pass = ⊤
TRBDPromotionEligible (obstructionTypedClean _) = ⊤
TRBDPromotionEligible (obstructionTypedPartial _) = ⊥
TRBDPromotionEligible obstructionUntyped = ⊥

record TRBDProtocolThresholds : Set where
  field
    coverageThresholdName :
      String

    coverageThreshold :
      String

    perpendicularThresholdName :
      String

    perpendicularThreshold :
      String

    thresholdFrozen :
      Bool

    thresholdFrozenIsTrue :
      thresholdFrozen ≡ true

open TRBDProtocolThresholds public

record TRBDReceipt (X : Set) : Setω where
  field
    observed :
      X

    predicted :
      X

    residualConvention :
      String

    metricOrCovariance :
      String

    basis :
      TypedBasis X

    basisCoefficients :
      List String

    rawChi2PerDof :
      String

    perpendicularChi2PerDof :
      String

    basisCoverage :
      String

    basisCoverageFormula :
      String

    coverageHonest :
      basisCoverageFormula ≡
      "rho_B = 1 - (perpendicular chi2 / raw chi2)"

    thresholds :
      TRBDProtocolThresholds

    obstructionStatus :
      ObstructionStatus

    projectionArtifact :
      String

    diagnosticOnly :
      Bool

    promotionBoundary :
      List String

open TRBDReceipt public

record PromotableTRBDReceipt (X : Set) : Setω where
  field
    receipt :
      TRBDReceipt X

    statusPromotable :
      TRBDPromotionEligible (obstructionStatus receipt)

    derivedBasis :
      NotFittedBasisSource (basisSource (basis receipt))

    diagnosticOnlyIsFalse :
      diagnosticOnly receipt ≡ false

open PromotableTRBDReceipt public

data OpenTRBDObstructionName : Set where
  openTypedClean :
    BasisName →
    OpenTRBDObstructionName

  openTypedPartial :
    BasisName →
    OpenTRBDObstructionName

record DASHIDerivationRequest : Set where
  field
    requestedQuantity :
      String

    requestedDerivationSource :
      BasisSourceType

    requestOpen :
      Bool

    requestOpenIsTrue :
      requestOpen ≡ true

    requestNotes :
      List String

open DASHIDerivationRequest public

record OpenShapeLawRequest (X : Set) : Setω where
  field
    receipt :
      TRBDReceipt X

    obstructionNamed :
      OpenTRBDObstructionName

    derivationPending :
      DASHIDerivationRequest

    nonPromoting :
      Bool

    nonPromotingIsTrue :
      nonPromoting ≡ true

    notPromotableReason :
      List String

open OpenShapeLawRequest public
