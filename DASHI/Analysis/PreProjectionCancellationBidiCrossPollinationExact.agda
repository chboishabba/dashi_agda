module DASHI.Analysis.PreProjectionCancellationBidiCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNAdjointBalancedSignedCancellationRound428Exact as NS
import DASHI.Physics.QuantumVacuum.ParallelPlateRegulatedDifferenceBidiExact as Casimir

------------------------------------------------------------------------
-- PRE-PROJECTION CANCELLATION: BIDI CROSS-POLLINATION
--
-- The Navier--Stokes donor proves a literal signed cancellation BEFORE norms.
-- The Casimir consumer requires plate/reference subtraction BEFORE cutoff
-- removal.  The common theorem shape is order-of-operations, not an imported
-- theorem instance:
--
--     paired/signed data
--       -> exact linear cancellation/difference
--       -> nonlinear projection (norm / absolute value / limit)
--
-- Reversing the order can destroy the cancellation information.
------------------------------------------------------------------------

data Lane : Set where
  navierStokes casimir spectralPairing : Lane

data ProjectionKind : Set where
  normProjection absoluteValueProjection limitProjection : ProjectionKind

record PreProjectionCancellationShape : Set₁ where
  field
    Carrier : Set
    pairedLeft pairedRight : Carrier
    Combined : Set
    combine : Carrier → Carrier → Combined
    Projected : Set
    project : Combined → Projected
    cancellationBeforeProjection : Set
    reading : String

open PreProjectionCancellationShape public

record CrossPollinationEdge : Set where
  field
    source target : Lane
    theoremShapeReusable : Bool
    applicationReceiptReusable : Bool
    reading : String

open CrossPollinationEdge public

nsToCasimir : CrossPollinationEdge
nsToCasimir = record
  { source = navierStokes
  ; target = casimir
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "NS pre-norm signed cancellation motivates Casimir subtraction-before-limit discipline; the NS receipt is not a Casimir convergence proof."
  }

spectralPairingToCasimir : CrossPollinationEdge
spectralPairingToCasimir = record
  { source = spectralPairing
  ; target = casimir
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "Conjugate/signed spectral pairing before norming has the same order-of-operations shape as plate/reference subtraction before regulator removal; physical instances remain distinct."
  }

record CasimirSubtractionBeforeLimitInvariant : Set₁ where
  field
    Regulator : Set
    Value : Set
    plate reference : Regulator → Value
    subtract : Value → Value → Value
    regulatedDifference : Regulator → Value
    differenceLaw : ∀ r → regulatedDifference r ≡ subtract (plate r) (reference r)

    Limit : Set
    differenceLimit : Limit
    differenceConverges : Set

    subtractionOccursBeforeLimit : Set
    sameRegulatorBothSides : Set
    samePhysicalComparisonObject : Set

open CasimirSubtractionBeforeLimitInvariant public

data SeparateRawLimitsPermission : Set where

data NSCancellationAutomaticallyProvesCasimirLimit : Set where

noSeparateRawLimitPromotion :
  SeparateRawLimitsPermission → ⊥
noSeparateRawLimitPromotion ()

noNSReceiptImport :
  NSCancellationAutomaticallyProvesCasimirLimit → ⊥
noNSReceiptImport ()

record BidiStatus : Set where
  field
    nsLiteralPreNormCancellationExists : Bool
    casimirMatchedDifferenceInterfaceExists : Bool
    sharedOrderOfOperationsShapeOwned : Bool
    nsApplicationReceiptImportedIntoCasimir : Bool

    nsLiteralPreNormCancellationExistsIsTrue :
      nsLiteralPreNormCancellationExists ≡ true
    casimirMatchedDifferenceInterfaceExistsIsTrue :
      casimirMatchedDifferenceInterfaceExists ≡ true
    sharedOrderOfOperationsShapeOwnedIsTrue :
      sharedOrderOfOperationsShapeOwned ≡ true
    nsApplicationReceiptImportedIntoCasimirIsFalse :
      nsApplicationReceiptImportedIntoCasimir ≡ false

open BidiStatus public

canonicalBidiStatus : BidiStatus
canonicalBidiStatus = record
  { nsLiteralPreNormCancellationExists = true
  ; casimirMatchedDifferenceInterfaceExists = true
  ; sharedOrderOfOperationsShapeOwned = true
  ; nsApplicationReceiptImportedIntoCasimir = false
  ; nsLiteralPreNormCancellationExistsIsTrue = refl
  ; casimirMatchedDifferenceInterfaceExistsIsTrue = refl
  ; sharedOrderOfOperationsShapeOwnedIsTrue = refl
  ; nsApplicationReceiptImportedIntoCasimirIsFalse = refl
  }
