module DASHI.Physics.QuantumVacuum.CasimirBishopMatchedAsymptoticCancellationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import Real as BishopReal
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.BishopMatchedCommonTermCancellationExact as Cancel
import DASHI.Physics.QuantumVacuum.CasimirBishopSetoidBackendReuseExact as Backend

------------------------------------------------------------------------
-- CASIMIR MATCHED ASYMPTOTIC CANCELLATION ON THE LITERAL BISHOP CARRIER
------------------------------------------------------------------------

CasimirAnalyticScalar : Set
CasimirAnalyticScalar = Spine.Carrier Backend.casimirSetoidReal

record CasimirMatchedAsymptoticDecomposition : Set₁ where
  field
    Regulator : Set
    plate reference : Regulator → CasimirAnalyticScalar
    plateResidual referenceResidual commonDivergentTerm :
      Regulator → CasimirAnalyticScalar

    plateDecomposition : ∀ r →
      Spine._≈_ Backend.casimirSetoidReal
        (plate r)
        (Spine._+_ Backend.casimirSetoidReal
          (plateResidual r)
          (commonDivergentTerm r))

    referenceDecomposition : ∀ r →
      Spine._≈_ Backend.casimirSetoidReal
        (reference r)
        (Spine._+_ Backend.casimirSetoidReal
          (referenceResidual r)
          (commonDivergentTerm r))

    samePhysicalRegulator : Set
    sameAsymptoticConvention : Set
    reading : String

open CasimirMatchedAsymptoticDecomposition public

asBishopMatchedDecomposition :
  CasimirMatchedAsymptoticDecomposition →
  Cancel.BishopMatchedRegulatedDecomposition
asBishopMatchedDecomposition D = record
  { Cancel.Regulator = Regulator D
  ; Cancel.plate = plate D
  ; Cancel.reference = reference D
  ; Cancel.plateResidual = plateResidual D
  ; Cancel.referenceResidual = referenceResidual D
  ; Cancel.commonTerm = commonDivergentTerm D
  ; Cancel.plateDecomposition = plateDecomposition D
  ; Cancel.referenceDecomposition = referenceDecomposition D
  }

casimirCommonDivergenceCancels :
  (D : CasimirMatchedAsymptoticDecomposition) →
  ∀ r →
  Spine._≈_ Backend.casimirSetoidReal
    (Spine._-_ Backend.casimirSetoidReal (plate D r) (reference D r))
    (Spine._-_ Backend.casimirSetoidReal
      (plateResidual D r)
      (referenceResidual D r))
casimirCommonDivergenceCancels D =
  Cancel.bishopRegulatedDifferenceCancelsCommon
    (asBishopMatchedDecomposition D)

record ResidualLimitObligations
    (D : CasimirMatchedAsymptoticDecomposition) : Set where
  field
    residualDifferenceIntegrableOrSummable : Set
    residualDifferenceCauchyTail : Set
    regulatorRemovalOnResidualDifference : Set
    residualLimitIndependentOfPresentation : Set
    sameResidualAsCasimirObservable : Set

open ResidualLimitObligations public

data ExactCancellationAutomaticallyProvesResidualTail : Set where

data RawDivergentFamiliesNeedSeparateLimits : Set where

cancellationDoesNotProveTail :
  ExactCancellationAutomaticallyProvesResidualTail → ⊥
cancellationDoesNotProveTail ()

matchedRenormalisationNeedsNoRawLimits :
  RawDivergentFamiliesNeedSeparateLimits → ⊥
matchedRenormalisationNeedsNoRawLimits ()

record Status : Set where
  field
    bishopCarrierSameAsCasimirAnalyticCarrier : Bool
    commonDivergenceCancellationOwned : Bool
    residualTailClosed : Bool

    bishopCarrierSameAsCasimirAnalyticCarrierIsTrue :
      bishopCarrierSameAsCasimirAnalyticCarrier ≡ true
    commonDivergenceCancellationOwnedIsTrue : commonDivergenceCancellationOwned ≡ true
    residualTailClosedIsFalse : residualTailClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { bishopCarrierSameAsCasimirAnalyticCarrier = true
  ; commonDivergenceCancellationOwned = true
  ; residualTailClosed = false
  ; bishopCarrierSameAsCasimirAnalyticCarrierIsTrue = refl
  ; commonDivergenceCancellationOwnedIsTrue = refl
  ; residualTailClosedIsFalse = refl
  }
