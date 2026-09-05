module DASHI.Physics.QuantumVacuum.CasimirResidualCauchyToLimitExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; proj₁; proj₂)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Physics.QuantumVacuum.CasimirBishopSetoidBackendReuseExact as Backend

------------------------------------------------------------------------
-- RESIDUAL CAUCHY -> RENORMALISED LIMIT ON THE ACTUAL CASIMIR BISHOP REAL
--
-- Once matched common terms have cancelled, the only analytic convergence
-- input needed for existence is a Cauchy receipt for the residual sequence.
-- Bishop completeness then constructs the limit; uniqueness is also inherited
-- from the backend.
------------------------------------------------------------------------

Real : Spine.SetoidOrderedCompleteReal
Real = Backend.casimirSetoidReal

record ResidualRegulatorSequence : Set₁ where
  field
    residualAt : Nat → Spine.Carrier Real
    sequence : Spine.Sequence Real
    sequenceIsResidual : ∀ n →
      Spine._≈_ Real (Spine.sequenceAt Real sequence n) (residualAt n)
    cauchy : Spine.IsCauchy Real sequence
    reading : String

open ResidualRegulatorSequence public

residualLimitWitness :
  ResidualRegulatorSequence →
  Σ (Spine.Carrier Real)
    (λ limit → Spine.ConvergesTo Real
      (sequence _) limit)
residualLimitWitness R =
  Spine.cauchyLimit Real (sequence R) (cauchy R)

residualLimit : ResidualRegulatorSequence → Spine.Carrier Real
residualLimit R = proj₁ (residualLimitWitness R)

residualConverges :
  (R : ResidualRegulatorSequence) →
  Spine.ConvergesTo Real (sequence R) (residualLimit R)
residualConverges R = proj₂ (residualLimitWitness R)

residualLimitUnique :
  (R : ResidualRegulatorSequence) →
  (other : Spine.Carrier Real) →
  Spine.ConvergesTo Real (sequence R) other →
  Spine._≈_ Real (residualLimit R) other
residualLimitUnique R other otherConverges =
  Spine.limitUnique Real (residualConverges R) otherConverges

record ReverseResidualLimitObligations : Set where
  field
    matchedCommonTermAlreadyCancelled : Set
    residualSequenceIdentified : Set
    residualCauchyEstimate : Set
    sameResidualAsPhysicalCasimirDifference : Set

open ReverseResidualLimitObligations public

data CompletenessAutomaticallyProvesCauchyEstimate : Set where

completenessDoesNotCreateTailEstimate :
  CompletenessAutomaticallyProvesCauchyEstimate → ⊥
completenessDoesNotCreateTailEstimate ()

record Status : Set where
  field
    bishopCompletenessReused : Bool
    cauchyToLimitCompilerOwned : Bool
    limitUniquenessOwned : Bool
    residualCauchyEstimateClosed : Bool

    bishopCompletenessReusedIsTrue : bishopCompletenessReused ≡ true
    cauchyToLimitCompilerOwnedIsTrue : cauchyToLimitCompilerOwned ≡ true
    limitUniquenessOwnedIsTrue : limitUniquenessOwned ≡ true
    residualCauchyEstimateClosedIsFalse : residualCauchyEstimateClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { bishopCompletenessReused = true
  ; cauchyToLimitCompilerOwned = true
  ; limitUniquenessOwned = true
  ; residualCauchyEstimateClosed = false
  ; bishopCompletenessReusedIsTrue = refl
  ; cauchyToLimitCompilerOwnedIsTrue = refl
  ; limitUniquenessOwnedIsTrue = refl
  ; residualCauchyEstimateClosedIsFalse = refl
  }
