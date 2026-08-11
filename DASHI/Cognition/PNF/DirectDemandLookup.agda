module DASHI.Cognition.PNF.DirectDemandLookup where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.NumericAuthority

------------------------------------------------------------------------
-- Linear export index versus descendant visibility expansion.
------------------------------------------------------------------------

linearGlobalLookupRows : Nat → Nat
linearGlobalLookupRows exports = exports

linearGlobalLookupRowsExact : ∀ exports →
  linearGlobalLookupRows exports ≡ exports
linearGlobalLookupRowsExact exports = refl

ancestorCopiedVisibilityRows : Nat → Nat
ancestorCopiedVisibilityRows zero = zero
ancestorCopiedVisibilityRows (suc n) =
  suc n +ᶜ ancestorCopiedVisibilityRows n

ancestorCopiedVisibilityRowsStep : ∀ n →
  ancestorCopiedVisibilityRows (suc n) ≡
    suc n +ᶜ ancestorCopiedVisibilityRows n
ancestorCopiedVisibilityRowsStep n = refl

------------------------------------------------------------------------
-- The B-tree contribution is an explicit storage-engine contract. Agda proves
-- the composition of that contract with bounded candidate retrieval and DAG
-- validation; it does not pretend to prove PostgreSQL's implementation.
------------------------------------------------------------------------

record ProbeContract : Set where
  constructor probeContract
  field
    probeCost : Nat
    logarithmicProbeBound : Nat
    probeWithinLogarithmicBound :
      probeCost ≤ᶜ logarithmicProbeBound

open ProbeContract public

lookupCost : ProbeContract → Nat → Nat → Nat
lookupCost contract candidates pathHeight =
  (probeCost contract +ᶜ candidates) +ᶜ pathHeight

lookupBound : ProbeContract → Nat → Nat → Nat
lookupBound contract candidates pathHeight =
  (logarithmicProbeBound contract +ᶜ candidates) +ᶜ pathHeight

lookupCostWithinBound : ∀ contract candidates pathHeight →
  lookupCost contract candidates pathHeight ≤ᶜ
    lookupBound contract candidates pathHeight
lookupCostWithinBound contract candidates pathHeight =
  +ᶜ-monotone-right
    (+ᶜ-monotone-right
      (probeWithinLogarithmicBound contract)
      candidates)
    pathHeight

record NearestCommonInterfaceValidation : Set where
  constructor nearestCommonInterfaceValidation
  field
    demandInterface candidateInterface commonInterface : InterfaceId
    validationPathHeight : Nat

open NearestCommonInterfaceValidation public

record CandidateBound : Set where
  constructor candidateBound
  field
    returnedCandidates maximumCandidates : Nat
    returnedWithinMaximum : returnedCandidates ≤ᶜ maximumCandidates

open CandidateBound public

record DirectLookupCertificate : Set where
  constructor directLookupCertificate
  field
    probe : ProbeContract
    candidates : CandidateBound
    commonInterfaceValidation : NearestCommonInterfaceValidation
    totalCost : Nat
    totalCostIsProbePlusCandidatesPlusPath :
      totalCost ≡
        lookupCost
          probe
          (returnedCandidates candidates)
          (validationPathHeight commonInterfaceValidation)

open DirectLookupCertificate public

record DirectLookupBoundary : Set where
  constructor directLookupBoundary
  field
    oneGlobalRowPerExport : Set
    candidateAdmissionRequiresDAGValidation : Set
    btreeLogarithmicClaimRequiresProbeContract : Set

canonicalDirectLookupBoundary : DirectLookupBoundary
canonicalDirectLookupBoundary =
  directLookupBoundary
    (∀ exports → linearGlobalLookupRows exports ≡ exports)
    NearestCommonInterfaceValidation
    ProbeContract
