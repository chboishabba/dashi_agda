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
-- Storage-engine probe contracts.
--
-- The original ProbeContract remains the ordered/B-tree-style logarithmic
-- contract used by the numeric PNF acceptance proofs.  This tranche adds two
-- orthogonal contracts rather than pretending every lookup has one geometry:
--
-- * exact equality / hash-style probes may be supplied with an expected
--   constant budget;
-- * prefix/partition probes may be supplied with their own explicit bound.
--
-- Agda proves consequences of those receipts.  It does not claim PostgreSQL,
-- a hash table, or a lattice implementation satisfies them without a runtime
-- plan/benchmark witness.
------------------------------------------------------------------------

record ProbeContract : Set where
  constructor probeContract
  field
    probeCost : Nat
    logarithmicProbeBound : Nat
    probeWithinLogarithmicBound :
      probeCost ≤ᶜ logarithmicProbeBound

open ProbeContract public

record ExpectedConstantProbeContract : Set where
  constructor expectedConstantProbeContract
  field
    equalityProbeCost : Nat
    constantProbeBudget : Nat
    equalityProbeWithinConstantBudget :
      equalityProbeCost ≤ᶜ constantProbeBudget

open ExpectedConstantProbeContract public

record PrefixProbeContract : Set where
  constructor prefixProbeContract
  field
    prefixProbeCost : Nat
    prefixProbeBound : Nat
    prefixProbeWithinBound : prefixProbeCost ≤ᶜ prefixProbeBound

open PrefixProbeContract public

data ProbeStrategy : Set where
  exactEqualityHashStrategy : ProbeStrategy
  orderedLogarithmicStrategy : ProbeStrategy
  prefixPartitionStrategy : ProbeStrategy

data TypedProbeContract : ProbeStrategy → Set where
  exactEqualityContract :
    ExpectedConstantProbeContract →
    TypedProbeContract exactEqualityHashStrategy
  orderedLogarithmicContract :
    ProbeContract →
    TypedProbeContract orderedLogarithmicStrategy
  prefixPartitionContract :
    PrefixProbeContract →
    TypedProbeContract prefixPartitionStrategy

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
    expectedConstantEqualityClaimRequiresContract : Set
    prefixPartitionClaimRequiresContract : Set

canonicalDirectLookupBoundary : DirectLookupBoundary
canonicalDirectLookupBoundary =
  directLookupBoundary
    (∀ exports → linearGlobalLookupRows exports ≡ exports)
    NearestCommonInterfaceValidation
    ProbeContract
    ExpectedConstantProbeContract
    PrefixProbeContract
