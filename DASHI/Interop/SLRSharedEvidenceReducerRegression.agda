module DASHI.Interop.SLRSharedEvidenceReducerRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRSharedEvidenceReducerExact as Reducer
import DASHI.Interop.SLRSprint2CanonicalEvidenceConvergenceExact as Sprint2

m21RemainsPaid : Sprint2.m21State ≡ Sprint2.paid
m21RemainsPaid = refl

m22RemainsPaid : Sprint2.m22State ≡ Sprint2.paid
m22RemainsPaid = refl

m23AwaitsRuntimeReceipt :
  Sprint2.m23State ≡ Sprint2.implementedAwaitingRuntime
m23AwaitsRuntimeReceipt = refl

reviewedEvidenceReferenceIsCanonical :
  Reducer.reviewedEvidenceReferenceCanonicalAndRevalidated
    Reducer.canonicalReviewedEvidenceParity
  ≡ true
reviewedEvidenceReferenceIsCanonical = refl

sharedReducerCreatesNoSemanticAuthority :
  Reducer.reducerCreatesSemanticAuthority
    Reducer.canonicalSharedEvidenceReducerParity
  ≡ false
sharedReducerCreatesNoSemanticAuthority = refl

sharedReducerPromotesNoApplicability :
  Reducer.reducerPromotesApplicability
    Reducer.canonicalSharedEvidenceReducerParity
  ≡ false
sharedReducerPromotesNoApplicability = refl

sharedReducerPromotesNoClaimTruth :
  Reducer.reducerPromotesClaimTruth
    Reducer.canonicalSharedEvidenceReducerParity
  ≡ false
sharedReducerPromotesNoClaimTruth = refl

reviewedEvidenceIdentityRewriteImpossible :
  Reducer.ReviewedEvidenceIdentityMayBeRewritten → ⊥
reviewedEvidenceIdentityRewriteImpossible =
  Reducer.reviewedEvidenceIdentityCannotBeRewritten

abstentionNeedsNoFabricatedDelta :
  Reducer.AbstentionRequiresFabricatedDelta → ⊥
abstentionNeedsNoFabricatedDelta =
  Reducer.abstentionDoesNotRequireFabricatedDelta
