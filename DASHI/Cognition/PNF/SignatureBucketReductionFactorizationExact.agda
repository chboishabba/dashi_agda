module DASHI.Cognition.PNF.SignatureBucketReductionFactorizationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- The runtime factor reducer first partitions proposals by an exact semantic
-- signature and performs compatibility grouping only within that signature.
-- This module isolates the theorem needed for an internal per-signature cache:
-- semantic output may be combined bucketwise without making diagnostic metrics
-- part of the semantic factorization.
------------------------------------------------------------------------

_++ᵇ_ : ∀ {A : Set} → List A → List A → List A
[] ++ᵇ ys = ys
(x ∷ xs) ++ᵇ ys = x ∷ (xs ++ᵇ ys)

-- Minimal local membership/empty types keep this theorem surface independent of
-- the larger stdlib while retaining the exact no-cross-signature premise.
data _∈ˡ_ {A : Set} (x : A) : List A → Set where
  hereˡ : ∀ {xs} → x ∈ˡ (x ∷ xs)
  thereˡ : ∀ {y xs} → x ∈ˡ xs → x ∈ˡ (y ∷ xs)

data ⊥ˡ : Set where

record BucketSemanticReducer
  (Proposal Signature SemanticOutput : Set)
  : Set where
  field
    signature : Proposal → Signature
    reduceBucket : Signature → List Proposal → List SemanticOutput

open BucketSemanticReducer public

record DisjointSignatureBuckets
  {Proposal Signature : Set}
  (signatureOf : Proposal → Signature)
  (left right : List Proposal)
  : Set where
  field
    separated :
      ∀ {l r} →
      l ∈ˡ left →
      r ∈ˡ right →
      signatureOf l ≡ signatureOf r →
      ⊥ˡ

-- A cached implementation needs only this law for its semantic surface.  It is
-- intentionally supplied as a proof obligation of the concrete reducer rather
-- than inferred from owner independence or from a complexity measurement.
record SignatureBucketFactorization
  (Proposal Signature SemanticOutput : Set)
  (reducer : BucketSemanticReducer Proposal Signature SemanticOutput)
  : Set where
  field
    combineSemantic : List SemanticOutput → List SemanticOutput → List SemanticOutput
    factorizes :
      ∀ (leftSignature rightSignature : Signature)
        (left right : List Proposal) →
      DisjointSignatureBuckets (signature reducer) left right →
      combineSemantic
        (reduceBucket reducer leftSignature left)
        (reduceBucket reducer rightSignature right)
      ≡
      (reduceBucket reducer leftSignature left ++ᵇ
       reduceBucket reducer rightSignature right)

open SignatureBucketFactorization public

bucketCacheCombinationIsSemanticCombination :
  ∀ {Proposal Signature SemanticOutput : Set}
    {reducer : BucketSemanticReducer Proposal Signature SemanticOutput}
    (law : SignatureBucketFactorization Proposal Signature SemanticOutput reducer)
    (leftSignature rightSignature : Signature)
    (left right : List Proposal)
    (disjoint : DisjointSignatureBuckets (signature reducer) left right) →
  combineSemantic law
    (reduceBucket reducer leftSignature left)
    (reduceBucket reducer rightSignature right)
  ≡
  (reduceBucket reducer leftSignature left ++ᵇ
   reduceBucket reducer rightSignature right)
bucketCacheCombinationIsSemanticCombination law leftSignature rightSignature left right disjoint =
  factorizes law leftSignature rightSignature left right disjoint
