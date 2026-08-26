{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.PackedNormativeDeltaAuthorityBridgeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- A2 normative composition boundary.
--
-- The packed hot path is allowed to reason with fibre-local token addresses.
-- Current durable authority may still use database-owned token identities in
-- object/factor/demand digests.  Those identities are supplied only at the
-- publication boundary; they are not a semantic prerequisite of local solve.
------------------------------------------------------------------------

record PackedNormativeArchitecture
    (PackedInput LocalAddress AuthorityTokenId LocalDelta DurableDelta : Set) : Set₁ where
  field
    localSolve : PackedInput → LocalDelta
    authorityTokenId : PackedInput → LocalAddress → AuthorityTokenId
    materialize :
      (PackedInput → LocalAddress → AuthorityTokenId) →
      PackedInput → LocalDelta → DurableDelta
    reference : PackedInput → DurableDelta

open PackedNormativeArchitecture public

------------------------------------------------------------------------
-- Exact publication bridge.
------------------------------------------------------------------------

record PackedNormativeAuthorityExact
    {PackedInput LocalAddress AuthorityTokenId LocalDelta DurableDelta : Set}
    (architecture :
      PackedNormativeArchitecture
        PackedInput LocalAddress AuthorityTokenId LocalDelta DurableDelta) : Set₁ where
  field
    materializationExact :
      (input : PackedInput) →
      materialize architecture
        (authorityTokenId architecture)
        input
        (localSolve architecture input)
      ≡ reference architecture input

open PackedNormativeAuthorityExact public

packedSolvePublishesReference :
  ∀ {PackedInput LocalAddress AuthorityTokenId LocalDelta DurableDelta : Set}
    (architecture :
      PackedNormativeArchitecture
        PackedInput LocalAddress AuthorityTokenId LocalDelta DurableDelta)
    (exact : PackedNormativeAuthorityExact architecture)
    (input : PackedInput) →
  materialize architecture
    (authorityTokenId architecture)
    input
    (localSolve architecture input)
  ≡ reference architecture input
packedSolvePublishesReference architecture exact input =
  materializationExact exact input

------------------------------------------------------------------------
-- The authority-id map is a publication input, not evidence that the local
-- solver itself needs global/database token identity.
------------------------------------------------------------------------

data LocalSolveRequiresIndependentGlobalTokenId : Set where

data DurableDigestIdentityMayBeInventedLocally : Set where

data MaterializationParityAuthorizesSecondSemanticAuthority : Set where

localSolveNeedNotRequireGlobalTokenId :
  LocalSolveRequiresIndependentGlobalTokenId → ⊥
localSolveNeedNotRequireGlobalTokenId ()

durableIdentityCannotBeInventedLocally :
  DurableDigestIdentityMayBeInventedLocally → ⊥
durableIdentityCannotBeInventedLocally ()

materializationParityDoesNotCreateAuthority :
  MaterializationParityAuthorizesSecondSemanticAuthority → ⊥
materializationParityDoesNotCreateAuthority ()

------------------------------------------------------------------------
-- Naturality of physical identity application: if two authority-id adapters
-- are pointwise equal, materialization cannot distinguish them.
------------------------------------------------------------------------

record PointwiseSameAuthorityMap
    {PackedInput LocalAddress AuthorityTokenId : Set}
    (left right : PackedInput → LocalAddress → AuthorityTokenId) : Set₁ where
  field
    same :
      (input : PackedInput) →
      (address : LocalAddress) →
      left input address ≡ right input address

open PointwiseSameAuthorityMap public

-- The concrete runtime bridge proves this by constructing the same Numeric*
-- digest inputs after ordinal-to-authority-id substitution.  The generic
-- architecture intentionally does not assume function extensionality here;
-- concrete instances may discharge equality by their own finite carrier.
