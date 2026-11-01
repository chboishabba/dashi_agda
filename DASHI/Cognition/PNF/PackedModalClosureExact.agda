{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.PackedModalClosureExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- A2 follow-on: the first factor family consumes the packed operator seam.
-- The factor/demand constructor remains one semantic authority; scalar and
-- SWAR differ only in how the operator selection is physically obtained.
------------------------------------------------------------------------

record ModalInput : Set where
  constructor modalInput
  field
    modalOrdinal headOrdinal : Nat
    subjectOrdinal objectOrdinal : Nat
    negationPresent : Nat

record ModalClosure (Factor Demand : Set) : Set₁ where
  constructor modalClosure
  field
    factors : Factor
    demands : Demand

record PackedModalComposer (Input Factor Demand : Set) : Set₁ where
  constructor packedModalComposer
  field
    scalarCompose : Input → ModalClosure Factor Demand
    packedCompose : Input → ModalClosure Factor Demand

open PackedModalComposer public

record PackedModalClosureExact
    {Input Factor Demand : Set}
    (composer : PackedModalComposer Input Factor Demand) : Set₁ where
  constructor packedModalClosureExact
  field
    closureExact :
      (input : Input) →
      packedCompose composer input ≡ scalarCompose composer input

open PackedModalClosureExact public

------------------------------------------------------------------------
-- Exactness is the admission condition for moving the normative modal
-- factor family to the packed carrier.  It says nothing about runtime speed.
------------------------------------------------------------------------

packedModalMayConsumeScalarAuthority :
  ∀ {Input Factor Demand : Set}
    (composer : PackedModalComposer Input Factor Demand)
    (exact : PackedModalClosureExact composer)
    (input : Input) →
  packedCompose composer input ≡ scalarCompose composer input
packedModalMayConsumeScalarAuthority composer exact input =
  closureExact exact input

------------------------------------------------------------------------
-- Local dependency topology is the only address supplied to this family.
-- A global token surrogate is not a premise of exact packed closure.
------------------------------------------------------------------------

data GlobalTokenSurrogateRequired : Set where

packedClosureDoesNotRequireGlobalTokenSurrogate :
  GlobalTokenSurrogateRequired → ⊥
packedClosureDoesNotRequireGlobalTokenSurrogate ()
