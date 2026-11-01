module DASHI.Philosophy.PolyphonicRelation where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)

------------------------------------------------------------------------
-- Dialectic, dialogue, and polyphony are distinct.  Polyphony retains
-- multiple voices and relations among relations without requiring one final
-- authorial synthesis.

data RelationalMode : Set where
  dialectic :
    RelationalMode

  dialogue :
    RelationalMode

  polyphony :
    RelationalMode

record PolyphonicConfiguration
       (Voice Content Relation : Set) : Set₁ where
  field
    voices :
      List Voice

    contents :
      List Content

    relations :
      List Relation

    unresolvedVoicesPreserved :
      Set

    relationsAmongRelationsVisible :
      Set

    finalUnityRequired :
      Bool

open PolyphonicConfiguration public

record PolyphonyBoundary : Set where
  constructor mkPolyphonyBoundary
  field
    contradictionCanBeProductive :
      Bool

    dialogueCanTransformParticipants :
      Bool

    multipleVoicesNeedNotCollapse :
      Bool

    oneFinalSynthesisRequired :
      Bool

open PolyphonyBoundary public

canonicalPolyphonyBoundary :
  PolyphonyBoundary
canonicalPolyphonyBoundary =
  mkPolyphonyBoundary
    true
    true
    true
    false

canonicalNoForcedFinalSynthesis :
  oneFinalSynthesisRequired canonicalPolyphonyBoundary
  ≡
  false
canonicalNoForcedFinalSynthesis =
  refl
