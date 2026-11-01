module DASHI.Philosophy.RetroactiveMeaning where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Later events can revise the meaning assigned to an earlier event without
-- changing the earlier occurrence.  This is retroactive interpretation, not
-- backward causation.

record InterpretiveTimeline
       (Event Meaning Time : Set) : Set₁ where
  field
    event :
      Event

    eventTime :
      Time

    earlierMeaning :
      Meaning

    laterMeaning :
      Meaning

    eventOccurrenceStable :
      Set

    meaningRevisable :
      Set

    backwardCausationClaimed :
      Bool

open InterpretiveTimeline public

record RetroactiveMeaningBoundary : Set where
  constructor mkRetroactiveMeaningBoundary
  field
    pastOccurrenceFixed :
      Bool

    pastMeaningRevisable :
      Bool

    reinterpretationEqualsBackwardCausation :
      Bool

open RetroactiveMeaningBoundary public

canonicalRetroactiveMeaningBoundary :
  RetroactiveMeaningBoundary
canonicalRetroactiveMeaningBoundary =
  mkRetroactiveMeaningBoundary
    true
    true
    false

canonicalNoBackwardCausation :
  reinterpretationEqualsBackwardCausation
    canonicalRetroactiveMeaningBoundary
  ≡
  false
canonicalNoBackwardCausation =
  refl
