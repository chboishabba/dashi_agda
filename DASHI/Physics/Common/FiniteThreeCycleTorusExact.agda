module DASHI.Physics.Common.FiniteThreeCycleTorusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- DASHI CONTRIBUTION
-- Give the exact finite translation algebra of the two-dimensional
-- three-cycle torus.  Each coordinate translation has order three, the two
-- coordinate translations commute, and a distinguished completion channel is
-- fixed.  Pullback on fields is the exact index-permutation ingredient of a
-- wreath-style action.  No continuous-torus or physical theorem is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

data Residue3 : Set where
  residueMinus : Residue3
  residueZero : Residue3
  residuePlus : Residue3

next3 : Residue3 → Residue3
next3 residueMinus = residueZero
next3 residueZero = residuePlus
next3 residuePlus = residueMinus

next3Cubed : ∀ residue → next3 (next3 (next3 residue)) ≡ residue
next3Cubed residueMinus = refl
next3Cubed residueZero = refl
next3Cubed residuePlus = refl

record Torus3x3 : Set where
  constructor torusPoint
  field
    firstCoordinate : Residue3
    secondCoordinate : Residue3

open Torus3x3 public

translateFirst : Torus3x3 → Torus3x3
translateFirst (torusPoint first second) = torusPoint (next3 first) second

translateSecond : Torus3x3 → Torus3x3
translateSecond (torusPoint first second) = torusPoint first (next3 second)

translateFirstCubed :
  ∀ point → translateFirst (translateFirst (translateFirst point)) ≡ point
translateFirstCubed (torusPoint first second)
  rewrite next3Cubed first = refl

translateSecondCubed :
  ∀ point → translateSecond (translateSecond (translateSecond point)) ≡ point
translateSecondCubed (torusPoint first second)
  rewrite next3Cubed second = refl

translationsCommute :
  ∀ point → translateFirst (translateSecond point)
  ≡ translateSecond (translateFirst point)
translationsCommute (torusPoint first second) = refl

data CompletedTorusChannel : Set where
  ordinaryTorusChannel : Torus3x3 → CompletedTorusChannel
  completionChannel : CompletedTorusChannel

completedTranslateFirst : CompletedTorusChannel → CompletedTorusChannel
completedTranslateFirst (ordinaryTorusChannel point) =
  ordinaryTorusChannel (translateFirst point)
completedTranslateFirst completionChannel = completionChannel

completedTranslateSecond : CompletedTorusChannel → CompletedTorusChannel
completedTranslateSecond (ordinaryTorusChannel point) =
  ordinaryTorusChannel (translateSecond point)
completedTranslateSecond completionChannel = completionChannel

completionFixedByFirstTranslation :
  completedTranslateFirst completionChannel ≡ completionChannel
completionFixedByFirstTranslation = refl

completionFixedBySecondTranslation :
  completedTranslateSecond completionChannel ≡ completionChannel
completionFixedBySecondTranslation = refl

Field : Set → Set
Field State = CompletedTorusChannel → State

pullbackFirst : ∀ {State : Set} → Field State → Field State
pullbackFirst fld channel = fld (completedTranslateFirst channel)

pullbackSecond : ∀ {State : Set} → Field State → Field State
pullbackSecond fld channel = fld (completedTranslateSecond channel)

pullbackFirstCubedAt :
  ∀ {State : Set} (fld : Field State) channel →
  pullbackFirst (pullbackFirst (pullbackFirst fld)) channel ≡ fld channel
pullbackFirstCubedAt fld (ordinaryTorusChannel point) =
  cong fld (cong ordinaryTorusChannel (translateFirstCubed point))
pullbackFirstCubedAt fld completionChannel = refl

pullbackSecondCubedAt :
  ∀ {State : Set} (fld : Field State) channel →
  pullbackSecond (pullbackSecond (pullbackSecond fld)) channel ≡ fld channel
pullbackSecondCubedAt fld (ordinaryTorusChannel point) =
  cong fld (cong ordinaryTorusChannel (translateSecondCubed point))
pullbackSecondCubedAt fld completionChannel = refl

pullbacksCommuteAt :
  ∀ {State : Set} (fld : Field State) channel →
  pullbackFirst (pullbackSecond fld) channel
  ≡ pullbackSecond (pullbackFirst fld) channel
pullbacksCommuteAt fld (ordinaryTorusChannel point) =
  cong fld (cong ordinaryTorusChannel (translationsCommute point))
pullbacksCommuteAt fld completionChannel = refl

record FiniteTorusBoundary : Set₁ where
  constructor finiteTorusBoundary
  field
    completedTorusIsContinuousTorus : Set
    completedTorusIsNotContinuousTorus :
      completedTorusIsContinuousTorus → Set
    fixedCompletionChannelIsAutomaticallyInvariantUnderExternalAction : Set
    fixedCompletionChannelIsNotAutomaticallyInvariantUnderExternalAction :
      fixedCompletionChannelIsAutomaticallyInvariantUnderExternalAction → Set

canonicalFiniteTorusBoundary : FiniteTorusBoundary
canonicalFiniteTorusBoundary =
  finiteTorusBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
