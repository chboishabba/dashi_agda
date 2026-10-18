{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223ConcreteR109TailToR136Test where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyEq223ConcreteR109TailToR136Exact as Cut

concretePreferredTailRoutePresent : Bool
concretePreferredTailRoutePresent = Cut.preferredConcreteTailRouteEliminatesArbitraryFiniteSequence

concretePreferredTailRoutePresent-is-true :
  concretePreferredTailRoutePresent ≡ true
concretePreferredTailRoutePresent-is-true = refl
