{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyConcreteR109RealCompletionToR136Test where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyConcreteR109RealCompletionToR136Exact as Cut

concreteR109RealCompletionToR136Present : Bool
concreteR109RealCompletionToR136Present = Cut.concreteRealCompletionToR136CompilerOwned

concreteR109RealCompletionToR136Present-is-true :
  concreteR109RealCompletionToR136Present ≡ true
concreteR109RealCompletionToR136Present-is-true = refl
