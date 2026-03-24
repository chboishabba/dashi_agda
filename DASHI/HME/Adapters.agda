module DASHI.HME.Adapters where

open import Agda.Builtin.Nat using (Nat)
open import Data.List using (List)

open import DASHI.HME.Path using (Path)

------------------------------------------------------------------------
-- Thin interface records: keep external surfaces separate.
------------------------------------------------------------------------

record SLAdapter (Doc State : Set) : Set₁ where
  field
    extract : Doc → List State
    encode : State → Set

record CaseyAdapter {S : Set} (step : S → S) : Set₁ where
  field
    propose : List (Path step)
    score : Path step → Nat
    select : List Nat → Nat

record ZelphAdapter {S : Set} (step : S → S) : Set₁ where
  field
    Fact : Set
    export : Path step → List Fact

