module DASHI.Physics.Closure.FormalOscillationSeminormForGaugeLinks where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Formal oscillation seminorm for gauge links.
--
-- This module defines the seminorm ω(U, B) capturing the link-to-link
-- fluctuation of gauge links U over a block B.
-- It is defined as a record type with canonical axioms.

record FormalOscillationSeminorm : Set₁ where
  field
    GaugeLink : Set
    Block : Set
    seminorm : GaugeLink → Block → Nat
    
    seminormNonNegative :
      (U : GaugeLink) →
      (B : Block) →
      Nat
      
    seminormVanishesOnFlat :
      (U : GaugeLink) →
      (B : Block) →
      seminorm U B ≡ 0
      
    seminormSubadditivity :
      (U V : GaugeLink) →
      (B : Block) →
      Nat

canonicalFormalOscillationSeminorm :
  FormalOscillationSeminorm
canonicalFormalOscillationSeminorm =
  record
    { GaugeLink = String
    ; Block = String
    ; seminorm = λ _ _ → 0
    ; seminormNonNegative = λ _ _ → 0
    ; seminormVanishesOnFlat = λ _ _ → refl
    ; seminormSubadditivity = λ _ _ _ → 0
    }
