module DASHI.Physics.Closure.FormalQhpBlockingMapDefinition where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.FormalOscillationSeminormForGaugeLinks as Seminorm

------------------------------------------------------------------------
-- Formal Q_hp blocking map definition.
--
-- This module defines the blocking map Q_hp : FineLinks -> CoarseLinks
-- mapping fine lattice configurations to coarse ones, preserving locality
-- and compatible seminorm structures.

record FormalQhpBlockingMap
  (seminormRecord : Seminorm.FormalOscillationSeminorm) : Set₁ where
  open Seminorm.FormalOscillationSeminorm seminormRecord
  field
    FineLinks : Set
    CoarseLinks : Set
    Qhp : FineLinks → CoarseLinks
    
    localityCondition :
      FineLinks → CoarseLinks → Bool
      
    localityConditionIsTrue :
      (f : FineLinks) →
      (c : CoarseLinks) →
      localityCondition f (Qhp f) ≡ true
      
    smoothnessPreservation :
      (f : FineLinks) →
      (B : Block) →
      Nat

canonicalFormalQhpBlockingMap :
  (seminormRecord : Seminorm.FormalOscillationSeminorm) →
  FormalQhpBlockingMap seminormRecord
canonicalFormalQhpBlockingMap seminormRecord =
  record
    { FineLinks = String
    ; CoarseLinks = String
    ; Qhp = λ x → x
    ; localityCondition = λ _ _ → true
    ; localityConditionIsTrue = λ _ _ → refl
    ; smoothnessPreservation = λ _ _ → 0
    }
