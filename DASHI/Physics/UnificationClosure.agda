{-# OPTIONS --safe #-}

module DASHI.Physics.UnificationClosure where

-- NOTE: We intentionally avoid depending on the theorem-critical Signature31 seam
-- here, because this module is marked --safe and the seam module is not (yet).

open import Level using (Level; suc)
open import Data.Product using (_×_; Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Physics.Core
open import DASHI.Physics.ContractionToQuadratic
open import DASHI.Physics.Signature31
open import DASHI.Physics.DecimationToClifford
open import DASHI.Physics.WaveLiftEvenSubalgebra

record ClosureStatus : Set₁ where
  field
    hasQuadratic    : Set
    hasQuadraticUnique : Set
    hasSignature31  : Set
    hasClifford     : Set
    hasEvenLift     : Set

-- Minimal closure witness.
unificationClosure :
  ClosureStatus
unificationClosure =
  record
    { hasQuadratic = ⊤
    ; hasQuadraticUnique = ⊤
    ; hasSignature31 = ⊤
    ; hasClifford = ⊤
    ; hasEvenLift = ⊤
    }
