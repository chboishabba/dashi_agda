module DASHI.Physics.Closure.PrimeCompatibilityProfile where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import Ontology.Hecke.FactorVecMultiLaneTransport using (pairMode; pairLegal)
open import Ontology.Hecke.ChamberToShiftWitnessBridge as CTSW

------------------------------------------------------------------------
-- Minimal closure-side prime profile:
-- enough to build a prime-address embedding and the fixed-prime illegal-mask /
-- forced-stable witness bridge, without committing to a richer shift-state map.

record PrimeCompatibilityProfile {ℓ : Level} (State : Set ℓ) : Set (lsuc ℓ) where
  field
    compat : State → SSP → Bool

  primeEmbedding : State → FactorVec
  primeEmbedding x =
    mkVec15
      (bitBool (compat x p2))
      (bitBool (compat x p3))
      (bitBool (compat x p5))
      (bitBool (compat x p7))
      (bitBool (compat x p11))
      (bitBool (compat x p13))
      (bitBool (compat x p17))
      (bitBool (compat x p19))
      (bitBool (compat x p23))
      (bitBool (compat x p29))
      (bitBool (compat x p31))
      (bitBool (compat x p41))
      (bitBool (compat x p47))
      (bitBool (compat x p59))
      (bitBool (compat x p71))
    where
    bitBool : Bool → Nat
    bitBool true = suc zero
    bitBool false = zero

  illegalMask : State → SSP → SSP → Bool
  illegalMask x p q = not (pairLegal (pairMode q p) (primeEmbedding x))
    where
    not : Bool → Bool
    not true = false
    not false = true

  witness : State → SSP → CTSW.ShiftWitness
  witness x p =
    record
      { forcedStableEntry = illegalMask x p }

  witnessBridge : CTSW.ChamberToShiftWitnessBridge State
  witnessBridge =
    record
      { illegalMask = illegalMask
      ; witness = witness
      ; witness-sound = λ _ _ _ illegalEq → illegalEq
      }

open PrimeCompatibilityProfile public
