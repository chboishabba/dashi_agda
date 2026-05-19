module Ontology.Hecke.ChamberToShiftWitnessBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using (+-mono-≤)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
import Ontology.Hecke.DefectCorrespondenceRepresentation as HD

------------------------------------------------------------------------
-- Minimal bridge surface:
-- for a fixed target prime p, extract only the chamber-side illegal mask and a
-- shift witness whose entries certify forced-stable behavior on the same
-- 15-prime index set.

bit : Bool → Nat
bit true  = suc zero
bit false = zero

record ShiftWitness : Set where
  field
    forcedStableEntry : SSP → Bool

record ChamberToShiftWitnessBridge {ℓ : Level}
                                   (ClosureState : Set ℓ)
                                   : Set (lsuc ℓ) where
  field
    illegalMask : ClosureState → SSP → SSP → Bool
    witness : ClosureState → SSP → ShiftWitness

    witness-sound :
      ∀ x p q →
      illegalMask x p q ≡ true →
      ShiftWitness.forcedStableEntry (witness x p) q ≡ true

illegalMaskVec :
  ∀ {ℓ} {ClosureState : Set ℓ} →
  ChamberToShiftWitnessBridge ClosureState →
  ClosureState → SSP → Vec15 Bool
illegalMaskVec bridge x p =
  mkVec15
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p2)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p3)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p5)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p7)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p11)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p13)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p17)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p19)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p23)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p29)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p31)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p41)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p47)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p59)
    (ChamberToShiftWitnessBridge.illegalMask bridge x p p71)

forcedStableMaskVec :
  ∀ {ℓ} {ClosureState : Set ℓ} →
  ChamberToShiftWitnessBridge ClosureState →
  ClosureState → SSP → Vec15 Bool
forcedStableMaskVec bridge x p =
  mkVec15
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p2)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p3)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p5)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p7)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p11)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p13)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p17)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p19)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p23)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p29)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p31)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p41)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p47)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p59)
    (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) p71)

illegalCount-chamber :
  ∀ {ℓ} {ClosureState : Set ℓ} →
  ChamberToShiftWitnessBridge ClosureState →
  ClosureState → SSP → Nat
illegalCount-chamber bridge x p =
  HD.sum15 (HD.map15 bit (illegalMaskVec bridge x p))

forcedStableCount-hist :
  ∀ {ℓ} {ClosureState : Set ℓ} →
  ChamberToShiftWitnessBridge ClosureState →
  ClosureState → SSP → Nat
forcedStableCount-hist bridge x p =
  HD.sum15 (HD.map15 bit (forcedStableMaskVec bridge x p))

bit≤forcedStable :
  ∀ {ℓ} {ClosureState : Set ℓ} →
  (bridge : ChamberToShiftWitnessBridge ClosureState) →
  (x : ClosureState) → (p q : SSP) →
  bit (ChamberToShiftWitnessBridge.illegalMask bridge x p q)
    ≤
  bit (ShiftWitness.forcedStableEntry (ChamberToShiftWitnessBridge.witness bridge x p) q)
bit≤forcedStable bridge x p q
  with ChamberToShiftWitnessBridge.illegalMask bridge x p q in illegalEq
... | true
  rewrite ChamberToShiftWitnessBridge.witness-sound bridge x p q illegalEq
  = s≤s z≤n
... | false = z≤n

forcedStableTransfer :
  ∀ {ℓ} {ClosureState : Set ℓ} →
  (bridge : ChamberToShiftWitnessBridge ClosureState) →
  ∀ x p →
  illegalCount-chamber bridge x p
    ≤
  forcedStableCount-hist bridge x p
forcedStableTransfer bridge x p =
  NatP.+-mono-≤
    (NatP.+-mono-≤
      (NatP.+-mono-≤
        (NatP.+-mono-≤
          (NatP.+-mono-≤
            (NatP.+-mono-≤
              (NatP.+-mono-≤
                (NatP.+-mono-≤
                  (NatP.+-mono-≤
                    (NatP.+-mono-≤
                      (NatP.+-mono-≤
                        (NatP.+-mono-≤
                          (NatP.+-mono-≤
                            (NatP.+-mono-≤
                              (bit≤forcedStable bridge x p p2)
                              (bit≤forcedStable bridge x p p3))
                            (bit≤forcedStable bridge x p p5))
                          (bit≤forcedStable bridge x p p7))
                        (bit≤forcedStable bridge x p p11))
                      (bit≤forcedStable bridge x p p13))
                    (bit≤forcedStable bridge x p p17))
                  (bit≤forcedStable bridge x p p19))
                (bit≤forcedStable bridge x p p23))
              (bit≤forcedStable bridge x p p29))
            (bit≤forcedStable bridge x p p31))
          (bit≤forcedStable bridge x p p41))
        (bit≤forcedStable bridge x p p47))
      (bit≤forcedStable bridge x p p59))
    (bit≤forcedStable bridge x p p71)
