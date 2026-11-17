{-# OPTIONS --safe #-}
module DASHI.AnimalCommunication.PoseMDL where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _<_; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- A pose ribbon is deliberately abstract: a concrete instance may carry
-- canonical keypoints, confidence, masks, coarse volume, flow, or audio.
-- The deterministic boundary begins only after a PoseRibbon is supplied.
record PoseMDLSpec : Set₁ where
  field
    PoseRibbon Dictionary MotifProgram Summary : Set

    canonicalize : PoseRibbon → PoseRibbon
    compile      : Dictionary → PoseRibbon → MotifProgram
    publish      : MotifProgram → Summary

    dictionaryCost : Dictionary → Nat
    parseCost      : Dictionary → PoseRibbon → MotifProgram → Nat
    residualCost   : PoseRibbon → MotifProgram → Nat
    totalCost      : Dictionary → PoseRibbon → MotifProgram → Nat

    totalCost-law :
      ∀ D P M →
      totalCost D P M ≡
      dictionaryCost D + parseCost D P M + residualCost P M

open PoseMDLSpec public

-- A candidate motif/dictionary refinement is justified only when it lowers
-- the complete description length, including its own dictionary cost.
record MDLImprovement (S : PoseMDLSpec) : Set where
  open PoseMDLSpec S
  field
    pose       : PoseRibbon
    baseline   : Dictionary
    candidate  : Dictionary
    oldProgram : MotifProgram
    newProgram : MotifProgram

    old-is-compiled : compile baseline (canonicalize pose) ≡ oldProgram
    new-is-compiled : compile candidate (canonicalize pose) ≡ newProgram
    strictly-shorter :
      totalCost candidate (canonicalize pose) newProgram <
      totalCost baseline  (canonicalize pose) oldProgram

open MDLImprovement public

-- Residuals are first-class evidence.  A motif parse is not accepted merely
-- because it returns a symbol; its unexplained remainder must fit a declared
-- budget.
record ResidualBounded (S : PoseMDLSpec) (budget : Nat) : Set where
  open PoseMDLSpec S
  field
    pose       : PoseRibbon
    dictionary : Dictionary
    program    : MotifProgram
    compiled   : compile dictionary (canonicalize pose) ≡ program
    residual≤budget : residualCost (canonicalize pose) program ≤ budget

open ResidualBounded public

-- A reusable deterministic receipt for pose -> motif program -> public
-- summary.  No semantic truth claim is made here: Summary is merely the
-- bounded output selected by the concrete instance.
record PoseMDLReceipt (S : PoseMDLSpec) (budget : Nat) : Set where
  open PoseMDLSpec S
  field
    pose       : PoseRibbon
    dictionary : Dictionary
    program    : MotifProgram
    summary    : Summary

    compiled : compile dictionary (canonicalize pose) ≡ program
    released : publish program ≡ summary
    residual≤budget : residualCost (canonicalize pose) program ≤ budget

open PoseMDLReceipt public
