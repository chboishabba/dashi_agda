module Ontology.BrainComputer.LogicAntifascistBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using ([]; _∷_)

import AntiFascistSystem as AFS
import LogicTlurey as LT
import Ontology.BrainComputer.BrainComputerCrossoverSurface as BCC

------------------------------------------------------------------------
-- Bounded bridge from the early logic/antifascist islands into the current
-- brain/computer carrier.  The antifascist postulates are carried as a
-- boundary, not re-used as new proofs.

stageCode : LT.Stage → Nat
stageCode LT.seed = 0
stageCode LT.counter = 1
stageCode LT.resonance = 2
stageCode LT.overflow = 3

logicCycleComputerState : BCC.ComputerState 4
logicCycleComputerState =
  BCC.computerState
    (stageCode LT.seed
     ∷ stageCode LT.counter
     ∷ stageCode LT.resonance
     ∷ stageCode LT.overflow
     ∷ [])
    4

logicCycleStepCoherent :
  LT.next (LT.next (LT.next (LT.next LT.seed))) ≡ LT.seed
logicCycleStepCoherent = refl

record AntifascistPostulateBoundary : Set₂ where
  field
    Carrier : Set
    entropy : Carrier → Nat
    invertibleBoundary : Set
    entropyPreservationBoundary : Set
    nonCollapseBoundary : Set₁

antifascistPostulateBoundary : AntifascistPostulateBoundary
antifascistPostulateBoundary = record
  { Carrier = AFS.S
  ; entropy = AFS.H
  ; invertibleBoundary = AFS.Invertible
  ; entropyPreservationBoundary =
      (u : AFS.Invertible) (s : AFS.S) →
      AFS.H (AFS.Invertible.U u s) ≡ AFS.H s
  ; nonCollapseBoundary = (u : AFS.Invertible) → Set
  }

record LogicAntifascistBridge : Set₂ where
  field
    logicSeed : LT.Stage
    computerCarrier : BCC.ComputerState 4
    logicCycleCloses : LT.next (LT.next (LT.next (LT.next logicSeed))) ≡ logicSeed
    antifascistBoundary : AntifascistPostulateBoundary

logicAntifascistBridge : LogicAntifascistBridge
logicAntifascistBridge = record
  { logicSeed = LT.seed
  ; computerCarrier = logicCycleComputerState
  ; logicCycleCloses = logicCycleStepCoherent
  ; antifascistBoundary = antifascistPostulateBoundary
  }
