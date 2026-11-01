module Ontology.Brain.BrainVisualFormConstantSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using
  (BrainState; BrainObservable; observeState; stateOf)

------------------------------------------------------------------------
-- Bounded visual-form-constant owner surface for the local brain lane.
-- This is intentionally theorem-thin and non-claiming: it packages a
-- small log-polar/open-loop geometry vocabulary on top of the current
-- local carrier without claiming full V1/V2 recovery.

data BrainVisualFormConstant : Set where
  lattice tunnel spiral cobweb : BrainVisualFormConstant

record BrainLogPolarGeometry : Set where
  constructor brainLogPolarGeometry
  field
    radialRing : Nat
    angularSector : Nat
    openLoop : Bool

geometryOfObservable : BrainObservable → BrainLogPolarGeometry
geometryOfObservable obs =
  brainLogPolarGeometry
    (BrainObservable.packetWidth obs)
    (BrainObservable.layerTag obs)
    (BrainObservable.activeFlag obs)

geometryOfState : ∀ {n} → BrainState n → BrainLogPolarGeometry
geometryOfState st = geometryOfObservable (observeState st)

classifyGeometry : BrainLogPolarGeometry → BrainVisualFormConstant
classifyGeometry geo with BrainLogPolarGeometry.openLoop geo | BrainLogPolarGeometry.radialRing geo
... | false | zero = cobweb
... | false | suc _ = lattice
... | true | zero = tunnel
... | true | suc _ = spiral

classifyState : ∀ {n} → BrainState n → BrainVisualFormConstant
classifyState st = classifyGeometry (geometryOfState st)

geometry-width :
  ∀ {n} (st : BrainState n) →
  BrainLogPolarGeometry.radialRing (geometryOfState st) ≡ n
geometry-width st = refl

geometry-layer :
  ∀ {n} (st : BrainState n) →
  BrainLogPolarGeometry.angularSector (geometryOfState st) ≡ BrainObservable.layerTag (observeState st)
geometry-layer st = refl

geometry-openLoop :
  ∀ {n} (st : BrainState n) →
  BrainLogPolarGeometry.openLoop (geometryOfState st) ≡ BrainObservable.activeFlag (observeState st)
geometry-openLoop st = refl

inactive-zero-classifies-cobweb :
  ∀ geo →
  BrainLogPolarGeometry.openLoop geo ≡ false →
  BrainLogPolarGeometry.radialRing geo ≡ zero →
  classifyGeometry geo ≡ cobweb
inactive-zero-classifies-cobweb geo refl refl = refl

inactive-suc-classifies-lattice :
  ∀ geo →
  BrainLogPolarGeometry.openLoop geo ≡ false →
  ∀ {n} →
  BrainLogPolarGeometry.radialRing geo ≡ suc n →
  classifyGeometry geo ≡ lattice
inactive-suc-classifies-lattice geo refl refl = refl

active-zero-classifies-tunnel :
  ∀ geo →
  BrainLogPolarGeometry.openLoop geo ≡ true →
  BrainLogPolarGeometry.radialRing geo ≡ zero →
  classifyGeometry geo ≡ tunnel
active-zero-classifies-tunnel geo refl refl = refl

active-suc-classifies-spiral :
  ∀ geo →
  BrainLogPolarGeometry.openLoop geo ≡ true →
  ∀ {n} →
  BrainLogPolarGeometry.radialRing geo ≡ suc n →
  classifyGeometry geo ≡ spiral
active-suc-classifies-spiral geo refl refl = refl

stateOf-zero-classification :
  ∀ (xs : Vec Nat zero) →
  classifyState (stateOf xs) ≡ cobweb
stateOf-zero-classification xs = refl

stateOf-suc-classification :
  ∀ {n} (xs : Vec Nat (suc n)) →
  classifyState (stateOf xs) ≡ spiral
stateOf-suc-classification xs = refl

record BrainVisualFormConstantSurface : Set₁ where
  field
    Geometry : Set
    FormConstant : Set
    geometry : ∀ {n} → BrainState n → Geometry
    classify : Geometry → FormConstant

brainVisualFormConstantSurface : BrainVisualFormConstantSurface
brainVisualFormConstantSurface = record
  { Geometry = BrainLogPolarGeometry
  ; FormConstant = BrainVisualFormConstant
  ; geometry = geometryOfState
  ; classify = classifyGeometry
  }
