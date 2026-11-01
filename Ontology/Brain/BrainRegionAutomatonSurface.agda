module Ontology.Brain.BrainRegionAutomatonSurface where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import Ontology.Brain.BrainVocabularySurface as BVS

------------------------------------------------------------------------
-- Minimal local brain-region automaton surface.
-- This is intentionally theorem-thin and non-claiming: it provides a typed
-- region/lens/motif vocabulary around the notebook-confirmed theme without
-- claiming neuroscience completeness.

data BrainRegion : Set where
  S3 S4 mu : BrainRegion

data RegionLens : Set where
  s3Lens s4Lens muLens : RegionLens

data RegionMotif : Set where
  M1 M2 M3 M4 M5 M6 M7 M8 M9 : RegionMotif

motifIndex : RegionMotif → Nat
motifIndex M1 = 1
motifIndex M2 = 2
motifIndex M3 = 3
motifIndex M4 = 4
motifIndex M5 = 5
motifIndex M6 = 6
motifIndex M7 = 7
motifIndex M8 = 8
motifIndex M9 = 9

lensOf : BrainRegion → RegionLens
lensOf S3 = s3Lens
lensOf S4 = s4Lens
lensOf mu = muLens

motifOf : BrainRegion → RegionMotif
motifOf S3 = M3
motifOf S4 = M4
motifOf mu = M1

stepRegion : BrainRegion → BrainRegion
stepRegion S3 = S4
stepRegion S4 = mu
stepRegion mu = mu

record RegionCorrespondence : Set where
  constructor regionCorrespondence
  field
    region : BrainRegion
    lens : RegionLens
    motif : RegionMotif

correspondenceOf : BrainRegion → RegionCorrespondence
correspondenceOf r = regionCorrespondence r (lensOf r) (motifOf r)

record BrainRegionState (n : Nat) : Set where
  constructor brainRegionState
  field
    carrier : BVS.BrainState n
    activeRegion : BrainRegion

record BrainRegionObservable : Set where
  constructor brainRegionObservable
  field
    width : Nat
    region : BrainRegion
    lens : RegionLens
    motif : RegionMotif
    activeFlag : BVS.BrainObservable

regionStateOf : ∀ {n} → BVS.BrainState n → BrainRegion → BrainRegionState n
regionStateOf st r = brainRegionState st r

observeRegionState : ∀ {n} → BrainRegionState n → BrainRegionObservable
observeRegionState {n} st =
  brainRegionObservable
    n
    (BrainRegionState.activeRegion st)
    (lensOf (BrainRegionState.activeRegion st))
    (motifOf (BrainRegionState.activeRegion st))
    (BVS.observeState (BrainRegionState.carrier st))

correspondence-lens-exact :
  (r : BrainRegion) →
  RegionCorrespondence.lens (correspondenceOf r) ≡ lensOf r
correspondence-lens-exact r = refl

correspondence-motif-exact :
  (r : BrainRegion) →
  RegionCorrespondence.motif (correspondenceOf r) ≡ motifOf r
correspondence-motif-exact r = refl

mu-fixed :
  stepRegion mu ≡ mu
mu-fixed = refl

step²-to-mu :
  (r : BrainRegion) →
  stepRegion (stepRegion r) ≡ mu
step²-to-mu S3 = refl
step²-to-mu S4 = refl
step²-to-mu mu = refl

observeRegionState-width :
  ∀ {n} (st : BrainRegionState n) →
  BrainRegionObservable.width (observeRegionState st) ≡ n
observeRegionState-width st = refl

observeRegionState-lens :
  ∀ {n} (st : BrainRegionState n) →
  BrainRegionObservable.lens (observeRegionState st)
    ≡ lensOf (BrainRegionState.activeRegion st)
observeRegionState-lens st = refl

observeRegionState-motif :
  ∀ {n} (st : BrainRegionState n) →
  BrainRegionObservable.motif (observeRegionState st)
    ≡ motifOf (BrainRegionState.activeRegion st)
observeRegionState-motif st = refl

record BrainRegionAutomatonSurface : Set₂ where
  field
    vocabulary : BVS.BrainVocabularySurface
    RegionState' : Nat → Set
    RegionObservable' : Set
    correspondence : BrainRegion → RegionCorrespondence
    step : BrainRegion → BrainRegion
    observe : ∀ {n} → RegionState' n → RegionObservable'

    muFixedLaw : step mu ≡ mu
    step²ToMuLaw : (r : BrainRegion) → step (step r) ≡ mu
    correspondenceLensLaw :
      (r : BrainRegion) →
      RegionCorrespondence.lens (correspondence r) ≡ lensOf r
    correspondenceMotifLaw :
      (r : BrainRegion) →
      RegionCorrespondence.motif (correspondence r) ≡ motifOf r

brainRegionAutomatonSurface : BrainRegionAutomatonSurface
brainRegionAutomatonSurface = record
  { vocabulary = BVS.brainVocabularySurface
  ; RegionState' = BrainRegionState
  ; RegionObservable' = BrainRegionObservable
  ; correspondence = correspondenceOf
  ; step = stepRegion
  ; observe = observeRegionState
  ; muFixedLaw = mu-fixed
  ; step²ToMuLaw = step²-to-mu
  ; correspondenceLensLaw = correspondence-lens-exact
  ; correspondenceMotifLaw = correspondence-motif-exact
  }
