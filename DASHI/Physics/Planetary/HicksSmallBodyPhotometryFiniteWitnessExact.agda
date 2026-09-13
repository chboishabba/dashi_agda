module DASHI.Physics.Planetary.HicksSmallBodyPhotometryFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Planetary.HicksSmallBodyPhotometryBidiExact as H

record FiniteHicksPhotometryWitness : Set where
  constructor finite-hicks-photometry-witness
  field
    sourceReference : String
    observables : List H.SmallBodyObservable
    fluxSamples : List Nat
    phaseSamples : List Nat
    inferredProperties : List H.PhysicalProperty
    viewingGeometryPaid : Bool
    syntheticLightcurve : Bool
    sourceDatasetReproduced : Bool
    nextExactLeaf : String

open FiniteHicksPhotometryWitness public

finiteHicksPhotometryWitness : FiniteHicksPhotometryWitness
finiteHicksPhotometryWitness = finite-hicks-photometry-witness
  "Hicks small-body publication corpus / repo specific-work owner"
  (H.broadbandFlux ∷ H.colourIndex ∷ H.phaseCurve ∷ H.rotationLightcurve ∷ [])
  (92 ∷ 105 ∷ 118 ∷ 101 ∷ 88 ∷ 96 ∷ [])
  (10 ∷ 20 ∷ 30 ∷ 40 ∷ 50 ∷ 60 ∷ [])
  (H.rotationPeriod ∷ H.albedo ∷ H.surfaceComposition ∷ [])
  false
  true
  false
  "select one source-exact Hicks lightcurve/photometry object, add viewing geometry/calibration and reproduce a bounded rotation/phase inference"

finiteWitnessShowsMultiSampleInferenceShape : Bool
finiteWitnessShowsMultiSampleInferenceShape = true

finiteWitnessUniquelyDeterminesShape : Bool
finiteWitnessUniquelyDeterminesShape = false

finiteWitnessIsSourceDatasetReplication : Bool
finiteWitnessIsSourceDatasetReplication = false
