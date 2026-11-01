module DASHI.Physics.WaveOrbitShellGeneratingSeries where

open import Agda.Builtin.Nat using (Nat; zero)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Physics.OrbitShellGeneratingSeries as OSG
open import DASHI.Physics.WaveLiftEvenSubalgebra as WLE

record WaveGradeSlice : Set where
  field
    grade : Nat
    shell1Terms : List OSG.SizeMultiplicity
    shell2Terms : List OSG.SizeMultiplicity

record WaveOrbitShellSeries : Set where
  field
    baseSeries : OSG.OrbitShellSeries
    gradedSlices : List WaveGradeSlice

grade0FromFinite : OSG.OrbitShellSeries → WaveOrbitShellSeries
grade0FromFinite base =
  record
    { baseSeries = base
    ; gradedSlices =
        record
          { grade = zero
          ; shell1Terms = OSG.OrbitShellSeries.shell1Terms base
          ; shell2Terms = OSG.OrbitShellSeries.shell2Terms base
          } ∷ []
    }

prototypeFromWaveLift :
  ∀ {ℓ} {A W : Set ℓ} →
  WLE.Graded A →
  WLE.WaveLift A W →
  OSG.OrbitShellSeries →
  WaveOrbitShellSeries
prototypeFromWaveLift _ _ base = grade0FromFinite base

