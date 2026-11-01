module DASHI.Physics.OrbitShellGeneratingSeries where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe using (Maybe)

open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR

record SizeMultiplicity : Set where
  field
    size : Nat
    multiplicity : Nat

record OrbitShellSeries : Set where
  field
    orientationTag : Maybe Nat
    shell1Terms : List SizeMultiplicity
    shell2Terms : List SizeMultiplicity

succ : Nat → Nat
succ n = suc n

compressSortedAcc : Nat → Nat → List Nat → List SizeMultiplicity
compressSortedAcc current count [] =
  record { size = current ; multiplicity = count } ∷ []
compressSortedAcc current count (x ∷ xs) with RPR.natEq current x
... | true = compressSortedAcc current (succ count) xs
... | false =
  record { size = current ; multiplicity = count } ∷
  compressSortedAcc x 1 xs

compressSorted : List Nat → List SizeMultiplicity
compressSorted [] = []
compressSorted (x ∷ xs) = compressSortedAcc x 1 xs

seriesFromRaw : Maybe Nat → List Nat → List Nat → OrbitShellSeries
seriesFromRaw orientation shell1 shell2 =
  record
    { orientationTag = orientation
    ; shell1Terms = compressSorted shell1
    ; shell2Terms = compressSorted shell2
    }

seriesFromObservation : RPR.RealizationObservation → OrbitShellSeries
seriesFromObservation obs =
  seriesFromRaw
    (RPR.RealizationObservation.orientationTag obs)
    (RPR.RealizationObservation.shell1Profile obs)
    (RPR.RealizationObservation.shell2Profile obs)
