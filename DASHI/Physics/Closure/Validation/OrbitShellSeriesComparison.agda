module DASHI.Physics.Closure.Validation.OrbitShellSeriesComparison where

open import Agda.Builtin.Nat using (Nat)
open import Data.Bool using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR
open import DASHI.Physics.OrbitShellGeneratingSeries as OSG

data OrbitShellSeriesVerdict : Set where
  exactSeriesMatch : OrbitShellSeriesVerdict
  shellOnlySeriesMatch : OrbitShellSeriesVerdict
  seriesMismatch : OrbitShellSeriesVerdict

record OrbitShellSeriesComparison : Set where
  field
    reference : OSG.OrbitShellSeries
    candidate : OSG.OrbitShellSeries
    shell1Matches : Bool
    shell2Matches : Bool
    orientationAvailable : Bool
    orientationMatches : Bool

sizeMultiplicityEq : OSG.SizeMultiplicity → OSG.SizeMultiplicity → Bool
sizeMultiplicityEq x y with RPR.natEq (OSG.SizeMultiplicity.size x) (OSG.SizeMultiplicity.size y)
... | false = false
... | true = RPR.natEq (OSG.SizeMultiplicity.multiplicity x) (OSG.SizeMultiplicity.multiplicity y)

listSizeMultiplicityEq : List OSG.SizeMultiplicity → List OSG.SizeMultiplicity → Bool
listSizeMultiplicityEq [] [] = true
listSizeMultiplicityEq [] (_ ∷ _) = false
listSizeMultiplicityEq (_ ∷ _) [] = false
listSizeMultiplicityEq (x ∷ xs) (y ∷ ys) with sizeMultiplicityEq x y
... | true = listSizeMultiplicityEq xs ys
... | false = false

seriesMaybeNatAvailable : Maybe Nat → Maybe Nat → Bool
seriesMaybeNatAvailable (just _) (just _) = true
seriesMaybeNatAvailable _ _ = false

seriesMaybeNatMatches : Maybe Nat → Maybe Nat → Bool
seriesMaybeNatMatches (just x) (just y) = RPR.natEq x y
seriesMaybeNatMatches _ _ = false

compareSeries :
  OSG.OrbitShellSeries → OSG.OrbitShellSeries → OrbitShellSeriesComparison
compareSeries reference candidate =
  record
    { reference = reference
    ; candidate = candidate
    ; shell1Matches =
        listSizeMultiplicityEq
          (OSG.OrbitShellSeries.shell1Terms reference)
          (OSG.OrbitShellSeries.shell1Terms candidate)
    ; shell2Matches =
        listSizeMultiplicityEq
          (OSG.OrbitShellSeries.shell2Terms reference)
          (OSG.OrbitShellSeries.shell2Terms candidate)
    ; orientationAvailable =
        seriesMaybeNatAvailable
          (OSG.OrbitShellSeries.orientationTag reference)
          (OSG.OrbitShellSeries.orientationTag candidate)
    ; orientationMatches =
        seriesMaybeNatMatches
          (OSG.OrbitShellSeries.orientationTag reference)
          (OSG.OrbitShellSeries.orientationTag candidate)
    }

classifySeries : OrbitShellSeriesComparison → OrbitShellSeriesVerdict
classifySeries cmp with OrbitShellSeriesComparison.shell1Matches cmp
... | false = seriesMismatch
... | true with OrbitShellSeriesComparison.shell2Matches cmp
... | false = seriesMismatch
... | true with OrbitShellSeriesComparison.orientationAvailable cmp
... | true with OrbitShellSeriesComparison.orientationMatches cmp
... | true = exactSeriesMatch
... | false = shellOnlySeriesMatch
classifySeries cmp | true | true | false = shellOnlySeriesMatch
