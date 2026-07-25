module DASHI.Physics.Closure.NSPeriodicNearConvolutionMultiplicity where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal convolution-pair multiplicity.
------------------------------------------------------------------------

convolutionPairs :
  ∀ {A B : Set} → List A → List B → List (Cube.Pair A B)
convolutionPairs = Cube.cartesian

convolutionPairCount :
  ∀ {A B : Set} (left : List A) (right : List B) →
  Cube.length (convolutionPairs left right) ≡
  Cube.length left * Cube.length right
convolutionPairCount = Cube.cartesianLength

convolutionPairsNoDuplicates :
  ∀ {A B : Set} {left : List A} {right : List B} →
  Cube.NoDuplicates left →
  Cube.NoDuplicates right →
  Cube.NoDuplicates (convolutionPairs left right)
convolutionPairsNoDuplicates = Cube.cartesianNoDuplicates

nearConvolutionMultiplicityLevel : ProofLevel
nearConvolutionMultiplicityLevel = machineChecked
