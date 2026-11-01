module DASHI.Physics.Closure.Validation.RootSystemB4OrbitMergeTheorem where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false)
open import Data.Vec using (_∷_; [])

open import DASHI.Physics.RootSystemB4Carrier as B4
open import DASHI.Physics.RootSystemB4WeylAction as W
open import DASHI.Physics.Closure.Validation.RootSystemB4OrbitStabilizerComparison as B4OSC

merge6and2-generator : W.WeylB4
merge6and2-generator =
  record
    { perm = W.p1023
    ; flips = true ∷ false ∷ true ∷ true ∷ []
    }

record RootSystemB4OrbitMergeTheorem : Set where
  field
    mergedShell1Representative :
      W.actWeyl
        merge6and2-generator
        (B4OSC.shiftRepresentative B4OSC.shiftShell1-2)
      ≡
      B4OSC.shiftRepresentative B4OSC.shiftShell1-6
    shell1MergedOrbitCardinality :
      B4OSC.b4OrbitSize B4OSC.shiftShell1-6
      ≡
      B4OSC.shiftOrbitSize B4OSC.shiftShell1-6
      + B4OSC.shiftOrbitSize B4OSC.shiftShell1-2
    shell1MergedStabilizerCardinality :
      B4OSC.b4StabilizerSize B4OSC.shiftShell1-6
      ≡
      B4OSC.b4StabilizerSize B4OSC.shiftShell1-2

canonicalRootSystemB4OrbitMergeTheorem :
  RootSystemB4OrbitMergeTheorem
canonicalRootSystemB4OrbitMergeTheorem =
  record
    { mergedShell1Representative = refl
    ; shell1MergedOrbitCardinality = refl
    ; shell1MergedStabilizerCardinality = refl
    }
