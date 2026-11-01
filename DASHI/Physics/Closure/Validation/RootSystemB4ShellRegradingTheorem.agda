module DASHI.Physics.Closure.Validation.RootSystemB4ShellRegradingTheorem where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ)
open import Data.Integer using (_≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using ([]; _∷_)
open import Relation.Nullary using (yes; no)

open import DASHI.Physics.RootSystemB4Carrier as B4
open import DASHI.Physics.Closure.Validation.RootSystemB4OrbitStabilizerComparison as B4OSC

data RootSystemB4ShellIndex : Set where
  b4-shell1 : RootSystemB4ShellIndex
  b4-shell2 : RootSystemB4ShellIndex
  outside-b4-root-shells : RootSystemB4ShellIndex

nonZeroWeight : ℤ → Nat
nonZeroWeight x with x ≟ B4.z
... | yes _ = zero
... | no _ = suc zero

quadraticWeight : B4.B4Point → Nat
quadraticWeight (a ∷ b ∷ c ∷ d ∷ []) =
  nonZeroWeight a
  + nonZeroWeight b
  + nonZeroWeight c
  + nonZeroWeight d

shellIndexFromQuadraticWeight : Nat → RootSystemB4ShellIndex
shellIndexFromQuadraticWeight (suc zero) = b4-shell1
shellIndexFromQuadraticWeight (suc (suc zero)) = b4-shell2
shellIndexFromQuadraticWeight _ = outside-b4-root-shells

quadraticWeightOfShiftRepresentative :
  B4OSC.ShiftShellClass → Nat
quadraticWeightOfShiftRepresentative c =
  quadraticWeight (B4OSC.shiftRepresentative c)

b4ShellIndexOfShiftRepresentative :
  B4OSC.ShiftShellClass → RootSystemB4ShellIndex
b4ShellIndexOfShiftRepresentative c =
  shellIndexFromQuadraticWeight (quadraticWeightOfShiftRepresentative c)

record RootSystemB4ShellRegradingTheorem : Set where
  field
    shell1SpatialClassHasQuadraticWeight1 :
      quadraticWeightOfShiftRepresentative B4OSC.shiftShell1-6 ≡ 1
    shell1TimelikeClassHasQuadraticWeight1 :
      quadraticWeightOfShiftRepresentative B4OSC.shiftShell1-2 ≡ 1
    shell2TwelveClassHasQuadraticWeight2 :
      quadraticWeightOfShiftRepresentative B4OSC.shiftShell2-12 ≡ 2
    shell1TwentyFourClassHasQuadraticWeight3 :
      quadraticWeightOfShiftRepresentative B4OSC.shiftShell1-24 ≡ 3
    shell2SixteenClassHasQuadraticWeight4 :
      quadraticWeightOfShiftRepresentative B4OSC.shiftShell2-16 ≡ 4
    shell1SpatialClassStaysVisible :
      b4ShellIndexOfShiftRepresentative B4OSC.shiftShell1-6 ≡ b4-shell1
    shell1TimelikeClassStaysVisible :
      b4ShellIndexOfShiftRepresentative B4OSC.shiftShell1-2 ≡ b4-shell1
    shell2TwelveClassRegradesToB4Shell2 :
      b4ShellIndexOfShiftRepresentative B4OSC.shiftShell2-12 ≡ b4-shell2
    shell1TwentyFourClassLeavesB4RootShells :
      b4ShellIndexOfShiftRepresentative B4OSC.shiftShell1-24
      ≡ outside-b4-root-shells
    shell2SixteenClassLeavesB4RootShells :
      b4ShellIndexOfShiftRepresentative B4OSC.shiftShell2-16
      ≡ outside-b4-root-shells

canonicalRootSystemB4ShellRegradingTheorem :
  RootSystemB4ShellRegradingTheorem
canonicalRootSystemB4ShellRegradingTheorem =
  record
    { shell1SpatialClassHasQuadraticWeight1 = refl
    ; shell1TimelikeClassHasQuadraticWeight1 = refl
    ; shell2TwelveClassHasQuadraticWeight2 = refl
    ; shell1TwentyFourClassHasQuadraticWeight3 = refl
    ; shell2SixteenClassHasQuadraticWeight4 = refl
    ; shell1SpatialClassStaysVisible = refl
    ; shell1TimelikeClassStaysVisible = refl
    ; shell2TwelveClassRegradesToB4Shell2 = refl
    ; shell1TwentyFourClassLeavesB4RootShells = refl
    ; shell2SixteenClassLeavesB4RootShells = refl
    }
