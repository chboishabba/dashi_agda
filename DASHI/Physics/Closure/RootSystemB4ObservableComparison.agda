module DASHI.Physics.Closure.RootSystemB4ObservableComparison where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.OrbitProfileComputedRootSystemB4 as ORB4
open import DASHI.Physics.Closure.Validation.RootSystemB4OrbitStabilizerComparison as B4OSC
open import DASHI.Physics.Closure.Validation.RootSystemB4OrbitMergeTheorem as B4OM
open import DASHI.Physics.Closure.Validation.RootSystemB4ShellRegradingTheorem as B4SR
open import DASHI.Physics.Closure.Validation.RootSystemB4OrientationSignatureBridge as B4OSB

record B4ObservableComparison : Setω where
  field
    shell1-24-comparison : B4OSC.OrbitStabilizerComparison
    shell1-6-comparison : B4OSC.OrbitStabilizerComparison
    shell1-2-comparison : B4OSC.OrbitStabilizerComparison
    shell2-16-comparison : B4OSC.OrbitStabilizerComparison
    shell2-12-comparison : B4OSC.OrbitStabilizerComparison
    orbitMerge : B4OM.RootSystemB4OrbitMergeTheorem
    shellRegrading : B4SR.RootSystemB4ShellRegradingTheorem
    rawShiftShell1Mismatch :
      OPD.shell1_p3_q1 ≡ ORB4.b4-shell1-computed → ⊥
    rawShiftShell2Mismatch :
      OPD.shell2_p3_q1 ≡ ORB4.b4-shell2-computed → ⊥
    signatureCompatibility :
      B4OSB.b4OrientationJustified ≡ B4OSB.b4OrientationJustified

mkB4ObservableComparison :
  B4OSC.OrbitStabilizerComparison →
  B4OSC.OrbitStabilizerComparison →
  B4OSC.OrbitStabilizerComparison →
  B4OSC.OrbitStabilizerComparison →
  B4OSC.OrbitStabilizerComparison →
  B4OM.RootSystemB4OrbitMergeTheorem →
  B4SR.RootSystemB4ShellRegradingTheorem →
  (OPD.shell1_p3_q1 ≡ ORB4.b4-shell1-computed → ⊥) →
  (OPD.shell2_p3_q1 ≡ ORB4.b4-shell2-computed → ⊥) →
  B4OSB.b4OrientationJustified ≡ B4OSB.b4OrientationJustified →
  B4ObservableComparison
mkB4ObservableComparison
  shell1-24
  shell1-6
  shell1-2
  shell2-16
  shell2-12
  orbitMerge
  shellRegrading
  rawShiftShell1Mismatch
  rawShiftShell2Mismatch
  signatureCompatibility =
  record
    { shell1-24-comparison = shell1-24
    ; shell1-6-comparison = shell1-6
    ; shell1-2-comparison = shell1-2
    ; shell2-16-comparison = shell2-16
    ; shell2-12-comparison = shell2-12
    ; orbitMerge = orbitMerge
    ; shellRegrading = shellRegrading
    ; rawShiftShell1Mismatch = rawShiftShell1Mismatch
    ; rawShiftShell2Mismatch = rawShiftShell2Mismatch
    ; signatureCompatibility = signatureCompatibility
    }

canonicalB4ObservableComparison : B4ObservableComparison
canonicalB4ObservableComparison =
  mkB4ObservableComparison
    (B4OSC.comparison B4OSC.shiftShell1-24)
    (B4OSC.comparison B4OSC.shiftShell1-6)
    (B4OSC.comparison B4OSC.shiftShell1-2)
    (B4OSC.comparison B4OSC.shiftShell2-16)
    (B4OSC.comparison B4OSC.shiftShell2-12)
    B4OM.canonicalRootSystemB4OrbitMergeTheorem
    B4SR.canonicalRootSystemB4ShellRegradingTheorem
    (λ ())
    (λ ())
    refl
