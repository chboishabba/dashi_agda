module DASHI.Physics.Closure.RootSystemB4ObservableResolutionMap where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  reflω : x ≡ω x

open import DASHI.Physics.Closure.ClosureObservableWitness as COW
open import DASHI.Physics.Closure.ShiftClosureObservableWitnessInstance as SCOWI
open import DASHI.Physics.Closure.RootSystemB4ClosureObservableWitnessInstance as B4COWI
open import DASHI.Physics.Closure.RootSystemB4ObservableComparison as B4OC
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR
open import DASHI.Physics.Closure.Validation.RootSystemB4PromotionBridge as B4PB
open import DASHI.Physics.Closure.Validation.RootSystemB4OrbitStabilizerComparison as B4OSC
  hiding (comparison)
open import DASHI.Physics.Closure.Validation.RootSystemB4ShellRegradingTheorem as B4SR
open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.OrbitProfileComputedRootSystemB4 as ORB4
open import DASHI.Physics.Signature31Canonical as S31C

data B4ObservableClass : Set where
  b4-shell1-class : B4ObservableClass
  b4-shell2-class : B4ObservableClass
  outside-b4-root-shells-class : B4ObservableClass

resolutionFromShellIndex :
  B4SR.RootSystemB4ShellIndex → B4ObservableClass
resolutionFromShellIndex B4SR.b4-shell1 = b4-shell1-class
resolutionFromShellIndex B4SR.b4-shell2 = b4-shell2-class
resolutionFromShellIndex B4SR.outside-b4-root-shells = outside-b4-root-shells-class

toB4ObservableClass :
  B4OSC.ShiftShellClass → B4ObservableClass
toB4ObservableClass B4OSC.shiftShell1-24 = outside-b4-root-shells-class
toB4ObservableClass B4OSC.shiftShell1-6 = b4-shell1-class
toB4ObservableClass B4OSC.shiftShell1-2 = b4-shell1-class
toB4ObservableClass B4OSC.shiftShell2-16 = outside-b4-root-shells-class
toB4ObservableClass B4OSC.shiftShell2-12 = b4-shell2-class

projectObservablesToB4 :
  COW.ClosureObservableWitness → COW.ClosureObservableWitness
projectObservablesToB4 obs =
  record
    { realizationLabel = "root-system-b4-standalone"
    ; provedSignature = S31C.signature31FromProvider S31C.b4CoreProvider
    ; observedOrientationTag = 31
    ; observedShell1 = ORB4.b4-shell1-computed
    ; observedShell2 = ORB4.b4-shell2-computed
    ; seams = λ {m} {k} → COW.ClosureObservableWitness.seams obs {m} {k}
    ; lyapunovShift =
        λ {m} {k} → COW.ClosureObservableWitness.lyapunovShift obs {m} {k}
    }

liftObservablesToShift :
  COW.ClosureObservableWitness → COW.ClosureObservableWitness
liftObservablesToShift obs =
  record
    { realizationLabel = "signed-permutation-shift"
    ; provedSignature = S31C.signature31FromProvider S31C.shiftCoreProvider
    ; observedOrientationTag = 31
    ; observedShell1 = OPD.shell1_p3_q1
    ; observedShell2 = OPD.shell2_p3_q1
    ; seams = λ {m} {k} → COW.ClosureObservableWitness.seams obs {m} {k}
    ; lyapunovShift =
        λ {m} {k} → COW.ClosureObservableWitness.lyapunovShift obs {m} {k}
    }

admissibleFromObservable :
  COW.ClosureObservableWitness → RPR.AdmissibleComparisonRealization
admissibleFromObservable obs =
  record
    { label = COW.ClosureObservableWitness.realizationLabel obs
    ; orientationTag = COW.ClosureObservableWitness.observedOrientationTag obs
    ; shell1Profile = COW.ClosureObservableWitness.observedShell1 obs
    ; shell2Profile = COW.ClosureObservableWitness.observedShell2 obs
    ; signature = COW.ClosureObservableWitness.provedSignature obs
    }

record ObservableResolutionMap : Setω where
  field
    toB4 : B4OSC.ShiftShellClass → B4ObservableClass
    onObservables :
      COW.ClosureObservableWitness → COW.ClosureObservableWitness
    liftToShift :
      COW.ClosureObservableWitness → COW.ClosureObservableWitness
    shell1-6-resolution :
      toB4 B4OSC.shiftShell1-6 ≡ b4-shell1-class
    shell1-2-resolution :
      toB4 B4OSC.shiftShell1-2 ≡ b4-shell1-class
    shell2-12-resolution :
      toB4 B4OSC.shiftShell2-12 ≡ b4-shell2-class
    shell1-24-resolution :
      toB4 B4OSC.shiftShell1-24 ≡ outside-b4-root-shells-class
    shell2-16-resolution :
      toB4 B4OSC.shiftShell2-16 ≡ outside-b4-root-shells-class
    resolutionMatchesShellRegrading :
      ∀ c →
      toB4 c ≡
      resolutionFromShellIndex (B4SR.b4ShellIndexOfShiftRepresentative c)

record B4ObservableRefinement
  (shiftObs b4Obs : COW.ClosureObservableWitness) : Setω where
  field
    resolutionMap : ObservableResolutionMap
    comparison : B4OC.B4ObservableComparison
    sourceAdmissible : RPR.AdmissibleComparisonRealization
    targetAdmissible : RPR.AdmissibleComparisonRealization
    sourceOrientationMatches :
      RPR.AdmissibleComparisonRealization.orientationTag sourceAdmissible
      ≡ COW.ClosureObservableWitness.observedOrientationTag shiftObs
    sourceShell1Matches :
      RPR.AdmissibleComparisonRealization.shell1Profile sourceAdmissible
      ≡ COW.ClosureObservableWitness.observedShell1 shiftObs
    sourceShell2Matches :
      RPR.AdmissibleComparisonRealization.shell2Profile sourceAdmissible
      ≡ COW.ClosureObservableWitness.observedShell2 shiftObs
    sourceSignatureMatches :
      RPR.AdmissibleComparisonRealization.signature sourceAdmissible
      ≡ COW.ClosureObservableWitness.provedSignature shiftObs
    targetOrientationMatches :
      RPR.AdmissibleComparisonRealization.orientationTag targetAdmissible
      ≡ COW.ClosureObservableWitness.observedOrientationTag b4Obs
    targetShell1Matches :
      RPR.AdmissibleComparisonRealization.shell1Profile targetAdmissible
      ≡ COW.ClosureObservableWitness.observedShell1 b4Obs
    targetShell2Matches :
      RPR.AdmissibleComparisonRealization.shell2Profile targetAdmissible
      ≡ COW.ClosureObservableWitness.observedShell2 b4Obs
    targetSignatureMatches :
      RPR.AdmissibleComparisonRealization.signature targetAdmissible
      ≡ COW.ClosureObservableWitness.provedSignature b4Obs
    targetPromotionReady :
      B4PB.B4PromotionBridge.promotionStatus B4PB.bridge
      ≡ B4PB.admissiblePromotionReady
    shellBoundaryRefinesToB4 :
      ObservableResolutionMap.onObservables resolutionMap shiftObs ≡ω b4Obs
    shell1BoundaryNotIdentical :
      COW.ClosureObservableWitness.observedShell1 shiftObs
      ≡
      COW.ClosureObservableWitness.observedShell1 b4Obs
      → ⊥
    shell2BoundaryNotIdentical :
      COW.ClosureObservableWitness.observedShell2 shiftObs
      ≡
      COW.ClosureObservableWitness.observedShell2 b4Obs
      → ⊥
    signaturePreserved :
      COW.ClosureObservableWitness.provedSignature shiftObs
      ≡
      COW.ClosureObservableWitness.provedSignature b4Obs

canonicalObservableResolutionMap : ObservableResolutionMap
canonicalObservableResolutionMap =
  record
    { toB4 = toB4ObservableClass
    ; onObservables = projectObservablesToB4
    ; liftToShift = liftObservablesToShift
    ; shell1-6-resolution = refl
    ; shell1-2-resolution = refl
    ; shell2-12-resolution = refl
    ; shell1-24-resolution = refl
    ; shell2-16-resolution = refl
    ; resolutionMatchesShellRegrading = λ
        { B4OSC.shiftShell1-24 → refl
        ; B4OSC.shiftShell1-6 → refl
        ; B4OSC.shiftShell1-2 → refl
        ; B4OSC.shiftShell2-16 → refl
        ; B4OSC.shiftShell2-12 → refl
        }
    }

canonicalB4ObservableRefinement :
  B4ObservableRefinement
    SCOWI.shiftClosureObservableWitness
    B4COWI.b4ClosureObservableWitness
canonicalB4ObservableRefinement =
  record
    { resolutionMap = canonicalObservableResolutionMap
    ; comparison = B4OC.canonicalB4ObservableComparison
    ; sourceAdmissible =
        admissibleFromObservable SCOWI.shiftClosureObservableWitness
    ; targetAdmissible =
        admissibleFromObservable B4COWI.b4ClosureObservableWitness
    ; sourceOrientationMatches = refl
    ; sourceShell1Matches = refl
    ; sourceShell2Matches = refl
    ; sourceSignatureMatches = refl
    ; targetOrientationMatches = refl
    ; targetShell1Matches = refl
    ; targetShell2Matches = refl
    ; targetSignatureMatches = refl
    ; targetPromotionReady = refl
    ; shellBoundaryRefinesToB4 = reflω
    ; shell1BoundaryNotIdentical =
        B4OC.B4ObservableComparison.rawShiftShell1Mismatch
          B4OC.canonicalB4ObservableComparison
    ; shell2BoundaryNotIdentical =
        B4OC.B4ObservableComparison.rawShiftShell2Mismatch
          B4OC.canonicalB4ObservableComparison
    ; signaturePreserved = refl
    }

canonicalLiftedShiftObservable :
  COW.ClosureObservableWitness
canonicalLiftedShiftObservable =
  liftObservablesToShift B4COWI.b4ClosureObservableWitness

canonicalB4LiftRefinement :
  B4ObservableRefinement
    canonicalLiftedShiftObservable
    B4COWI.b4ClosureObservableWitness
canonicalB4LiftRefinement =
  record
    { resolutionMap = canonicalObservableResolutionMap
    ; comparison = B4OC.canonicalB4ObservableComparison
    ; sourceAdmissible =
        admissibleFromObservable canonicalLiftedShiftObservable
    ; targetAdmissible =
        admissibleFromObservable B4COWI.b4ClosureObservableWitness
    ; sourceOrientationMatches = refl
    ; sourceShell1Matches = refl
    ; sourceShell2Matches = refl
    ; sourceSignatureMatches = refl
    ; targetOrientationMatches = refl
    ; targetShell1Matches = refl
    ; targetShell2Matches = refl
    ; targetSignatureMatches = refl
    ; targetPromotionReady = refl
    ; shellBoundaryRefinesToB4 = reflω
    ; shell1BoundaryNotIdentical = λ ()
    ; shell2BoundaryNotIdentical = λ ()
    ; signaturePreserved = refl
    }
