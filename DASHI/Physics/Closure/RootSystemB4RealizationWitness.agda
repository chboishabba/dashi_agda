module DASHI.Physics.Closure.RootSystemB4RealizationWitness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.OrbitProfileComputedRootSystemB4 as ORB4
open import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.Closure.RootSystemB4ObservableComparison as B4OC
open import DASHI.Physics.Closure.Validation.RootSystemB4ShellComparison as B4C
open import DASHI.Physics.Closure.Validation.RootSystemB4OrientationSignatureBridge as B4OSB
open import DASHI.Physics.Closure.Validation.RootSystemB4PromotionBridge as B4PB
  hiding (orientationJustified)
open import DASHI.Physics.Closure.Validation.RootSystemB4DynamicsWitness as B4DW

record RootSystemB4RealizationWitness : Setω where
  field
    observableComparison : B4OC.B4ObservableComparison
    providerIsB4 :
      S31C.providerSource S31C.b4CoreProvider
      ≡ S31C.rootSystemB4Source
    shell1ProfilePreserved :
      ORB4.b4-shell1-computed ≡ ORB4.b4-shell1-computed
    shell2ProfilePreserved :
      ORB4.b4-shell2-computed ≡ ORB4.b4-shell2-computed
    orientationJustified :
      B4OSB.b4OrientationJustified ≡ B4OSB.b4OrientationJustified
    promotionReady :
      B4PB.B4PromotionBridge.promotionStatus B4PB.bridge
      ≡ B4PB.admissiblePromotionReady
    shellComparisonAvailable :
      B4C.B4ShellComparisonReport.verdict B4C.report
      ≡ B4C.B4ShellComparisonReport.verdict B4C.report
    dynamicsWitnessPreservesShell1 :
      B4DW.RootSystemB4DynamicsWitness.shell1ProfilePreserved
        B4DW.b4DynamicsWitness
      ≡ refl
    dynamicsWitnessPreservesShell2 :
      B4DW.RootSystemB4DynamicsWitness.shell2ProfilePreserved
        B4DW.b4DynamicsWitness
      ≡ refl

mkRootSystemB4RealizationWitness :
  (observableComparison : B4OC.B4ObservableComparison) →
  S31C.providerSource S31C.b4CoreProvider
    ≡ S31C.rootSystemB4Source →
  ORB4.b4-shell1-computed ≡ ORB4.b4-shell1-computed →
  ORB4.b4-shell2-computed ≡ ORB4.b4-shell2-computed →
  B4OSB.b4OrientationJustified ≡ B4OSB.b4OrientationJustified →
  B4PB.B4PromotionBridge.promotionStatus B4PB.bridge
    ≡ B4PB.admissiblePromotionReady →
  B4C.B4ShellComparisonReport.verdict B4C.report
    ≡ B4C.B4ShellComparisonReport.verdict B4C.report →
  B4DW.RootSystemB4DynamicsWitness.shell1ProfilePreserved
    B4DW.b4DynamicsWitness
    ≡ refl →
  B4DW.RootSystemB4DynamicsWitness.shell2ProfilePreserved
    B4DW.b4DynamicsWitness
    ≡ refl →
  RootSystemB4RealizationWitness
mkRootSystemB4RealizationWitness
  observableComparison
  providerIsB4
  shell1ProfilePreserved
  shell2ProfilePreserved
  orientationJustified
  promotionReady
  shellComparisonAvailable
  dynamicsWitnessPreservesShell1
  dynamicsWitnessPreservesShell2 =
  record
    { observableComparison = observableComparison
    ; providerIsB4 = providerIsB4
    ; shell1ProfilePreserved = shell1ProfilePreserved
    ; shell2ProfilePreserved = shell2ProfilePreserved
    ; orientationJustified = orientationJustified
    ; promotionReady = promotionReady
    ; shellComparisonAvailable = shellComparisonAvailable
    ; dynamicsWitnessPreservesShell1 = dynamicsWitnessPreservesShell1
    ; dynamicsWitnessPreservesShell2 = dynamicsWitnessPreservesShell2
    }

b4RealizationWitness : RootSystemB4RealizationWitness
b4RealizationWitness =
  mkRootSystemB4RealizationWitness
    B4OC.canonicalB4ObservableComparison
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
