module DASHI.Physics.Closure.RootSystemB4OrbitQuotientTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (_+_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.ClosureObservableWitness as COW
open import DASHI.Physics.Closure.ShiftClosureObservableWitnessInstance as SCOWI
open import DASHI.Physics.Closure.RootSystemB4ClosureObservableWitnessInstance as B4COWI
open import DASHI.Physics.Closure.RootSystemB4ObservableResolutionMap as B4ORM
open import DASHI.Physics.Closure.RootSystemB4ObservableComparison as B4OC
open import DASHI.Physics.Closure.Validation.RootSystemB4OrbitStabilizerComparison as B4OSC
open import DASHI.Physics.Closure.Validation.RootSystemB4OrbitMergeTheorem as B4OM

record RootSystemB4OrbitQuotientTheorem : Setω where
  field
    resolutionMap : B4ORM.ObservableResolutionMap
    observableComparison : B4OC.B4ObservableComparison
    observableRefinement :
      B4ORM.B4ObservableRefinement
        SCOWI.shiftClosureObservableWitness
        B4COWI.b4ClosureObservableWitness
    shell1FinePartitionDescendsToB4 :
      B4ORM.ObservableResolutionMap.toB4 resolutionMap
        B4OSC.shiftShell1-6
      ≡
      B4ORM.ObservableResolutionMap.toB4 resolutionMap
        B4OSC.shiftShell1-2
    shell1FinePartitionQuotientCardinality :
      B4OSC.b4OrbitSize B4OSC.shiftShell1-6
      ≡
      B4OSC.shiftOrbitSize B4OSC.shiftShell1-6
      + B4OSC.shiftOrbitSize B4OSC.shiftShell1-2
    shell2TwelveClassSurvivesAsB4Shell2 :
      B4ORM.ObservableResolutionMap.toB4 resolutionMap
        B4OSC.shiftShell2-12
      ≡
      B4ORM.b4-shell2-class
    shiftObservableBoundaryDescendsToB4 :
      B4ORM._≡ω_
        (B4ORM.ObservableResolutionMap.onObservables resolutionMap
          SCOWI.shiftClosureObservableWitness)
        B4COWI.b4ClosureObservableWitness
    quotientWitnessedByExplicitWeylElement :
      B4OM.RootSystemB4OrbitMergeTheorem.mergedShell1Representative
        (B4OC.B4ObservableComparison.orbitMerge observableComparison)
      ≡
      B4OM.RootSystemB4OrbitMergeTheorem.mergedShell1Representative
        (B4OC.B4ObservableComparison.orbitMerge observableComparison)

mkRootSystemB4OrbitQuotientTheorem :
  (resolutionMap : B4ORM.ObservableResolutionMap) →
  (observableComparison : B4OC.B4ObservableComparison) →
  (observableRefinement :
    B4ORM.B4ObservableRefinement
      SCOWI.shiftClosureObservableWitness
      B4COWI.b4ClosureObservableWitness) →
  B4ORM.ObservableResolutionMap.toB4 resolutionMap
    B4OSC.shiftShell1-6
  ≡
  B4ORM.ObservableResolutionMap.toB4 resolutionMap
    B4OSC.shiftShell1-2
  →
  B4OSC.b4OrbitSize B4OSC.shiftShell1-6
  ≡
  B4OSC.shiftOrbitSize B4OSC.shiftShell1-6
  + B4OSC.shiftOrbitSize B4OSC.shiftShell1-2
  →
  B4ORM.ObservableResolutionMap.toB4 resolutionMap
    B4OSC.shiftShell2-12
  ≡
  B4ORM.b4-shell2-class
  →
  B4ORM._≡ω_
    (B4ORM.ObservableResolutionMap.onObservables resolutionMap
      SCOWI.shiftClosureObservableWitness)
    B4COWI.b4ClosureObservableWitness
  →
  B4OM.RootSystemB4OrbitMergeTheorem.mergedShell1Representative
    (B4OC.B4ObservableComparison.orbitMerge observableComparison)
  ≡
  B4OM.RootSystemB4OrbitMergeTheorem.mergedShell1Representative
    (B4OC.B4ObservableComparison.orbitMerge observableComparison)
  →
  RootSystemB4OrbitQuotientTheorem
mkRootSystemB4OrbitQuotientTheorem
  resolutionMap
  observableComparison
  observableRefinement
  shell1FinePartitionDescendsToB4
  shell1FinePartitionQuotientCardinality
  shell2TwelveClassSurvivesAsB4Shell2
  shiftObservableBoundaryDescendsToB4
  quotientWitnessedByExplicitWeylElement =
  record
    { resolutionMap = resolutionMap
    ; observableComparison = observableComparison
    ; observableRefinement = observableRefinement
    ; shell1FinePartitionDescendsToB4 = shell1FinePartitionDescendsToB4
    ; shell1FinePartitionQuotientCardinality =
        shell1FinePartitionQuotientCardinality
    ; shell2TwelveClassSurvivesAsB4Shell2 =
        shell2TwelveClassSurvivesAsB4Shell2
    ; shiftObservableBoundaryDescendsToB4 =
        shiftObservableBoundaryDescendsToB4
    ; quotientWitnessedByExplicitWeylElement =
        quotientWitnessedByExplicitWeylElement
    }

canonicalRootSystemB4OrbitQuotientTheorem :  
  RootSystemB4OrbitQuotientTheorem
canonicalRootSystemB4OrbitQuotientTheorem =
  mkRootSystemB4OrbitQuotientTheorem
    B4ORM.canonicalObservableResolutionMap
    B4OC.canonicalB4ObservableComparison
    B4ORM.canonicalB4ObservableRefinement
    refl
    (B4OM.RootSystemB4OrbitMergeTheorem.shell1MergedOrbitCardinality
      B4OM.canonicalRootSystemB4OrbitMergeTheorem)
    refl
    B4ORM.reflω
    refl
