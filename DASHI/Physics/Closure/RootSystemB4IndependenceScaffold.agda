module DASHI.Physics.Closure.RootSystemB4IndependenceScaffold where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.ObservableResolutionInvarianceTheorem as ORIT
open import DASHI.Physics.Closure.PhysicsClosureConstructorTheorem as PCCT
open import DASHI.Physics.Closure.PhysicsClosureRealizationIndependenceTheorem as PCRIT
open import DASHI.Physics.Closure.RootSystemB4OrbitQuotientTheorem as B4OQT
open import DASHI.Physics.Closure.Validation.RootSystemB4ShellComparison as B4C

record RootSystemB4IndependentCoreWitnessObligations : Setω where
  field
    shellComparisonAvailable : B4C.B4ShellComparisonReport
    constructorReady : PCCT.PhysicsClosureConstructorTheorem
    orbitQuotientReady : B4OQT.RootSystemB4OrbitQuotientTheorem
    observableResolutionInvariant : ORIT.ObservableResolutionInvarianceTheorem
    independenceReady : PCRIT.PhysicsClosureRealizationIndependenceTheorem

b4IndependentCoreWitnessObligations :
  RootSystemB4IndependentCoreWitnessObligations
b4IndependentCoreWitnessObligations =
  record
    { shellComparisonAvailable = B4C.report
    ; constructorReady = PCCT.b4PhysicsClosureConstructorTheorem
    ; orbitQuotientReady = B4OQT.canonicalRootSystemB4OrbitQuotientTheorem
    ; observableResolutionInvariant =
        ORIT.canonicalObservableResolutionInvarianceTheorem
    ; independenceReady = PCRIT.b4PhysicsClosureRealizationIndependenceTheorem
    }
