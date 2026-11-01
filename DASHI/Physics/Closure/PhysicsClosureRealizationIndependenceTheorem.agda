module DASHI.Physics.Closure.PhysicsClosureRealizationIndependenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.Closure.PhysicsClosureCoreWitness as PCCW
open import DASHI.Physics.Closure.PhysicsClosureConstructorTheorem as PCCT
open import DASHI.Physics.Closure.ClosureObservableWitness as COW
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.Closure.PhysicsClosureFullInstance as PCFI
open import DASHI.Physics.Closure.RootSystemB4ObservableComparison as B4OC
open import DASHI.Physics.Closure.RootSystemB4RealizationWitness as B4RW
open import DASHI.Physics.Signature31Canonical as S31C

record StructuralRealizationDifference
  (w : PCCW.PhysicsClosureCoreWitness) : Setω where
  field
    comparisonMap : B4OC.B4ObservableComparison
    providerSourceNotShift :
      S31C.providerSource
        (PCCW.PhysicsClosureCoreWitness.signatureCoreProvider w)
      ≡
      S31C.shiftOrbitProfileSource
      → ⊥
    shell1BoundaryNotIdentical :
      COW.ClosureObservableWitness.observedShell1
        (PCCW.PhysicsClosureCoreWitness.observables w)
      ≡
      COW.ClosureObservableWitness.observedShell1
        (PCCW.PhysicsClosureCoreWitness.observables PCFI.physicsClosureCoreWitness)
      → ⊥
    shell2BoundaryNotIdentical :
      COW.ClosureObservableWitness.observedShell2
        (PCCW.PhysicsClosureCoreWitness.observables w)
      ≡
      COW.ClosureObservableWitness.observedShell2
        (PCCW.PhysicsClosureCoreWitness.observables PCFI.physicsClosureCoreWitness)
      → ⊥

record IndependentFromShift
  (w : PCCW.PhysicsClosureCoreWitness) : Setω where
  field
    b4Realization : B4RW.RootSystemB4RealizationWitness
    witnessUsesB4Provider :
      PCCT._≡ω_
        (PCCW.PhysicsClosureCoreWitness.signatureCoreProvider w)
        S31C.b4CoreProvider
    witnessSignatureAgreesWithObservables :
      S31C.signature31FromProvider
        (PCCW.PhysicsClosureCoreWitness.signatureCoreProvider w)
      ≡
      COW.ClosureObservableWitness.provedSignature
        (PCCW.PhysicsClosureCoreWitness.observables w)
    structuralDifference :
      StructuralRealizationDifference w

record PhysicsClosureRealizationIndependenceTheorem : Setω where
  field
    shiftWitness : PCCW.PhysicsClosureCoreWitness
    independentWitness : PCCW.PhysicsClosureCoreWitness
    shiftConstructorTheorem : PCCT.PhysicsClosureConstructorTheorem
    independentConstructorTheorem : PCCT.PhysicsClosureConstructorTheorem
    independentFromShift :
      IndependentFromShift independentWitness

  shiftClosure : PCF.PhysicsClosureFull
  shiftClosure =
    PCCT.PhysicsClosureConstructorTheorem.fullClosure
      shiftConstructorTheorem

  independentClosure : PCF.PhysicsClosureFull
  independentClosure =
    PCCT.PhysicsClosureConstructorTheorem.fullClosure
      independentConstructorTheorem

canonicalShiftConstructorTheorem :
  PCCT.PhysicsClosureConstructorTheorem
canonicalShiftConstructorTheorem =
  PCCT.canonicalPhysicsClosureConstructorTheorem

b4Source≢shiftSource :
  S31C.rootSystemB4Source ≡ S31C.shiftOrbitProfileSource →
  ⊥
b4Source≢shiftSource ()

realizationIndependenceTheoremFromWitnesses :
  (wShift : PCCW.PhysicsClosureCoreWitness) →
  (wIndependent : PCCW.PhysicsClosureCoreWitness) →
  IndependentFromShift wIndependent →
  PhysicsClosureRealizationIndependenceTheorem
realizationIndependenceTheoremFromWitnesses wShift wIndependent independence =
  record
    { shiftWitness = wShift
    ; independentWitness = wIndependent
    ; shiftConstructorTheorem =
        PCCT.physicsClosureConstructorTheorem wShift
    ; independentConstructorTheorem =
        PCCT.physicsClosureConstructorTheorem wIndependent
    ; independentFromShift = independence
    }

canonicalShiftWitness :
  PCCW.PhysicsClosureCoreWitness
canonicalShiftWitness = PCFI.physicsClosureCoreWitness

b4IndependentFromShift :
  IndependentFromShift PCFI.b4PhysicsClosureCoreWitness
b4IndependentFromShift =
  let
    cmp =
      B4RW.RootSystemB4RealizationWitness.observableComparison
        B4RW.b4RealizationWitness
  in
  record
    { b4Realization = B4RW.b4RealizationWitness
    ; witnessUsesB4Provider = PCCT.reflω
    ; witnessSignatureAgreesWithObservables =
        PCCW.PhysicsClosureCoreWitness.observableSignatureAgreement
          PCFI.b4PhysicsClosureCoreWitness
    ; structuralDifference =
        record
          { comparisonMap = cmp
          ; providerSourceNotShift = b4Source≢shiftSource
          ; shell1BoundaryNotIdentical = λ eq →
              B4OC.B4ObservableComparison.rawShiftShell1Mismatch cmp (sym eq)
          ; shell2BoundaryNotIdentical = λ eq →
              B4OC.B4ObservableComparison.rawShiftShell2Mismatch cmp (sym eq)
          }
    }

b4PhysicsClosureRealizationIndependenceTheorem :
  PhysicsClosureRealizationIndependenceTheorem
b4PhysicsClosureRealizationIndependenceTheorem =
  realizationIndependenceTheoremFromWitnesses
    PCFI.physicsClosureCoreWitness
    PCFI.b4PhysicsClosureCoreWitness
    b4IndependentFromShift

shiftAndB4StructurallyDistinct :
  StructuralRealizationDifference PCFI.b4PhysicsClosureCoreWitness
shiftAndB4StructurallyDistinct =
  IndependentFromShift.structuralDifference b4IndependentFromShift
