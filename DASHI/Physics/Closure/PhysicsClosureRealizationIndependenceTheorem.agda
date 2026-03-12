module DASHI.Physics.Closure.PhysicsClosureRealizationIndependenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.Closure.PhysicsClosureCoreWitness as PCCW
open import DASHI.Physics.Closure.PhysicsClosureConstructorTheorem as PCCT
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.Closure.PhysicsClosureFullInstance as PCFI
open import DASHI.Physics.Closure.ObservablePredictionPackage as OPP
open import DASHI.Physics.Closure.SyntheticRealizationWitness as SYRW
open import DASHI.Physics.Signature31Canonical as S31C

record IndependentFromShift
  (w : PCCW.PhysicsClosureCoreWitness) : Setω where
  field
    syntheticRealization : SYRW.SyntheticRealizationWitness
    witnessUsesSyntheticProvider :
      PCCW.PhysicsClosureCoreWitness.signatureCoreProvider w
      ≡
      S31C.syntheticCoreProvider
    witnessSignatureAgreesWithObservables :
      S31C.signature31FromProvider
        (PCCW.PhysicsClosureCoreWitness.signatureCoreProvider w)
      ≡
      OPP.ObservablePredictionPackage.provedSignature
        (PCCW.PhysicsClosureCoreWitness.observables w)
    providerDistinguishedFromShift :
      PCCW.PhysicsClosureCoreWitness.signatureCoreProvider w
      ≡
      S31C.shiftCoreProvider
      → ⊥

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

syntheticSource≢shiftSource :
  S31C.syntheticOneMinusSource ≡ S31C.shiftOrbitProfileSource →
  ⊥
syntheticSource≢shiftSource ()

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

syntheticIndependentFromShift :
  IndependentFromShift PCFI.syntheticPhysicsClosureCoreWitness
syntheticIndependentFromShift =
  record
    { syntheticRealization = SYRW.syntheticRealizationWitness
    ; witnessUsesSyntheticProvider = refl
    ; witnessSignatureAgreesWithObservables =
        PCCW.PhysicsClosureCoreWitness.observableSignatureAgreement
          PCFI.syntheticPhysicsClosureCoreWitness
    ; providerDistinguishedFromShift = λ eq →
        syntheticSource≢shiftSource
          (cong S31C.providerSource eq)
    }

syntheticPhysicsClosureRealizationIndependenceTheorem :
  PhysicsClosureRealizationIndependenceTheorem
syntheticPhysicsClosureRealizationIndependenceTheorem =
  realizationIndependenceTheoremFromWitnesses
    PCFI.physicsClosureCoreWitness
    PCFI.syntheticPhysicsClosureCoreWitness
    syntheticIndependentFromShift
