module DASHI.Physics.Closure.PhysicsClosureConstructorTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.PhysicsClosureCoreWitness as PCCW
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.Closure.PhysicsClosureFullInstance as PCFI

record PhysicsClosureConstructorTheorem : Setω where
  field
    closureCoreWitness : PCCW.PhysicsClosureCoreWitness
    fullClosure : PCF.PhysicsClosureFull
    constructedByCanonicalConstructor :
      fullClosure ≡
      PCF.physicsClosureFullFromCoreWitness closureCoreWitness

physicsClosureConstructorTheorem :
  (w : PCCW.PhysicsClosureCoreWitness) →
  PhysicsClosureConstructorTheorem
physicsClosureConstructorTheorem w =
  record
    { closureCoreWitness = w
    ; fullClosure = PCF.physicsClosureFullFromCoreWitness w
    ; constructedByCanonicalConstructor = refl
    }

canonicalPhysicsClosureConstructorTheorem :
  PhysicsClosureConstructorTheorem
canonicalPhysicsClosureConstructorTheorem =
  record
    { closureCoreWitness = PCFI.physicsClosureCoreWitness
    ; fullClosure = PCFI.physicsClosureFull
    ; constructedByCanonicalConstructor = refl
    }

syntheticPhysicsClosureConstructorTheorem :
  PhysicsClosureConstructorTheorem
syntheticPhysicsClosureConstructorTheorem =
  record
    { closureCoreWitness = PCFI.syntheticPhysicsClosureCoreWitness
    ; fullClosure = PCFI.physicsClosureFullSynthetic
    ; constructedByCanonicalConstructor = refl
    }
