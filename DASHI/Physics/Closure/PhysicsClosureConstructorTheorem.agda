module DASHI.Physics.Closure.PhysicsClosureConstructorTheorem where

open import Agda.Primitive using (Setω)
data _≡ω_ {A : Setω} (x : A) : A → Setω where
  reflω : x ≡ω x

open import DASHI.Physics.Closure.PhysicsClosureCoreWitness as PCCW
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.Closure.PhysicsClosureFullInstance as PCFI

record PhysicsClosureConstructorTheorem : Setω where
  field
    closureCoreWitness : PCCW.PhysicsClosureCoreWitness
    fullClosure : PCF.PhysicsClosureFull
    constructedByCanonicalConstructor :
      fullClosure ≡ω
      PCF.physicsClosureFullFromCoreWitness closureCoreWitness

physicsClosureConstructorTheorem :
  (w : PCCW.PhysicsClosureCoreWitness) →
  PhysicsClosureConstructorTheorem
physicsClosureConstructorTheorem w =
  record
    { closureCoreWitness = w
    ; fullClosure = PCF.physicsClosureFullFromCoreWitness w
    ; constructedByCanonicalConstructor = reflω
    }

canonicalPhysicsClosureConstructorTheorem :
  PhysicsClosureConstructorTheorem
canonicalPhysicsClosureConstructorTheorem =
  record
    { closureCoreWitness = PCFI.physicsClosureCoreWitness
    ; fullClosure = PCF.physicsClosureFullFromCoreWitness PCFI.physicsClosureCoreWitness
    ; constructedByCanonicalConstructor = reflω
    }

syntheticPhysicsClosureConstructorTheorem :
  PhysicsClosureConstructorTheorem
syntheticPhysicsClosureConstructorTheorem =
  record
    { closureCoreWitness = PCFI.syntheticPhysicsClosureCoreWitness
    ; fullClosure = PCFI.physicsClosureFullSynthetic
    ; constructedByCanonicalConstructor = reflω
    }

b4PhysicsClosureConstructorTheorem :
  PhysicsClosureConstructorTheorem
b4PhysicsClosureConstructorTheorem =
  record
    { closureCoreWitness = PCFI.b4PhysicsClosureCoreWitness
    ; fullClosure = PCFI.b4PhysicsClosureFull
    ; constructedByCanonicalConstructor = reflω
    }
