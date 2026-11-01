module DASHI.Physics.Closure.PhysicsClosureCoreWitness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Physics.RealClosureKit
open import DASHI.Physics.UniversalityTheorem
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem as QTCB
open import DASHI.Physics.Closure.CanonicalConstraintClosureWitness as CCCW
open import DASHI.Physics.Closure.ClosureObservableWitness as COW
open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.ExecutionAdmissibilityWitness as EAW
open import DASHI.Physics.Signature31Canonical as S31C

record PhysicsClosureCoreWitness : Setω where
  field
    kit : RealClosureKit
    universality : Universality (RealClosureKit.C kit)

    contractionQuadraticWitness : CFQS.ContractionForcesQuadraticStrong
    contractionSignatureWitness :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem
    quadraticCliffordWitness :
      QTCB.QuadraticToCliffordBridgeTheorem

    signatureCoreProvider : S31C.IntrinsicCoreProvider
    constraintClosureWitness : CCCW.CanonicalConstraintClosureWitness

    dynamics : DC.DynamicalClosure
    dynamicsWitness : DCW.DynamicalClosureWitness
    executionAdmissibilityWitness : EAW.SomeExecutionAdmissibilityWitness
    familyClassificationWitness : EAW.SomeFamilyClassificationWitness

    observables : COW.ClosureObservableWitness
    observableSignatureAgreement :
      S31C.signature31FromProvider signatureCoreProvider
      ≡
      COW.ClosureObservableWitness.provedSignature observables

  closureSignature : CTI.Signature
  closureSignature =
    S31C.signature31FromProvider signatureCoreProvider

open PhysicsClosureCoreWitness public

closureQuadraticBoundary :
  (w : PhysicsClosureCoreWitness) →
  CFQS.SignatureCliffordGaugeBoundary
    (CQSB.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
      (PhysicsClosureCoreWitness.contractionSignatureWitness w))
closureQuadraticBoundary w =
  CQSB.signatureBridgeBoundary
    (PhysicsClosureCoreWitness.contractionSignatureWitness w)
