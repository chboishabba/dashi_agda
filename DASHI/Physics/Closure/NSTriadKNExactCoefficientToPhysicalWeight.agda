module DASHI.Physics.Closure.NSTriadKNExactCoefficientToPhysicalWeight where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation as Allocation
import DASHI.Physics.Closure.NSTriadKNPhysicalClassEncoding as Encoding
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Exact

------------------------------------------------------------------------
-- Bridge the exact signed coefficient to the Nat-valued matrix only through
-- an explicitly named majorant.  The raw coefficient remains signed.
------------------------------------------------------------------------

record RetainedCoefficientRealization
    {v s : Level}
    {Vector : Set v}
    {Scalar : Set s}
    (L : Exact.VelocityGalerkinLaws Z3.FourierMode Vector Scalar)
    {carrier : Allocation.TriadStateCarrier}
    {N : Nat}
    (policy : Allocation.RetainedStatePolicy carrier N) :
    Set (lsuc (v ⊔ s)) where
  constructor retained-coefficient-realization
  field
    pVector qVector kTestVector :
      Allocation.RetainedPhysicalTriad policy → Vector

    coefficientMajorant : Scalar → Nat

open RetainedCoefficientRealization public

retainedIncidence :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N} →
  Allocation.RetainedPhysicalTriad policy →
  Physical.PhysicalTriadIncidence
retainedIncidence τ =
  Allocation.incidence (Allocation.state τ)

exactRetainedSignedCoefficient :
  ∀ {v s} {Vector : Set v} {Scalar : Set s}
    {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N}
    (L : Exact.VelocityGalerkinLaws Z3.FourierMode Vector Scalar) →
  RetainedCoefficientRealization L policy →
  Allocation.RetainedPhysicalTriad policy →
  Scalar
exactRetainedSignedCoefficient L realization τ =
  Exact.testedOrderedPairCoefficient L
    (Physical.k
      (retainedIncidence τ))
    (Physical.p
      (retainedIncidence τ))
    (Physical.q
      (retainedIncidence τ))
    (pVector realization τ)
    (qVector realization τ)
    (kTestVector realization τ)

exactCoefficientWeightDerivation :
  ∀ {v s} {Vector : Set v} {Scalar : Set s}
    {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N}
    (L : Exact.VelocityGalerkinLaws Z3.FourierMode Vector Scalar) →
  (realization : RetainedCoefficientRealization L policy) →
  Encoding.PhysicalWeightDerivation
    (Allocation.RetainedPhysicalTriad policy)
exactCoefficientWeightDerivation L realization =
  Encoding.physical-weight-derivation
    _
    (exactRetainedSignedCoefficient L realization)
    (coefficientMajorant realization)

rawCoefficientIsExactSignedGalerkinTerm :
  ∀ {v s} {Vector : Set v} {Scalar : Set s}
    {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N}
    (L : Exact.VelocityGalerkinLaws Z3.FourierMode Vector Scalar)
    (realization : RetainedCoefficientRealization L policy)
    (τ : Allocation.RetainedPhysicalTriad policy) →
  Encoding.rawFourierCoefficient
    (exactCoefficientWeightDerivation L realization) τ
  ≡ exactRetainedSignedCoefficient L realization τ
rawCoefficientIsExactSignedGalerkinTerm L realization τ = refl

natKernelWeightIsNamedMajorant :
  ∀ {v s} {Vector : Set v} {Scalar : Set s}
    {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N}
    (L : Exact.VelocityGalerkinLaws Z3.FourierMode Vector Scalar)
    (realization : RetainedCoefficientRealization L policy)
    (τ : Allocation.RetainedPhysicalTriad policy) →
  Encoding.physicalWeight
    (exactCoefficientWeightDerivation L realization) τ
  ≡
  coefficientMajorant realization
    (exactRetainedSignedCoefficient L realization τ)
natKernelWeightIsNamedMajorant L realization τ = refl

exactCoefficientConnectedToPhysicalWeight : Bool
exactCoefficientConnectedToPhysicalWeight = true

exactCoefficientConnectedToPhysicalWeightIsTrue :
  exactCoefficientConnectedToPhysicalWeight ≡ true
exactCoefficientConnectedToPhysicalWeightIsTrue = refl

majorantProvedSharpEnoughForUniformGap : Bool
majorantProvedSharpEnoughForUniformGap = false

majorantProvedSharpEnoughForUniformGapIsFalse :
  majorantProvedSharpEnoughForUniformGap ≡ false
majorantProvedSharpEnoughForUniformGapIsFalse = refl
