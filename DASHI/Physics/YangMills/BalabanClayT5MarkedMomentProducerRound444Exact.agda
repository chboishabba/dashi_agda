{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5MarkedMomentProducerRound444Exact where

------------------------------------------------------------------------
-- ROUND444 / TYPED REALIZATION OF THE MATURE MARKED-FP MOMENT CLOSURE
--
-- The physical marked-polymer owners already organize the analytic chain
--
--   marked FP admissibility
--     -> single-scale exponential moment
--     -> multiscale recursion + summable costs
--     -> uniform exponential moment
--     -> polynomial moments
--     -> reflected-product uniform integrability.
--
-- Historically most of those conclusions are stored as Set-valued physical
-- receipts.  The selected T5 consumer instead requires typed inequalities and
-- a concrete UniformIntegrabilityWitness.
--
-- R444 is the least-privilege bridge: it does NOT ask for a second moment
-- theorem.  It asks only for typed realization of the already-selected marked
-- moment quantities in the exact T5 expectation algebra, then constructs the
-- ExponentialMomentProducer consumed by R443/R464/compactness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP

record MarkedMomentTypedRealization
    {Measure Observable Polymer : Set}
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData Measure Observable ℚ)
    (measureSequence : Nat → Measure)
    (model : FP.AbstractPolymerModel Polymer)
    (marked : FP.MarkedActivityData Polymer Observable model)
    (closure : Physical.MarkedMomentClosure Polymer Observable model marked)
    : Set₁ where
  field
    absoluteObservable : Observable → Observable
    exponentialObservable : ℚ → Observable → Observable
    powerObservable : Nat → Observable → Observable

    zero one lambda : ℚ
    add multiply divide exp : ℚ → ℚ → ℚ
    LessEqual : ℚ → ℚ → Set

    -- Typed realization of the mature uniform exponential-moment theorem.
    uniformExponentialMomentRealized :
      ∀ observable →
      T5.RenormalizedObservable thermodynamic observable →
      ∀ cutoff →
      LessEqual
        (Gram.expectation (T5.operations thermodynamic)
          (measureSequence cutoff)
          (exponentialObservable lambda (absoluteObservable observable)))
        (Physical.uniformMomentBound closure observable)

    -- Typed realization of the already-owned polynomial-from-exponential step.
    powerBelowFactorialExponentialRealized :
      ∀ degree observable → Set

    polynomialMomentRealized :
      ∀ degree observable →
      T5.RenormalizedObservable thermodynamic observable →
      ∀ cutoff →
      LessEqual
        (Gram.expectation (T5.operations thermodynamic)
          (measureSequence cutoff)
          (powerObservable degree (absoluteObservable observable)))
        (multiply (Physical.factorial closure degree)
          (divide (Physical.uniformMomentBound closure observable) lambda))

    reflectedProductYoungRealized :
      ∀ left right → Set

    reflectedProductExponentialMomentRealized :
      ∀ left right →
      T5.RenormalizedObservable thermodynamic left →
      T5.RenormalizedObservable thermodynamic right →
      ∀ cutoff → Set

    reflectedProductUniformIntegrabilityWitness :
      ∀ left right →
      T5.RenormalizedObservable thermodynamic left →
      T5.RenormalizedObservable thermodynamic right →
      T5.UniformIntegrabilityWitness Observable ℚ
        (λ cutoff →
          Gram.multiplyObservable (T5.operations thermodynamic)
            (Gram.reflectObservable (T5.operations thermodynamic) left)
            right)

open MarkedMomentTypedRealization public

compileExponentialMomentProducer :
  ∀ {Measure Observable Polymer}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData Measure Observable ℚ}
    {measureSequence : Nat → Measure}
    {model : FP.AbstractPolymerModel Polymer}
    {marked : FP.MarkedActivityData Polymer Observable model}
    {closure : Physical.MarkedMomentClosure Polymer Observable model marked} →
  MarkedMomentTypedRealization
    thermodynamic measureSequence model marked closure →
  T5.ExponentialMomentProducer
    (T5.operations thermodynamic)
    measureSequence
    (T5.RenormalizedObservable thermodynamic)
compileExponentialMomentProducer realization = record
  { T5.ExponentialMomentProducer.absoluteObservable =
      absoluteObservable realization
  ; T5.ExponentialMomentProducer.exponentialObservable =
      exponentialObservable realization
  ; T5.ExponentialMomentProducer.powerObservable =
      powerObservable realization
  ; T5.ExponentialMomentProducer.zero =
      zero realization
  ; T5.ExponentialMomentProducer.one =
      one realization
  ; T5.ExponentialMomentProducer.lambda =
      lambda realization
  ; T5.ExponentialMomentProducer.add =
      add realization
  ; T5.ExponentialMomentProducer.multiply =
      multiply realization
  ; T5.ExponentialMomentProducer.divide =
      divide realization
  ; T5.ExponentialMomentProducer.exp =
      exp realization
  ; T5.ExponentialMomentProducer.factorial =
      Physical.factorial _
  ; T5.ExponentialMomentProducer.LessEqual =
      LessEqual realization
  ; T5.ExponentialMomentProducer.exponentialMomentBound =
      Physical.uniformMomentBound _
  ; T5.ExponentialMomentProducer.exponentialMomentUniformBound =
      uniformExponentialMomentRealized realization
  ; T5.ExponentialMomentProducer.powerBelowFactorialExponential =
      powerBelowFactorialExponentialRealized realization
  ; T5.ExponentialMomentProducer.singleScaleInsertionMomentBound =
      polynomialMomentRealized realization
  ; T5.ExponentialMomentProducer.reflectedProductYoungBound =
      reflectedProductYoungRealized realization
  ; T5.ExponentialMomentProducer.reflectedProductExponentialMomentBound =
      reflectedProductExponentialMomentRealized realization
  ; T5.ExponentialMomentProducer.buildUniformIntegrabilityWitness =
      reflectedProductUniformIntegrabilityWitness realization
  }

round444MarkedMomentToT5CompilerLevel : ProofLevel
round444MarkedMomentToT5CompilerLevel = machineChecked

-- The abstract marked-FP / multiscale moment deduction is already owned by
-- Physical.MarkedMomentClosure.  What remains is literal typed realization on
-- the selected CMP119 expectation algebra.
round444MarkedFPAbstractMomentClosureLevel : ProofLevel
round444MarkedFPAbstractMomentClosureLevel = machineChecked

round444LiteralCMP119TypedMomentRealizationLevel : ProofLevel
round444LiteralCMP119TypedMomentRealizationLevel = conditional

round444IndependentSecondExponentialMomentTheoremRequired : Bool
round444IndependentSecondExponentialMomentTheoremRequired = false
