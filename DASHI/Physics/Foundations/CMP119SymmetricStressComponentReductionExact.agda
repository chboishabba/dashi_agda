{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as Rat using (ℚ; +_; -[1+_]; 0ℚ)
open import Data.Nat.Base using (zero)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut

------------------------------------------------------------------------
-- TEN-COMPONENT SYMMETRIC REDUCTION
--
-- A symmetric rank-two tensor in four dimensions has ten independent
-- components.  DASHI already owns exactly that finite carrier in
-- KernelGeometryEmergenceObligations.
------------------------------------------------------------------------

symmetricComponentAxes :
  K.SymmetricTensorComponent4 → Flat.Axis4 × Flat.Axis4
symmetricComponentAxes K.component00 = Flat.timeAxis , Flat.timeAxis
symmetricComponentAxes K.component01 = Flat.timeAxis , Flat.xAxis
symmetricComponentAxes K.component02 = Flat.timeAxis , Flat.yAxis
symmetricComponentAxes K.component03 = Flat.timeAxis , Flat.zAxis
symmetricComponentAxes K.component11 = Flat.xAxis , Flat.xAxis
symmetricComponentAxes K.component12 = Flat.xAxis , Flat.yAxis
symmetricComponentAxes K.component13 = Flat.xAxis , Flat.zAxis
symmetricComponentAxes K.component22 = Flat.yAxis , Flat.yAxis
symmetricComponentAxes K.component23 = Flat.yAxis , Flat.zAxis
symmetricComponentAxes K.component33 = Flat.zAxis , Flat.zAxis

record PairingComponentSymmetry
    {StressTensor : Set}
    (evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor)
    (stress : StressTensor) : Set where
  field
    componentSymmetric :
      ∀ a b →
      Cut.component evaluator stress a b
      ≡ Cut.component evaluator stress b a

open PairingComponentSymmetry public

record NormalizedSymmetricTenComponentInstance
    {StressTensor : Set}
    (evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor)
    (stress : StressTensor) : Set where
  field
    symmetry :
      PairingComponentSymmetry evaluator stress

    qft00 :
      Cut.component evaluator stress Flat.timeAxis Flat.timeAxis ≡ + 1
    qft01 :
      Cut.component evaluator stress Flat.timeAxis Flat.xAxis ≡ 0ℚ
    qft02 :
      Cut.component evaluator stress Flat.timeAxis Flat.yAxis ≡ 0ℚ
    qft03 :
      Cut.component evaluator stress Flat.timeAxis Flat.zAxis ≡ 0ℚ
    qft11 :
      Cut.component evaluator stress Flat.xAxis Flat.xAxis ≡ -[1+ zero ]
    qft12 :
      Cut.component evaluator stress Flat.xAxis Flat.yAxis ≡ 0ℚ
    qft13 :
      Cut.component evaluator stress Flat.xAxis Flat.zAxis ≡ 0ℚ
    qft22 :
      Cut.component evaluator stress Flat.yAxis Flat.yAxis ≡ -[1+ zero ]
    qft23 :
      Cut.component evaluator stress Flat.yAxis Flat.zAxis ≡ 0ℚ
    qft33 :
      Cut.component evaluator stress Flat.zAxis Flat.zAxis ≡ -[1+ zero ]

open NormalizedSymmetricTenComponentInstance public

tenSymmetricComponentsCompileToSixteen :
  ∀ {StressTensor : Set}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor}
    {stress : StressTensor} →
  NormalizedSymmetricTenComponentInstance evaluator stress →
  Cut.NormalizedCrossSectorStressInstance StressTensor evaluator stress
tenSymmetricComponentsCompileToSixteen instance = record
  { Cut.NormalizedCrossSectorStressInstance.qft00 = qft00 instance
  ; Cut.NormalizedCrossSectorStressInstance.qft11 = qft11 instance
  ; Cut.NormalizedCrossSectorStressInstance.qft22 = qft22 instance
  ; Cut.NormalizedCrossSectorStressInstance.qft33 = qft33 instance
  ; Cut.NormalizedCrossSectorStressInstance.qft01 = qft01 instance
  ; Cut.NormalizedCrossSectorStressInstance.qft02 = qft02 instance
  ; Cut.NormalizedCrossSectorStressInstance.qft03 = qft03 instance
  ; Cut.NormalizedCrossSectorStressInstance.qft10 =
      trans
        (componentSymmetric (symmetry instance) Flat.xAxis Flat.timeAxis)
        (qft01 instance)
  ; Cut.NormalizedCrossSectorStressInstance.qft12 = qft12 instance
  ; Cut.NormalizedCrossSectorStressInstance.qft13 = qft13 instance
  ; Cut.NormalizedCrossSectorStressInstance.qft20 =
      trans
        (componentSymmetric (symmetry instance) Flat.yAxis Flat.timeAxis)
        (qft02 instance)
  ; Cut.NormalizedCrossSectorStressInstance.qft21 =
      trans
        (componentSymmetric (symmetry instance) Flat.yAxis Flat.xAxis)
        (qft12 instance)
  ; Cut.NormalizedCrossSectorStressInstance.qft23 = qft23 instance
  ; Cut.NormalizedCrossSectorStressInstance.qft30 =
      trans
        (componentSymmetric (symmetry instance) Flat.zAxis Flat.timeAxis)
        (qft03 instance)
  ; Cut.NormalizedCrossSectorStressInstance.qft31 =
      trans
        (componentSymmetric (symmetry instance) Flat.zAxis Flat.xAxis)
        (qft13 instance)
  ; Cut.NormalizedCrossSectorStressInstance.qft32 =
      trans
        (componentSymmetric (symmetry instance) Flat.zAxis Flat.yAxis)
        (qft23 instance)
  }

tenSymmetricComponentsCompileToTensorEquality :
  ∀ {StressTensor : Set}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor}
    {stress : StressTensor} →
  NormalizedSymmetricTenComponentInstance evaluator stress →
  (a b : Flat.Axis4) →
  Cut.finiteGRStressRational a b
  ≡ Cut.cmp119RationalTensor evaluator stress a b
tenSymmetricComponentsCompileToTensorEquality instance =
  Cut.normalizedSixteenComponentsCompileToTensorEquality
    (tenSymmetricComponentsCompileToSixteen instance)

independentStressComponentPayments : ℚ
independentStressComponentPayments = + 10

sixteenIndependentComponentPaymentsRequired : Bool
sixteenIndependentComponentPaymentsRequired = false

sixteenIndependentComponentPaymentsRequiredIsFalse :
  sixteenIndependentComponentPaymentsRequired ≡ false
sixteenIndependentComponentPaymentsRequiredIsFalse = refl

ymAbstractSymmetryPredicateAloneGivesCoordinateSymmetry : Bool
ymAbstractSymmetryPredicateAloneGivesCoordinateSymmetry = false

ymAbstractSymmetryPredicateAloneGivesCoordinateSymmetryIsFalse :
  ymAbstractSymmetryPredicateAloneGivesCoordinateSymmetry ≡ false
ymAbstractSymmetryPredicateAloneGivesCoordinateSymmetryIsFalse = refl
