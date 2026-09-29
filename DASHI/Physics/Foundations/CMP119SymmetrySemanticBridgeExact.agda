{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetrySemanticBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact as Sym

------------------------------------------------------------------------
-- SEMANTIC BRIDGE FOR THE EXISTING YM "Symmetric" PREDICATE
--
-- The pinned YM local-stress package already carries a proof of an abstract
-- predicate Symmetric stressTensor.  GRQFT only needs its coordinate meaning on
-- the selected metric-basis evaluator.  This bridge states that meaning once.
------------------------------------------------------------------------

record YMSymmetryMeansMetricBasisComponentSymmetry
    {StressTensor : Set}
    (Symmetric : StressTensor → Set)
    (stress : StressTensor)
    (evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor) : Set₁ where
  field
    ymSymmetric :
      Symmetric stress

    symmetricPredicateHasCoordinateMeaning :
      Symmetric stress →
      ∀ a b →
      Cut.component evaluator stress a b
      ≡ Cut.component evaluator stress b a

open YMSymmetryMeansMetricBasisComponentSymmetry public

compileYMSymmetryToComponentSymmetry :
  ∀ {StressTensor : Set}
    {Symmetric : StressTensor → Set}
    {stress : StressTensor}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor} →
  YMSymmetryMeansMetricBasisComponentSymmetry Symmetric stress evaluator →
  Sym.PairingComponentSymmetry evaluator stress
compileYMSymmetryToComponentSymmetry bridge = record
  { Sym.PairingComponentSymmetry.componentSymmetric =
      symmetricPredicateHasCoordinateMeaning bridge (ymSymmetric bridge)
  }

secondIndependentSymmetryTheoremAfterSemanticBridgeRequired : Bool
secondIndependentSymmetryTheoremAfterSemanticBridgeRequired = false

secondIndependentSymmetryTheoremAfterSemanticBridgeRequiredIsFalse :
  secondIndependentSymmetryTheoremAfterSemanticBridgeRequired ≡ false
secondIndependentSymmetryTheoremAfterSemanticBridgeRequiredIsFalse = refl

symmetrySemanticMeaningStillRequired : Bool
symmetrySemanticMeaningStillRequired = true

symmetrySemanticMeaningStillRequiredIsTrue :
  symmetrySemanticMeaningStillRequired ≡ true
symmetrySemanticMeaningStillRequiredIsTrue = refl
