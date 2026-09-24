{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact where

open import Agda.Builtin.Equality using (_≡_)\nopen import Data.Rational.Base using (ℚ; 0ℚ; _+_)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalWilsonDiagonalMetricVariationExact as Diag
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- TEN-SLOT CLASSICAL WILSON ACTION VARIATION
--
-- Diagonal directions are determined by the six plaquette-orientation energies.
-- Off-diagonal metric directions require the mixed F_{mu alpha} F_{nu alpha}
-- lattice observable; these are left explicit rather than incorrectly set zero.
------------------------------------------------------------------------

record ClassicalWilsonTenMetricVariation
    (Configuration : Set) : Set₁ where
  field
    diagonalEnergies :
      Diag.FiniteSixPlaquetteEnergyFamily Configuration

    mixed01 mixed02 mixed03 mixed12 mixed13 mixed23 :
      Configuration → ℚ

open ClassicalWilsonTenMetricVariation public

actionVariationAt :
  ∀ {Configuration} →
  ClassicalWilsonTenMetricVariation Configuration →
  K.SymmetricTensorComponent4 →
  Configuration → ℚ
actionVariationAt dataSet K.component00 =
  Diag.classicalActionVariation00 (diagonalEnergies dataSet)
actionVariationAt dataSet K.component01 = mixed01 dataSet
actionVariationAt dataSet K.component02 = mixed02 dataSet
actionVariationAt dataSet K.component03 = mixed03 dataSet
actionVariationAt dataSet K.component11 =
  Diag.classicalActionVariation11 (diagonalEnergies dataSet)
actionVariationAt dataSet K.component12 = mixed12 dataSet
actionVariationAt dataSet K.component13 = mixed13 dataSet
actionVariationAt dataSet K.component22 =
  Diag.classicalActionVariation22 (diagonalEnergies dataSet)
actionVariationAt dataSet K.component23 = mixed23 dataSet
actionVariationAt dataSet K.component33 =
  Diag.classicalActionVariation33 (diagonalEnergies dataSet)

diagonalActionVariationTraceZero :
  ∀ {Configuration}
    (dataSet : ClassicalWilsonTenMetricVariation Configuration)
    configuration →
  actionVariationAt dataSet K.component00 configuration
  + actionVariationAt dataSet K.component11 configuration
  + actionVariationAt dataSet K.component22 configuration
  + actionVariationAt dataSet K.component33 configuration
  ≡ 0ℚ
diagonalActionVariationTraceZero dataSet =
  Diag.classicalActionVariationTraceZero (diagonalEnergies dataSet)

------------------------------------------------------------------------
-- Package into the Gibbs N/Z/DN/DZ route once the selected base insertion O
-- and its ten metric variations DO[h] are supplied.
------------------------------------------------------------------------

record ClassicalWilsonSelectedInsertion
    (Configuration : Set) : Set₁ where
  field
    actionMetricVariation :
      ClassicalWilsonTenMetricVariation Configuration

    insertionObservable :
      Configuration → ℚ

    insertionVariation :
      K.SymmetricTensorComponent4 →
      Configuration → ℚ

open ClassicalWilsonSelectedInsertion public

asGibbsMetricInsertionData :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  ClassicalWilsonSelectedInsertion Configuration →
  Gibbs.GibbsMetricInsertionData
    Configuration K.SymmetricTensorComponent4 measure
asGibbsMetricInsertionData dataSet = record
  { Gibbs.GibbsMetricInsertionData.insertionObservable =
      insertionObservable dataSet
  ; Gibbs.GibbsMetricInsertionData.actionVariation =
      actionVariationAt (actionMetricVariation dataSet)
  ; Gibbs.GibbsMetricInsertionData.insertionVariation =
      insertionVariation dataSet
  }
