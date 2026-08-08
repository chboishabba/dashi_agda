module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound37RepairSelectorValidation where

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound36FiniteAtomSelectorValidation
import DASHI.Physics.YangMills.BalabanSelectedPlaquetteLinearRepairModelExact as Repair
import DASHI.Physics.YangMills.BalabanSelectedPlaquetteResidualBudgetRound37Exact as Residual

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _*_)

explicitSelectorIsGaugeAdmissible :
  (h : ℚ) →
  Repair.gaugeFunctional (Repair.selectedPlaquetteVariation h)
  ≡ Repair.zeroQ
explicitSelectorIsGaugeAdmissible =
  Repair.selectedPlaquetteVariationGaugeAdmissible

explicitSelectorIsConstraintTangent :
  (h : ℚ) →
  Repair.constraintFunctional (Repair.selectedPlaquetteVariation h)
  ≡ Repair.zeroQ
explicitSelectorIsConstraintTangent =
  Repair.selectedPlaquetteVariationConstraintTangent

explicitSelectorExtractsRequestedSingleton :
  (h : ℚ) →
  Repair.singletonExtractionFunctional
    (Repair.selectedPlaquetteVariation h)
  ≡ h
explicitSelectorExtractsRequestedSingleton =
  Repair.selectedPlaquetteVariationExtractsSingleton

explicitSelectorChargeIsHalfSquare :
  (h : ℚ) →
  Repair.variationCharge (Repair.selectedPlaquetteVariation h)
  ≡ Repair.halfQ * (h * h)
explicitSelectorChargeIsHalfSquare =
  Repair.selectedPlaquetteVariationChargeExact

residualLedgerClosesExactBudget :
  Residual.gaugeCoefficient + Residual.constraintCoefficient
  + Residual.transportCoefficient + Residual.boundaryCoefficient
  ≡ Residual.totalResidualCoefficient
residualLedgerClosesExactBudget =
  Residual.residualCoefficientLedgerExact
