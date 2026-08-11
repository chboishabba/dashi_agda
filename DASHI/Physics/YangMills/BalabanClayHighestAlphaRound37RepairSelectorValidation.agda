module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound37RepairSelectorValidation where

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound36FiniteAtomSelectorValidation
import DASHI.Physics.YangMills.BalabanSelectedPlaquetteLinearRepairModelExact as Repair
import DASHI.Physics.YangMills.BalabanSelectedPlaquetteResidualBudgetRound37Exact as Residual
import DASHI.Physics.YangMills.BalabanP33WilsonGateSignatureRound37Exact as Signature
import DASHI.Physics.YangMills.BalabanP33WilsonAtomOwnershipExact as Atom

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_)

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
  (Residual.gaugeCoefficient + Residual.constraintCoefficient)
  + (Residual.transportCoefficient + Residual.boundaryCoefficient)
  ≡ Residual.totalResidualCoefficient
residualLedgerClosesExactBudget =
  Residual.residualCoefficientLedgerExact

singletonRemainsEulerLagrangeOpen :
  Signature.dependency Signature.singletonSignature
  ≡ Signature.eulerLagrangeOpen
singletonRemainsEulerLagrangeOpen = refl

pairRemainsFiniteYoungClosed :
  Signature.dependency Signature.pairSignature
  ≡ Signature.finiteYoungClosed
pairRemainsFiniteYoungClosed = refl

pairOwnershipRemainsCorrelated :
  Signature.chargeOwner Signature.pairSignature ≡ Atom.correlatedOwner
pairOwnershipRemainsCorrelated = refl
