module DASHI.Physics.YangMills.BalabanClayT3ConfiguredPhysicalGatewayExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredFiveHessianDominationExact as Hessian
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredCommonRadiusCertificateExact as Radius
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredPhysicalGreenInstanceExact as Green

------------------------------------------------------------------------
-- End-to-end T3 gateway.  The five local physical estimates construct the
-- configured domination record; exact radius arithmetic gives coercivity; the
-- resulting spectral gap is then the input to the configured Combes--Thomas /
-- Fourier / RG-image Green instance.
------------------------------------------------------------------------

record ConfiguredPhysicalT3Gateway
    (Background State CurvatureCell TransportCell ChartCell GaugeCell
      ConstraintCell Scale Volume Site Function Scalar GreenOperator Symbol : Set)
    : Set₂ where
  field
    localHessian : Hessian.LiteralFiveHessianLocalData
      Background State CurvatureCell TransportCell ChartCell GaugeCell
      ConstraintCell

    referenceEnergy physicalEnergy : Background → State → ℚ

    referenceCoercive : ∀ background state →
      Radius.configuredReferenceCoercivity
        * Hessian.normSq localHessian background state
      ≤ referenceEnergy background state

    physicalEnergyDefinition : ∀ background state →
      physicalEnergy background state
      ≡ referenceEnergy background state
        + Hessian.totalRemainder localHessian background state

    physicalEnergyLowerFromAbsoluteRemainder : ∀ background state →
      Hessian.totalRemainder localHessian background state
      ≤ Radius.configuredHalfReference
        * Hessian.normSq localHessian background state →
      Radius.configuredHalfReference
        * Hessian.normSq localHessian background state
      ≤ physicalEnergy background state

    radiusIsConfigured : ∀ background state →
      Hessian.configuredRadius localHessian background state
      ≡ Radius.configuredRadius

    green : Green.ConfiguredFourierRGImageInstance
      Scale Volume Site Function Scalar GreenOperator Symbol

    physicalGapFeedsGreen : ∀ background state →
      Hessian.BackgroundInConfiguredRadius localHessian background → Set

open ConfiguredPhysicalT3Gateway public

asConfiguredCommonRadiusPhysicalInput :
  ∀ {Background State CurvatureCell TransportCell ChartCell GaugeCell
      ConstraintCell Scale Volume Site Function Scalar GreenOperator Symbol} →
  ConfiguredPhysicalT3Gateway
    Background State CurvatureCell TransportCell ChartCell GaugeCell
    ConstraintCell Scale Volume Site Function Scalar GreenOperator Symbol →
  Radius.ConfiguredCommonRadiusPhysicalInput Background State
asConfiguredCommonRadiusPhysicalInput dataSet = record
  { domination = Hessian.asConfiguredFiveRemainderDomination
      (localHessian dataSet)
  ; radiusIsConfigured = radiusIsConfigured dataSet
  ; referenceEnergy = referenceEnergy dataSet
  ; physicalEnergy = physicalEnergy dataSet
  ; referenceCoercive = referenceCoercive dataSet
  ; physicalEnergyDefinition = physicalEnergyDefinition dataSet
  ; physicalEnergyLowerFromAbsoluteRemainder =
      physicalEnergyLowerFromAbsoluteRemainder dataSet
  }

literalFiveBackgroundRemaindersBelowHalfConfigured :
  ∀ {Background State CurvatureCell TransportCell ChartCell GaugeCell
      ConstraintCell Scale Volume Site Function Scalar GreenOperator Symbol}
    (dataSet : ConfiguredPhysicalT3Gateway
      Background State CurvatureCell TransportCell ChartCell GaugeCell
      ConstraintCell Scale Volume Site Function Scalar GreenOperator Symbol)
    background state →
  Hessian.BackgroundInConfiguredRadius (localHessian dataSet) background →
  Hessian.totalRemainder (localHessian dataSet) background state
  ≤ Radius.configuredHalfReference
      * Hessian.normSq (localHessian dataSet) background state
literalFiveBackgroundRemaindersBelowHalfConfigured dataSet =
  Radius.configuredFiveBackgroundRemaindersBelowHalf
    (asConfiguredCommonRadiusPhysicalInput dataSet)

physicalSmallFieldFluctuationCoerciveLiteralConfigured :
  ∀ {Background State CurvatureCell TransportCell ChartCell GaugeCell
      ConstraintCell Scale Volume Site Function Scalar GreenOperator Symbol}
    (dataSet : ConfiguredPhysicalT3Gateway
      Background State CurvatureCell TransportCell ChartCell GaugeCell
      ConstraintCell Scale Volume Site Function Scalar GreenOperator Symbol)
    background state →
  Hessian.BackgroundInConfiguredRadius (localHessian dataSet) background →
  Radius.configuredHalfReference
    * Hessian.normSq (localHessian dataSet) background state
  ≤ physicalEnergy dataSet background state
physicalSmallFieldFluctuationCoerciveLiteralConfigured dataSet =
  Radius.configuredPhysicalSmallFieldCoercive
    (asConfiguredCommonRadiusPhysicalInput dataSet)

physicalFluctuationGreenOffDiagonalDecayLiteralConfigured dataSet =
  Green.physicalFluctuationGreenOffDiagonalDecayConfigured (green dataSet)

configuredT3LocalToCoerciveGatewayLevel : ProofLevel
configuredT3LocalToCoerciveGatewayLevel = machineChecked

configuredT3CoerciveToGreenGatewayLevel : ProofLevel
configuredT3CoerciveToGreenGatewayLevel = machineChecked

literalLocalHessianGapFourierImageInputsLevel : ProofLevel
literalLocalHessianGapFourierImageInputsLevel = conditional
