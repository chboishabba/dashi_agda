module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallPaymentReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.SuperconductingChargeMassCurrentBidiExact as Current
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyScopeBidiExact as Stress
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact as GR
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGConstitutiveRatioMeasurementExact as Ratio
import DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact as Plan
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGDiscriminatorCutsetExact as Cutset
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScalingModelDiscriminatorExact as Scaling
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScalingReplicationIdentityWeldExact as Replication
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallProgressionExact as Progress

------------------------------------------------------------------------
-- RECEIPT-INDEXED TERMINAL SCIENTIFIC-WALL PAYMENT
--
-- The five-bit progression state is a scheduler, not evidence.  The terminal
-- all-paid state is admissible for downstream use only when backed by the
-- actual existing receipts and same-object welds below.
------------------------------------------------------------------------

record FullyPaidScientificWallReceipt
    {prediction : GR.OrdinaryGRPredictionReceipt}
    (ratio : Ratio.ConstitutiveRatioMeasurementReceipt prediction)
    (bundle : Plan.ScalingReplicationBundleReceipt) : Set₁ where
  constructor fully-paid-scientific-wall-receipt
  field
    massCurrent : Current.MassCurrentSourceReconstructionReceipt
    stressEnergy : Stress.LaboratoryStressEnergyReceipt
    stressEnergyUsesSameMassCurrent :
      Stress.massCurrentSource stressEnergy ≡ massCurrent

    discrimination : Cutset.MaterialEffectiveNegativeGDiscriminationReceipt
    modelSeparation : Scaling.ScalingModelSeparationReceipt
    modelSeparationUsesSameDiscrimination :
      Scaling.upstreamCutset modelSeparation ≡ discrimination

    scalingReplicationWeld : Replication.ScalingReplicationIdentityWeld ratio bundle

    sameNegativeGInterpretation :
      Cutset.constitutiveNegativeGWeld discrimination
        ≡ Replication.compileConstitutiveNegativeGReceipt scalingReplicationWeld

open FullyPaidScientificWallReceipt public

paymentStateFromFullyPaidReceipt :
  {prediction : GR.OrdinaryGRPredictionReceipt} →
  {ratio : Ratio.ConstitutiveRatioMeasurementReceipt prediction} →
  {bundle : Plan.ScalingReplicationBundleReceipt} →
  FullyPaidScientificWallReceipt ratio bundle →
  Progress.ScientificWallPaymentState
paymentStateFromFullyPaidReceipt _ = Progress.fullyPaidWall

fullyPaidReceiptClosesScientificWall :
  {prediction : GR.OrdinaryGRPredictionReceipt} →
  {ratio : Ratio.ConstitutiveRatioMeasurementReceipt prediction} →
  {bundle : Plan.ScalingReplicationBundleReceipt} →
  (receipt : FullyPaidScientificWallReceipt ratio bundle) →
  Progress.firstOpenScientificWallLeaf (paymentStateFromFullyPaidReceipt receipt)
    ≡ Progress.scientificWallClosed
fullyPaidReceiptClosesScientificWall _ = Progress.fullyPaidWallIsClosed

fullyPaidReceiptSchedulesNoFurtherWallAcquisition :
  {prediction : GR.OrdinaryGRPredictionReceipt} →
  {ratio : Ratio.ConstitutiveRatioMeasurementReceipt prediction} →
  {bundle : Plan.ScalingReplicationBundleReceipt} →
  (receipt : FullyPaidScientificWallReceipt ratio bundle) →
  Progress.decisionForLeaf
    (Progress.firstOpenScientificWallLeaf (paymentStateFromFullyPaidReceipt receipt))
    ≡ Progress.noFurtherScientificWallAcquisition
fullyPaidReceiptSchedulesNoFurtherWallAcquisition _ = Progress.closedWallHasNoFurtherAcquisition

record ScientificWallPaymentReceiptBoundary : Set where
  constructor scientific-wall-payment-receipt-boundary
  field
    arbitraryAllTrueBooleansCountAsScientificPayment : Bool
    terminalPaymentRequiresActualReceipts : Bool
    stressEnergyMustUseExactPaidMassCurrent : Bool
    modelSeparationMustUseExactDiscriminationReceipt : Bool
    scalingReplicationMustUseExactTypedRatio : Bool
    terminalNegativeGInterpretationMayDriftAcrossReceipts : Bool
    fullyPaidReceiptAutomaticallyProvesPhysicalNegativeG : Bool

canonicalScientificWallPaymentReceiptBoundary : ScientificWallPaymentReceiptBoundary
canonicalScientificWallPaymentReceiptBoundary =
  scientific-wall-payment-receipt-boundary false true true true true false false
