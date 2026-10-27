module DASHI.Physics.YangMills.YangMillsPlaquetteTOEBridgeValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsPlaquetteTOEBridgeExact as TOE

finiteWilsonGaugeInvarianceIsMachineChecked :
  TOE.toeFiniteSUNWilsonGaugeInvarianceLevel ≡ machineChecked
finiteWilsonGaugeInvarianceIsMachineChecked = refl

singlePlaquetteSecondVariationIsMachineChecked :
  TOE.toeSinglePlaquetteSecondVariationLevel ≡ machineChecked
singlePlaquetteSecondVariationIsMachineChecked = refl

flatWilsonCurlIdentificationIsMachineChecked :
  TOE.toePhysicalFlatWilsonCurlIdentificationLevel ≡ machineChecked
flatWilsonCurlIdentificationIsMachineChecked = refl

zeroFieldCrossChargeIsMachineChecked :
  TOE.toeZeroPhysicalFieldCrossChargeLevel ≡ machineChecked
zeroFieldCrossChargeIsMachineChecked = refl

routeSRemainsLeastPrivilege :
  TOE.toeDirectSourceOSIsLeastPrivilegeMassGapRoute ≡ true
routeSRemainsLeastPrivilege =
  TOE.toeDirectSourceOSIsLeastPrivilegeMassGapRouteIsTrue

routeSDoesNotNeedDenseL2 :
  TOE.toeRouteSRequiresDenseL2Normalization ≡ false
routeSDoesNotNeedDenseL2 =
  TOE.toeRouteSRequiresDenseL2NormalizationIsFalse


routeSH1HasOneTheoremBearingField :
  TOE.toeRouteSH1HasOneTheoremBearingField ≡ true
routeSH1HasOneTheoremBearingField =
  TOE.toeRouteSH1HasOneTheoremBearingFieldIsTrue

routeSH1NeedsNoHistoricalPublishedWrapper :
  TOE.toeRouteSH1RequiresHistoricalPublishedWrapper ≡ false
routeSH1NeedsNoHistoricalPublishedWrapper =
  TOE.toeRouteSH1RequiresHistoricalPublishedWrapperIsFalse

routeSH1ToR387NeedsNoSourceEnvelope :
  TOE.toeRouteSH1ToR387RequiresSourceEnvelope ≡ false
routeSH1ToR387NeedsNoSourceEnvelope =
  TOE.toeRouteSH1ToR387RequiresSourceEnvelopeIsFalse

d1NeedsNoNewAnalyticInequality :
  TOE.toeD1NewAnalyticInequalityRequired ≡ false
d1NeedsNoNewAnalyticInequality =
  TOE.toeD1NewAnalyticInequalityRequiredIsFalse

d2NeedsNoSecondMixingMap :
  TOE.toeD2SecondMixingMapRequired ≡ false
d2NeedsNoSecondMixingMap =
  TOE.toeD2SecondMixingMapRequiredIsFalse


d2BareTransportDoesNotPayPhysicalMixing :
  TOE.toeD2BareTransportABIPaysPhysicalMixing ≡ false
d2BareTransportDoesNotPayPhysicalMixing =
  TOE.toeD2BareTransportABIPaysPhysicalMixingIsFalse

d2NeedsNoIndependentPhysicalOneStepRecurrence :
  TOE.toeD2IndependentPhysicalOneStepRecurrenceRequired ≡ false
d2NeedsNoIndependentPhysicalOneStepRecurrence =
  TOE.toeD2IndependentPhysicalOneStepRecurrenceRequiredIsFalse

d2SameFamilyCompositeConvergenceRemainsPhysical :
  TOE.toeD2SameFamilyCompositeConvergenceStillPhysical ≡ true
d2SameFamilyCompositeConvergenceRemainsPhysical =
  TOE.toeD2SameFamilyCompositeConvergenceStillPhysicalIsTrue

d2ForbidsParallelCompositeTheory :
  TOE.toeD2ParallelCompositeOperatorTheoryAllowed ≡ false
d2ForbidsParallelCompositeTheory =
  TOE.toeD2ParallelCompositeOperatorTheoryAllowedIsFalse

d3RejectsPerturbationIndependentWardSequence :
  TOE.toeD3PerturbationIndependentWardSequenceWouldBeTooWeak ≡ true
d3RejectsPerturbationIndependentWardSequence =
  TOE.toeD3PerturbationIndependentWardSequenceWouldBeTooWeakIsTrue

massGapRemainsUnpromoted :
  TOE.toeMassGapPromoted ≡ false
massGapRemainsUnpromoted =
  TOE.toeMassGapPromotedIsFalse

stoneHamiltonianIdentificationRemainsUnpromoted :
  TOE.toePhysicalStoneGeneratorEqualsYMHamiltonianPromoted ≡ false
stoneHamiltonianIdentificationRemainsUnpromoted =
  TOE.toePhysicalStoneGeneratorEqualsYMHamiltonianPromotedIsFalse

stoneSpectralLowerBoundRemainsUnpromoted :
  TOE.toePhysicalStoneSpectralLowerBoundPromoted ≡ false
stoneSpectralLowerBoundRemainsUnpromoted =
  TOE.toePhysicalStoneSpectralLowerBoundPromotedIsFalse

clayYangMillsRemainsUnpromoted :
  TOE.toeClayYangMillsPromoted ≡ false
clayYangMillsRemainsUnpromoted =
  TOE.toeClayYangMillsPromotedIsFalse

bridgeAddsNoNewPhysicalTheorem :
  TOE.plaquetteTOEBridgeAddsNewPhysicalTheorem ≡ false
bridgeAddsNoNewPhysicalTheorem =
  TOE.plaquetteTOEBridgeAddsNewPhysicalTheoremIsFalse

bridgeCompilerIsMachineChecked :
  TOE.plaquetteTOEBridgeCompilerLevel ≡ machineChecked
bridgeCompilerIsMachineChecked = refl
