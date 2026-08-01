module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound2AnalyticReductionLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeContractionBallConstructionExact as Ball
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicSchurFromNormPipelineExact as Schur
import DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectPipelineExact as Resolvent
import DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectOnUnitStateExact as UnitResolvent
import DASHI.Physics.YangMills.BalabanClayGate4SU2NonlinearityDefectPipelineExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyResolvedResolventAdapterExact as ResolvedResolvent
import DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyResolvedDefectsAdapterExact as ResolvedBoth
import DASHI.Physics.YangMills.BalabanClayGate4T3ResolvedDefectsReuseExact as T3Resolved

------------------------------------------------------------------------
-- Round-two analytic reductions after the common structural tranche.
--
-- These modules do not assert the missing physical constants.  They prove that
-- once component estimates are supplied, no additional global Schur,
-- resolvent, SU(2)-defect or five-channel theorem remains.
------------------------------------------------------------------------

quantitativeBallInvarianceFromScalarBudgetLevel =
  Ball.quantitativeBallInvarianceFromScalarBudgetLevel
quantitativeContractionBallConstructionLevel =
  Ball.quantitativeContractionBallConstructionLevel

cmp109SegmentToSignedWordLevel = Contours.cmp109SegmentToSignedWordLevel
cmp109SegmentWordLengthLevel = Contours.cmp109SegmentWordLengthLevel
cmp109EnumeratedPeriodicPathConstructionLevel =
  Contours.cmp109EnumeratedPeriodicPathConstructionLevel
cmp109FullPeriodicContourFamilyLevel =
  Contours.cmp109FullPeriodicContourFamilyLevel
cmp109FourActivePeriodicContourCount24Level =
  Contours.cmp109FourActivePeriodicContourCount24Level
cmp109NamedEndpointPathTransportLevel =
  Contours.cmp109NamedEndpointPathTransportLevel

cmp109PipelineToEntryBoundLevel = Schur.cmp109PipelineToEntryBoundLevel
cmp109PipelineToDyadicEnvelopeLevel =
  Schur.cmp109PipelineToDyadicEnvelopeLevel
cmp109PipelineRow128BudgetLevel = Schur.cmp109PipelineRow128BudgetLevel
cmp109PipelineColumn8BudgetLevel = Schur.cmp109PipelineColumn8BudgetLevel

resolventSecondIdentityLevel = Resolvent.resolventSecondIdentityLevel
resolventThreeFactorNormLevel = Resolvent.resolventThreeFactorNormLevel
resolventDifferenceBudgetAssemblyLevel =
  Resolvent.resolventDifferenceBudgetAssemblyLevel
resolventOperatorToUnitDefectLevel =
  UnitResolvent.resolventOperatorToUnitDefectLevel

su2ThreeComponentDefectDefinitionLevel =
  SU2.su2ThreeComponentDefectDefinitionLevel
su2ThreeComponentUnitDefectLevel = SU2.su2ThreeComponentUnitDefectLevel

twoFamilyResolvedResolventUniformityLevel =
  ResolvedResolvent.twoFamilyResolvedResolventUniformityLevel
twoFamilyResolvedResolventAdapterLevel =
  ResolvedResolvent.twoFamilyResolvedResolventAdapterLevel

twoFamilySU2UniformityDerivedLevel =
  ResolvedBoth.twoFamilySU2UniformityDerivedLevel
twoFamilyResolventUniformityDerivedLevel =
  ResolvedBoth.twoFamilyResolventUniformityDerivedLevel
twoFamilyResolvedDefectsAdapterLevel =
  ResolvedBoth.twoFamilyResolvedDefectsAdapterLevel

t3FiveChannelBoundsFromResolvedDefectsLevel =
  T3Resolved.t3FiveChannelBoundsFromResolvedDefectsLevel

------------------------------------------------------------------------
-- Remaining physical constants and identifications.
------------------------------------------------------------------------

physicalCentreMembershipAndScalarBudgetInputsLevel =
  Ball.physicalCentreMembershipAndScalarBudgetInputsLevel
physicalCMP109ComputedEndpointIdentificationInputsLevel =
  Contours.physicalCMP109ComputedEndpointIdentificationInputsLevel
physicalCMP109KernelNormConventionInputsLevel =
  Schur.physicalCMP109KernelNormConventionInputsLevel
physicalCMP109AdjointPipelineInputsLevel =
  Schur.physicalCMP109AdjointPipelineInputsLevel

physicalPerturbedInverseNormInputsLevel =
  Resolvent.physicalPerturbedInverseNormInputsLevel
physicalResolventOperatorIdentificationInputsLevel =
  Resolvent.physicalResolventOperatorIdentificationInputsLevel
physicalResolventActionNormInputsLevel =
  UnitResolvent.physicalResolventActionNormInputsLevel
physicalUnitStateNormConventionInputsLevel =
  UnitResolvent.physicalUnitStateNormConventionInputsLevel

physicalAdMinusIdentityNormInputsLevel =
  SU2.physicalAdMinusIdentityNormInputsLevel
physicalDexpMinusIdentityNormInputsLevel =
  SU2.physicalDexpMinusIdentityNormInputsLevel
physicalDexpInverseMinusIdentityNormInputsLevel =
  SU2.physicalDexpInverseMinusIdentityNormInputsLevel

physicalGaugeConstraintToResolventFormInputsLevel =
  ResolvedResolvent.physicalGaugeConstraintToResolventFormInputsLevel
physicalResolventUnitStateOrderMeaningInputsLevel =
  ResolvedResolvent.physicalResolventUnitStateOrderMeaningInputsLevel
physicalFiveFormsToResolvedDefectsInputsLevel =
  ResolvedBoth.physicalFiveFormsToResolvedDefectsInputsLevel
physicalResolvedDefectOrderConventionInputsLevel =
  ResolvedBoth.physicalResolvedDefectOrderConventionInputsLevel
physicalT3FiveFormIdentificationInputsLevel =
  T3Resolved.physicalT3FiveFormIdentificationInputsLevel
physicalT3ResolvedBudgetMeaningInputsLevel =
  T3Resolved.physicalT3ResolvedBudgetMeaningInputsLevel

physicalClosureRound2AnalyticReductionLedgerLevel : ProofLevel
physicalClosureRound2AnalyticReductionLedgerLevel = machineChecked
