module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound2IntegratedExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109BlockConventionSeparationExact as Convention
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative
import DASHI.Physics.YangMills.BalabanClayGate4FederbushFaddeevPopovQuantitativeIFTReuseExact as IFT
import DASHI.Physics.YangMills.BalabanClayGate4FederbushFaddeevPopovInverseStabilityExact as Inverse
import DASHI.Physics.YangMills.BalabanClayGate4TreeBackgroundSliceTransitionExact as Slice
import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Norm
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaFiveLocalChannelsExact as HR
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaLocalToUniformExact as HRBase

------------------------------------------------------------------------
-- One coherent consumer for physical-closure round two.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- This record ensures that contour geometry, the two quantitative implicit
-- functions, their centre/Faddeev--Popov inverse carriers, the CMP109 entry-norm
-- pipeline, and the five local H-R_beta channels are selected together.  The
-- consequences below are derived from that one witness, preventing downstream
-- consumers from mixing radius, norm, basis or block conventions.
------------------------------------------------------------------------

record PhysicalClosureRound2Inputs
    (Point
      FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar : Set)
    : Set₁ where
  field
    blockConventionBridge : Convention.BlockConventionBridge

    contourAction :
      Contours.CommutingSegmentAction Point Contours.AxisSegment
    contourDisplacement : Contours.Displacement4

    sharedIFT : IFT.SharedQuantitativeIFTApplications
      FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent Bound

    centreInverse :
      Inverse.FederbushCentreInverseClosure CentreTangent Bound
    centreZeroAgreement :
      Inverse.ZeroConventionAgreement
        (Inverse.closure centreInverse)

    faddeevPopovInverse :
      Inverse.FaddeevPopovInverseClosure GaugeParameter Bound
    faddeevPopovZeroAgreement :
      Inverse.ZeroConventionAgreement
        (Inverse.closure faddeevPopovInverse)

    entryPipeline : Norm.CMP109DerivativeEntryPipeline Operator Bound

    hrBeta : HR.PhysicalFiveChannelHRBetaNormalization Cell Scalar

    CommonPhysicalNormConvention : Set
    commonPhysicalNormConvention : CommonPhysicalNormConvention

    BlockBridgeMatchesContourConvention : Set
    blockBridgeMatchesContourConvention :
      BlockBridgeMatchesContourConvention

open PhysicalClosureRound2Inputs public

selectedFederbushClosure :
  ∀ {Point FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar} →
  PhysicalClosureRound2Inputs Point
    FederbushInput FederbushCentre FederbushResidual
    TreeSlice BackgroundSlice TreeTangent BackgroundTangent
    CentreTangent GaugeParameter Operator Bound Cell Scalar →
  IFT.FederbushQuantitativeClosure
    FederbushInput FederbushCentre FederbushResidual Bound
selectedFederbushClosure inputs = IFT.federbush (sharedIFT inputs)

selectedBackgroundClosure :
  ∀ {Point FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar} →
  PhysicalClosureRound2Inputs Point
    FederbushInput FederbushCentre FederbushResidual
    TreeSlice BackgroundSlice TreeTangent BackgroundTangent
    CentreTangent GaugeParameter Operator Bound Cell Scalar →
  IFT.BackgroundSliceQuantitativeClosure
    TreeSlice BackgroundSlice TreeTangent BackgroundTangent Bound
selectedBackgroundClosure inputs = IFT.backgroundSlice (sharedIFT inputs)

federbushSolutionUniqueFromIntegratedInputs :
  ∀ {Point FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar}
    (inputs : PhysicalClosureRound2Inputs Point
      FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar)
    input
    (admissible : Quantitative.AdmissibleInput
      (IFT.implicitFunction (selectedFederbushClosure inputs)) input)
    candidate →
  Quantitative.InBall
    (Quantitative.contractionBall
      (IFT.implicitFunction (selectedFederbushClosure inputs)) input)
    candidate →
  Quantitative.ResidualZero
    (IFT.implicitFunction (selectedFederbushClosure inputs))
    input candidate →
  candidate ≡ Quantitative.implicitSolution
    (IFT.implicitFunction (selectedFederbushClosure inputs))
    input admissible
federbushSolutionUniqueFromIntegratedInputs inputs =
  IFT.federbushAverageUniqueOnQuantitativeBall
    (selectedFederbushClosure inputs)

backgroundSliceUniqueFromIntegratedInputs :
  ∀ {Point FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar}
    (inputs : PhysicalClosureRound2Inputs Point
      FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar)
    tree
    (admissible : Quantitative.AdmissibleInput
      (IFT.implicitFunction (selectedBackgroundClosure inputs)) tree)
    candidate →
  Quantitative.InBall
    (Quantitative.contractionBall
      (IFT.implicitFunction (selectedBackgroundClosure inputs)) tree)
    candidate →
  Quantitative.ResidualZero
    (IFT.implicitFunction (selectedBackgroundClosure inputs))
    tree candidate →
  candidate ≡ Slice.toBackground
    (IFT.transition (selectedBackgroundClosure inputs)) tree
backgroundSliceUniqueFromIntegratedInputs inputs =
  IFT.backgroundSliceUniqueOnQuantitativeBall
    (selectedBackgroundClosure inputs)

centreDifferentialLeftInverseFromIntegratedInputs :
  ∀ {Point FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar}
    (inputs : PhysicalClosureRound2Inputs Point
      FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar) →
  ∀ vector →
  Quantitative.inverse
    (Inverse.finiteSquare (Inverse.closure (centreInverse inputs)))
    (Quantitative.operator
      (Inverse.relativeKernel
        (Inverse.closure (centreInverse inputs))) vector)
  ≡ vector
centreDifferentialLeftInverseFromIntegratedInputs inputs =
  Inverse.relativeFiniteInverseLeftLaw
    (Inverse.closure (centreInverse inputs))
    (centreZeroAgreement inputs)

faddeevPopovRightInverseFromIntegratedInputs :
  ∀ {Point FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar}
    (inputs : PhysicalClosureRound2Inputs Point
      FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar) →
  ∀ vector →
  Quantitative.operator
    (Inverse.relativeKernel
      (Inverse.closure (faddeevPopovInverse inputs)))
    (Quantitative.inverse
      (Inverse.finiteSquare
        (Inverse.closure (faddeevPopovInverse inputs))) vector)
  ≡ vector
faddeevPopovRightInverseFromIntegratedInputs inputs =
  Inverse.relativeFiniteInverseRightLaw
    (Inverse.closure (faddeevPopovInverse inputs))
    (faddeevPopovZeroAgreement inputs)

cmp109EntryNormBoundFromIntegratedInputs :
  ∀ {Point FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar}
    (inputs : PhysicalClosureRound2Inputs Point
      FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar) →
  Norm.LessEqual (Norm.algebra (entryPipeline inputs))
    (Norm.operatorNorm (Norm.algebra (entryPipeline inputs))
      (Norm.assembledDerivativeEntryOperator (entryPipeline inputs)))
    (Norm.entryBound (entryPipeline inputs))
cmp109EntryNormBoundFromIntegratedInputs inputs =
  Norm.assembledDerivativeEntryNormBound (entryPipeline inputs)

hrBetaUniformHalfBoundFromIntegratedInputs :
  ∀ {Point FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar}
    (inputs : PhysicalClosureRound2Inputs Point
      FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar) →
  HRBase.LessEqual (HR.algebra (HR.channels (hrBeta inputs)))
    (HRBase.absolute (HR.algebra (HR.channels (hrBeta inputs)))
      (HR.totalRemainder (HR.channels (hrBeta inputs))))
    (HR.PhysicalHalf (hrBeta inputs) (HR.Delta (hrBeta inputs)))
hrBetaUniformHalfBoundFromIntegratedInputs inputs =
  HR.physicalFiveChannelUniformHRBeta (hrBeta inputs)

contourEndpointIndependentFromIntegratedInputs :
  ∀ {Point FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar}
    (inputs : PhysicalClosureRound2Inputs Point
      FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      CentreTangent GaugeParameter Operator Bound Cell Scalar)
    order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (contourDisplacement inputs)) →
  ∀ point →
  Contours.follow (contourAction inputs) point order
  ≡ Contours.follow (contourAction inputs) point
      (Contours.activeSegments (contourDisplacement inputs))
contourEndpointIndependentFromIntegratedInputs inputs order membership =
  Contours.cmp109EnumeratedContourEndpointExact
    (contourAction inputs)
    (contourDisplacement inputs)
    order membership

physicalClosureRound2IntegratedCarrierLevel : ProofLevel
physicalClosureRound2IntegratedCarrierLevel = machineChecked

physicalClosureRound2IntegratedIFTConsequencesLevel : ProofLevel
physicalClosureRound2IntegratedIFTConsequencesLevel = machineChecked

physicalClosureRound2IntegratedInverseConsequencesLevel : ProofLevel
physicalClosureRound2IntegratedInverseConsequencesLevel = machineChecked

physicalClosureRound2IntegratedNormAndRemainderLevel : ProofLevel
physicalClosureRound2IntegratedNormAndRemainderLevel = machineChecked
