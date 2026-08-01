module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound4IntegratedExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109SiteWeightIdentificationExact as CMP109
import DASHI.Physics.YangMills.BalabanClayGate4SU2PauliNormConventionExact as Pauli
import DASHI.Physics.YangMills.BalabanClayGate4SU2HalfRadiusScalarEnvelopeExact as HalfRadius
import DASHI.Physics.YangMills.BalabanClayGate4ConservativeDyadicNewtonBudgetExact as Newton
import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeContractionBallConstructionExact as Ball
import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalHessianFromFactorizationsExact as Hessian
import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSelfAdjointOperatorBoundExact as FiveBound
import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSixteenthBudgetExact as Sixteenth
import DASHI.Physics.YangMills.BalabanClayGate4SelfAdjointFormOperatorNormExact as FormNorm
import DASHI.Physics.YangMills.BalabanClayGate4DimockNormalizedPolymerReblockingExact as Reblocking
import DASHI.Physics.YangMills.BalabanClayGate4GaugeTaylorLocalizationExact as Taylor
import DASHI.Physics.YangMills.BalabanClayGate4GaugeLargeFieldPenaltyExact as LargeField
import DASHI.Physics.YangMills.BalabanClayGate4GaugeClusterLocalInfluenceExact as Cluster
import DASHI.Physics.YangMills.BalabanClayGate4GaugeRootedEntropyDecayExact as Rooted
import DASHI.Physics.YangMills.BalabanClayGate4GaugeHRBetaFiveActivityAllocationExact as Activity
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaDimockLocalizationAdapterExact as HRAdapter
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaLocalToUniformExact as HRBase
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaFiveLocalChannelsExact as HRFive
import DASHI.Physics.YangMills.BalabanClayGate4DimockConnectedActivityStabilityExact as Dimock

------------------------------------------------------------------------
-- Physical closure round four: one consumer for the four remaining lanes.
--
-- This record owns:
--
-- * the literal CMP109 site, contour and weight identification;
-- * one Pauli norm, one half-radius scalar ledger and the shared BF/FP Newton
--   budget;
-- * the literal factorized five-channel Hessian and one-sixteenth allocation;
-- * gauge Taylor extraction, bad-block suppression, cluster local influence,
--   rooted entropy/decay summability and the five-activity H-R_beta allocation.
--
-- The record does not manufacture the final Yang--Mills estimates.  It makes
-- their dependencies coherent and proves every finite/algebraic consequence,
-- so a physical instantiation cannot mix radii, operators or budget ledgers.
------------------------------------------------------------------------

record PhysicalClosureRound4Inputs
    (radius : Nat)
    (FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP
      Operator State HessianBound
      ActivityType ReblockingScalar
      Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar : Set) : Set₂ where
  field
    cmp109Identification :
      CMP109.CMP109Equations003To012Identification
        radius FineSite CoarseSite Spacing FineBond CoarseBond Path
        AverageScalar AverageValue Input Output

    pauliConvention :
      Pauli.PauliSU2NormConvention Lie Vector SU2Scalar

    pauliAdjointNorm :
      Pauli.PauliAdjointOperatorNormMeaning Lie Vector SU2Scalar

    pauliConventionAgrees :
      Pauli.convention pauliAdjointNorm ≡ pauliConvention

    scalarEnvelope :
      HalfRadius.SU2HalfRadiusScalarEnvelope SU2Scalar

    scalarNumericalLedger :
      HalfRadius.SU2HalfRadiusNumericalLedger SU2Scalar

    scalarLedgerAgrees :
      HalfRadius.envelope scalarNumericalLedger ≡ scalarEnvelope

    triangleBF : Ball.MetricTriangleBudget PointBF SU2Scalar
    triangleFP : Ball.MetricTriangleBudget PointFP SU2Scalar

    newtonConstantsBF : Newton.DyadicNewtonConstants triangleBF
    newtonConstantsFP : Newton.DyadicNewtonConstants triangleFP

    newtonReuse :
      Newton.FederbushFaddeevPopovDyadicNewtonReuse
        newtonConstantsBF newtonConstantsFP

    factorizedHessian :
      Hessian.PhysicalHessianFactorizedInputs
        Operator State HessianBound

    hessianFormMeaning :
      FiveBound.FiveChannelSelfAdjointNormMeaning
        Operator State HessianBound

    physicalFormTotalMeaning :
      FiveBound.total (FiveBound.formData hessianFormMeaning)
      ≡ Hessian.totalRemainder factorizedHessian

    channelAllocation :
      Sixteenth.FiveChannelSixteenthAllocation
        (FiveBound.formData hessianFormMeaning)

    gaugeTaylor :
      Taylor.GaugeNormalizedReblockingInputs
        ActivityType ReblockingScalar

    gaugeLargeField :
      LargeField.GaugeLargeFieldPenaltyInputs
        Scale Block Configuration LargeFieldScalar

    gaugeCluster :
      Cluster.GaugeClusterWithHolesInputs
        ClusterIndex Boundary Parameter Derivative ClusterScalar

    rootedDecay : Rooted.RootedEntropyDecayData RootedScalar
    rootedSummability :
      Rooted.UniformRootedGeometricSummability rootedDecay

    hrNormalization :
      HRFive.PhysicalFiveChannelHRBetaNormalization Cell HRScalar

    connectedActivities :
      Dimock.ConnectedActivityStabilityData Polymer HRScalar

    fiveActivityHalf :
      Activity.GaugeFiveActivityPhysicalHalfInputs
        hrNormalization connectedActivities

open PhysicalClosureRound4Inputs public

cmp109ExecutableEqualsPrintedEquation004 :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar}
    (inputs : PhysicalClosureRound4Inputs
      radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar) →
  CMP109.executableMap (cmp109Identification inputs)
  ≡ CMP109.printedEquation004Map (cmp109Identification inputs)
cmp109ExecutableEqualsPrintedEquation004 inputs =
  CMP109.executableEqualsPrintedEquation004
    (cmp109Identification inputs)

pauliBracketBoundFromRound4 :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar}
    (inputs : PhysicalClosureRound4Inputs
      radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar)
    left right →
  Pauli.LessEqual (Pauli.vectorGeometry (pauliConvention inputs))
    (Pauli.lieNorm (pauliConvention inputs)
      (Pauli.bracket (pauliConvention inputs) left right))
    (Pauli.multiply (Pauli.vectorGeometry (pauliConvention inputs))
      (Pauli.lieNorm (pauliConvention inputs) left)
      (Pauli.lieNorm (pauliConvention inputs) right))
pauliBracketBoundFromRound4 inputs =
  Pauli.pauliBracketNormBound (pauliConvention inputs)

federbushInvariantBallFromRound4 :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar}
    (inputs : PhysicalClosureRound4Inputs
      radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar) →
  Quantitative.InvariantContractionBall
    (Ball.metric (triangleBF inputs))
federbushInvariantBallFromRound4 inputs =
  Ball.asInvariantContractionBall
    (Newton.asContractionBallConstruction
      (Newton.federbushCentre (newtonReuse inputs)))

faddeevPopovInvariantBallFromRound4 :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar}
    (inputs : PhysicalClosureRound4Inputs
      radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar) →
  Quantitative.InvariantContractionBall
    (Ball.metric (triangleFP inputs))
faddeevPopovInvariantBallFromRound4 inputs =
  Ball.asInvariantContractionBall
    (Newton.asContractionBallConstruction
      (Newton.faddeevPopovSlice (newtonReuse inputs)))

physicalHessianSelfAdjointFromRound4 :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar}
    (inputs : PhysicalClosureRound4Inputs
      radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar) →
  FiveBound.SelfAdjoint
    (Hessian.formAlgebra (factorizedHessian inputs))
    (Hessian.fullHessian (factorizedHessian inputs))
physicalHessianSelfAdjointFromRound4 inputs =
  Hessian.factorizedPhysicalHessianSelfAdjoint
    (factorizedHessian inputs)

physicalRemainderNormBelowHalfFromRound4 :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar}
    (inputs : PhysicalClosureRound4Inputs
      radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar) →
  FormNorm.LessEqual (FiveBound.normData (hessianFormMeaning inputs))
    (FormNorm.operatorNorm (FiveBound.normData (hessianFormMeaning inputs))
      (Hessian.totalRemainder (factorizedHessian inputs)))
    (Sixteenth.half (Sixteenth.budget (channelAllocation inputs)))
physicalRemainderNormBelowHalfFromRound4 inputs =
  subst
    (λ operator →
      FormNorm.LessEqual (FiveBound.normData (hessianFormMeaning inputs))
        (FormNorm.operatorNorm
          (FiveBound.normData (hessianFormMeaning inputs)) operator)
        (Sixteenth.half
          (Sixteenth.budget (channelAllocation inputs))))
    (physicalFormTotalMeaning inputs)
    (Sixteenth.selfAdjointRemainderNormBelowHalf
      (hessianFormMeaning inputs) (channelAllocation inputs))

gaugeTaylorContractionFromRound4 :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar}
    (inputs : PhysicalClosureRound4Inputs
      radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar) →
  let dataSet = Taylor.genericReblocking (gaugeTaylor inputs)
      certificate = Taylor.contraction (gaugeTaylor inputs)
  in Reblocking.LessEqual (Reblocking.algebra dataSet)
      (Reblocking.normalizedReblockedNorm dataSet)
      (Reblocking.multiply (Reblocking.algebra dataSet)
        (Reblocking.targetContraction certificate)
        (Reblocking.currentNorm dataSet))
gaugeTaylorContractionFromRound4 inputs =
  Taylor.gaugeNormalizedReblockingContraction (gaugeTaylor inputs)

allFiniteRootedSumsFromRound4 :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar}
    (inputs : PhysicalClosureRound4Inputs
      radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar)
    depth →
  Rooted.LessEqual (Rooted.algebra (rootedDecay inputs))
    (Rooted.rootedShellPartialSum
      (Rooted.algebra (rootedDecay inputs))
      (Rooted.shellActivity (rootedDecay inputs)) depth)
    (Rooted.rootedAllowance (rootedSummability inputs))
allFiniteRootedSumsFromRound4 inputs =
  Rooted.allFiniteRootedShellSumsBelowAllowance
    (rootedSummability inputs)

hrBetaPhysicalHalfFromRound4 :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar}
    (inputs : PhysicalClosureRound4Inputs
      radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      AverageScalar AverageValue Input Output
      Lie Vector SU2Scalar PointBF PointFP Operator State HessianBound
      ActivityType ReblockingScalar Scale Block Configuration LargeFieldScalar
      ClusterIndex Boundary Parameter Derivative ClusterScalar
      Polymer RootedScalar Cell HRScalar) →
  HRBase.LessEqual (HRFive.algebra (HRFive.channels (hrNormalization inputs)))
    (HRBase.absolute (HRFive.algebra (HRFive.channels (hrNormalization inputs)))
      (HRFive.totalRemainder (HRFive.channels (hrNormalization inputs))))
    (HRFive.PhysicalHalf (hrNormalization inputs)
      (HRFive.Delta (hrNormalization inputs)))
hrBetaPhysicalHalfFromRound4 inputs =
  HRAdapter.localizedConnectedActivitiesGivePhysicalHalf
    (Activity.asHRBetaDimockLocalizationInputs (fiveActivityHalf inputs))

physicalClosureRound4IntegratedCarrierLevel : ProofLevel
physicalClosureRound4IntegratedCarrierLevel = machineChecked

physicalClosureRound4CMP109IdentificationLevel : ProofLevel
physicalClosureRound4CMP109IdentificationLevel = machineChecked

physicalClosureRound4NewtonReuseLevel : ProofLevel
physicalClosureRound4NewtonReuseLevel = machineChecked

physicalClosureRound4HessianAndBudgetLevel : ProofLevel
physicalClosureRound4HessianAndBudgetLevel = machineChecked

physicalClosureRound4GaugePolymerConsequencesLevel : ProofLevel
physicalClosureRound4GaugePolymerConsequencesLevel = machineChecked
