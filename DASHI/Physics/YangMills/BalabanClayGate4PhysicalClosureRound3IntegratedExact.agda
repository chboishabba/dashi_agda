module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound3IntegratedExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embedding
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredEndpointCertificateExact as EndpointCertificate
import DASHI.Physics.YangMills.BalabanClayGate4SU2FixedRadiusEnvelopeExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4DimockNormalizedPolymerReblockingExact as Reblocking
import DASHI.Physics.YangMills.BalabanClayGate4DimockLargeFieldSuppressionExact as LargeField
import DASHI.Physics.YangMills.BalabanClayGate4DimockClusterWithHolesLocalInfluenceExact as Cluster
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaDimockLocalizationAdapterExact as HRBeta
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaLocalToUniformExact as HRBase
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaFiveLocalChannelsExact as Five
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalOperatorChannelIdentificationExact as Channels
import DASHI.Physics.YangMills.BalabanClayGate4SU2QuadraticChartDefectExact as Quadratic

------------------------------------------------------------------------
-- One coherent consumer for the Dimock/centred-geometry closure tranche.
--
-- The record owns the literal centred block, its injective periodic embedding,
-- executable certificates for every printed contour endpoint, one SU(2) chart
-- radius, normalized polymer reblocking, large-field slack, cluster-with-holes
-- correction, connected H-R_beta activities and the physical channel naming
-- map.  This prevents later consumers from mixing incompatible radii, endpoint
-- conventions, polymer norms or channel allocations.
------------------------------------------------------------------------

record PhysicalClosureRound3Inputs
    (n radius : Nat)
    (SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator : Set) : Set₁ where
  field
    centeredBlock : Centered.CMP109CenteredBlockConvention radius
    centeredEmbedding : Embedding.CenteredPeriodicNoWrapEmbedding n radius

    centeredEndpointCertificates :
      ∀ point →
      EndpointCertificate.CenteredEndpointCertificate n radius
        (Embedding.embeddingCentre centeredEmbedding) point

    su2Envelope : SU2.SU2FixedRadiusEnvelope SU2Operator SU2Scalar

    normalizedReblocking :
      Reblocking.NormalizedPolymerReblockingData ReblockingScalar
    normalizedReblockingContraction :
      Reblocking.ContractiveNormalizedReblocking normalizedReblocking

    largeFieldBudgets :
      LargeField.MultiscaleLargeFieldBudget Scale LargeFieldScalar
    selectedScale : Scale

    clusterWithHoles :
      Cluster.ClusterWithHolesLocalInfluenceData ClusterIndex ClusterScalar
    clusterCorrectionAbsorption :
      Cluster.ClusterCorrectionAbsorption clusterWithHoles

    hrBetaLocalization :
      HRBeta.HRBetaDimockLocalizationInputs Cell Polymer HRScalar

    channelIdentification :
      Channels.PhysicalChannelOperatorIdentification PhysicalOperator

open PhysicalClosureRound3Inputs public

centeredPrintedContourEndpointFromRound3 :
  ∀ {n radius SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator}
    (inputs : PhysicalClosureRound3Inputs n radius
      SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator)
    point order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (Embedding.centeredDisplacement4 point)) →
  Bond.walk
      (Embedding.embeddingCentre (centeredEmbedding inputs))
      (Periodic.contourWord order)
  ≡ Embedding.embed (centeredEmbedding inputs) point
centeredPrintedContourEndpointFromRound3 inputs point order membership =
  trans
    (EndpointCertificate.certifiedCenteredContourEndpointExact
      (centeredEndpointCertificates inputs point)
      order membership)
    (sym (Embedding.embedMeaning (centeredEmbedding inputs) point))

su2AdDefectBoundFromRound3 :
  ∀ {n radius SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator}
    (inputs : PhysicalClosureRound3Inputs n radius
      SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator) →
  Quadratic.LessEqual
    (Quadratic.algebra (SU2.quadratic (su2Envelope inputs)))
    (Quadratic.operatorNorm
      (Quadratic.algebra (SU2.quadratic (su2Envelope inputs)))
      (Quadratic.adMinusIdentity
        (SU2.quadratic (su2Envelope inputs))))
    (SU2.adDefectEnvelope (su2Envelope inputs))
su2AdDefectBoundFromRound3 inputs =
  SU2.adMinusIdentityBelowFixedRadiusEnvelope (su2Envelope inputs)

su2DexpDefectBoundFromRound3 :
  ∀ {n radius SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator}
    (inputs : PhysicalClosureRound3Inputs n radius
      SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator) →
  Quadratic.LessEqual
    (Quadratic.algebra (SU2.quadratic (su2Envelope inputs)))
    (Quadratic.operatorNorm
      (Quadratic.algebra (SU2.quadratic (su2Envelope inputs)))
      (Quadratic.dexpMinusIdentity
        (SU2.quadratic (su2Envelope inputs))))
    (SU2.dexpDefectEnvelope (su2Envelope inputs))
su2DexpDefectBoundFromRound3 inputs =
  SU2.dexpMinusIdentityBelowFixedRadiusEnvelope (su2Envelope inputs)

normalizedReblockingContractionFromRound3 :
  ∀ {n radius SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator}
    (inputs : PhysicalClosureRound3Inputs n radius
      SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator) →
  Reblocking.LessEqual (Reblocking.algebra (normalizedReblocking inputs))
    (Reblocking.normalizedReblockedNorm (normalizedReblocking inputs))
    (Reblocking.multiply (Reblocking.algebra (normalizedReblocking inputs))
      (Reblocking.targetContraction
        (normalizedReblockingContraction inputs))
      (Reblocking.currentNorm (normalizedReblocking inputs)))
normalizedReblockingContractionFromRound3 inputs =
  Reblocking.normalizedReblockingBelowTargetContraction
    (normalizedReblockingContraction inputs)

largeFieldSlackFromRound3 :
  ∀ {n radius SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator}
    (inputs : PhysicalClosureRound3Inputs n radius
      SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator) →
  LargeField.LessEqual
    (LargeField.algebra
      (LargeField.budgetAt (largeFieldBudgets inputs)
        (selectedScale inputs)))
    (LargeField.natScale
      (LargeField.algebra
        (LargeField.budgetAt (largeFieldBudgets inputs)
          (selectedScale inputs)))
      (LargeField.add
        (LargeField.algebra
          (LargeField.budgetAt (largeFieldBudgets inputs)
            (selectedScale inputs)))
        (LargeField.entropyPerBadCube
          (LargeField.budgetAt (largeFieldBudgets inputs)
            (selectedScale inputs)))
        (LargeField.reservedSlackPerBadCube
          (LargeField.budgetAt (largeFieldBudgets inputs)
            (selectedScale inputs))))
      (LargeField.badCubeCountAt (largeFieldBudgets inputs)
        (selectedScale inputs)))
    (LargeField.natScale
      (LargeField.algebra
        (LargeField.budgetAt (largeFieldBudgets inputs)
          (selectedScale inputs)))
      (LargeField.penaltyPerBadCube
        (LargeField.budgetAt (largeFieldBudgets inputs)
          (selectedScale inputs)))
      (LargeField.badCubeCountAt (largeFieldBudgets inputs)
        (selectedScale inputs)))
largeFieldSlackFromRound3 inputs =
  LargeField.multiscaleLargeFieldSlackAt
    (largeFieldBudgets inputs) (selectedScale inputs)

clusterCorrectionBoundFromRound3 :
  ∀ {n radius SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator}
    (inputs : PhysicalClosureRound3Inputs n radius
      SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator) →
  Cluster.LessEqual (Cluster.algebra (clusterWithHoles inputs))
    (Cluster.absolute (Cluster.algebra (clusterWithHoles inputs))
      (Cluster.correctionLog (clusterWithHoles inputs)))
    (Cluster.correctionAllowance (clusterCorrectionAbsorption inputs))
clusterCorrectionBoundFromRound3 inputs =
  Cluster.clusterWithHolesCorrectionAbsorbed
    (clusterCorrectionAbsorption inputs)

hrBetaPhysicalHalfFromRound3 :
  ∀ {n radius SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator}
    (inputs : PhysicalClosureRound3Inputs n radius
      SU2Operator SU2Scalar ReblockingScalar
      Scale LargeFieldScalar ClusterIndex ClusterScalar
      Cell Polymer HRScalar PhysicalOperator) →
  HRBase.LessEqual
    (Five.algebra
      (Five.channels
        (HRBeta.normalization (hrBetaLocalization inputs))))
    (HRBase.absolute
      (Five.algebra
        (Five.channels
          (HRBeta.normalization (hrBetaLocalization inputs))))
      (Five.totalRemainder
        (Five.channels
          (HRBeta.normalization (hrBetaLocalization inputs)))))
    (Five.PhysicalHalf
      (HRBeta.normalization (hrBetaLocalization inputs))
      (Five.Delta
        (HRBeta.normalization (hrBetaLocalization inputs))))
hrBetaPhysicalHalfFromRound3 inputs =
  HRBeta.localizedConnectedActivitiesGivePhysicalHalf
    (hrBetaLocalization inputs)

physicalClosureRound3IntegratedCarrierLevel : ProofLevel
physicalClosureRound3IntegratedCarrierLevel = machineChecked

physicalClosureRound3CenteredEndpointLevel : ProofLevel
physicalClosureRound3CenteredEndpointLevel = machineChecked

physicalClosureRound3SU2AndPolymerConsequencesLevel : ProofLevel
physicalClosureRound3SU2AndPolymerConsequencesLevel = machineChecked

physicalClosureRound3HRBetaConsequenceLevel : ProofLevel
physicalClosureRound3HRBetaConsequenceLevel = machineChecked
