module DASHI.Physics.YangMills.BalabanClayGate4DimockClusterWithHolesLocalInfluenceExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact leading/tiny/boundary split for a cluster expansion with holes.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - II. Large Fields",
-- arXiv:1212.5562v2 [math-ph]. No DOI recorded.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Dimock, Lemmas 3.18--3.21, first exponentiates the ultralocal fluctuation
-- integral and then separates boundary-dependent clusters, tiny remainders and
-- the leading normalized activity.  The local-influence property says that a
-- cluster wholly inside the small-field region cannot depend on the boundary
-- interpolation variable.  This module records that support statement and
-- proves the exact correction budget from the tiny and boundary estimates.
------------------------------------------------------------------------

record ClusterCorrectionAlgebra (Scalar : Set) : Set₁ where
  field
    add : Scalar → Scalar → Scalar
    absolute : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)
    absoluteTriangle : ∀ left right →
      LessEqual (absolute (add left right))
        (add (absolute left) (absolute right))

open ClusterCorrectionAlgebra public

record ClusterWithHolesLocalInfluenceData
    (Cluster Scalar : Set) : Set₁ where
  field
    algebra : ClusterCorrectionAlgebra Scalar

    leadingCluster tinyCluster boundaryCluster : Cluster → Set
    touchesHoleBoundary : Cluster → Set

    localInfluenceLeading : ∀ cluster →
      leadingCluster cluster → Set
    localInfluenceTiny : ∀ cluster →
      tinyCluster cluster → Set
    boundaryClustersTouchHole : ∀ cluster →
      boundaryCluster cluster → touchesHoleBoundary cluster

    leadingLog tinyLog boundaryLog fullLog : Scalar
    tinyBudget boundaryBudget : Scalar

    fullLogMeaning :
      fullLog ≡ add algebra leadingLog
        (add algebra tinyLog boundaryLog)

    tinyEstimate :
      LessEqual algebra (absolute algebra tinyLog) tinyBudget

    boundaryEstimate :
      LessEqual algebra (absolute algebra boundaryLog) boundaryBudget

  correctionLog : Scalar
  correctionLog = add algebra tinyLog boundaryLog

open ClusterWithHolesLocalInfluenceData public

clusterWithHolesCorrectionEstimate :
  ∀ {Cluster Scalar}
    (dataSet : ClusterWithHolesLocalInfluenceData Cluster Scalar) →
  LessEqual (algebra dataSet)
    (absolute (algebra dataSet) (correctionLog dataSet))
    (add (algebra dataSet)
      (tinyBudget dataSet)
      (boundaryBudget dataSet))
clusterWithHolesCorrectionEstimate dataSet =
  transitive (algebra dataSet)
    (absoluteTriangle (algebra dataSet)
      (tinyLog dataSet) (boundaryLog dataSet))
    (addMonotone (algebra dataSet)
      (tinyEstimate dataSet)
      (boundaryEstimate dataSet))

fullClusterLogAsLeadingPlusControlledCorrection :
  ∀ {Cluster Scalar}
    (dataSet : ClusterWithHolesLocalInfluenceData Cluster Scalar) →
  fullLog dataSet
  ≡ add (algebra dataSet)
      (leadingLog dataSet)
      (correctionLog dataSet)
fullClusterLogAsLeadingPlusControlledCorrection dataSet =
  fullLogMeaning dataSet

record ClusterCorrectionAbsorption
    {Cluster Scalar : Set}
    (dataSet : ClusterWithHolesLocalInfluenceData Cluster Scalar) : Set₁ where
  field
    correctionAllowance : Scalar
    tinyAndBoundaryBelowAllowance :
      LessEqual (algebra dataSet)
        (add (algebra dataSet)
          (tinyBudget dataSet)
          (boundaryBudget dataSet))
        correctionAllowance

open ClusterCorrectionAbsorption public

clusterWithHolesCorrectionAbsorbed :
  ∀ {Cluster Scalar}
    {dataSet : ClusterWithHolesLocalInfluenceData Cluster Scalar} →
  (absorption : ClusterCorrectionAbsorption dataSet) →
  LessEqual (algebra dataSet)
    (absolute (algebra dataSet) (correctionLog dataSet))
    (correctionAllowance absorption)
clusterWithHolesCorrectionAbsorbed {dataSet = dataSet} absorption =
  transitive (algebra dataSet)
    (clusterWithHolesCorrectionEstimate dataSet)
    (tinyAndBoundaryBelowAllowance absorption)

dimockClusterWithHolesSplitLevel : ProofLevel
dimockClusterWithHolesSplitLevel = machineChecked

dimockClusterLocalInfluenceVocabularyLevel : ProofLevel
dimockClusterLocalInfluenceVocabularyLevel = machineChecked

dimockClusterWithHolesSourceLevel : ProofLevel
dimockClusterWithHolesSourceLevel = standardImported

physicalYangMillsClusterLocalInfluenceInputsLevel : ProofLevel
physicalYangMillsClusterLocalInfluenceInputsLevel = conditional

physicalYangMillsTinyAndBoundaryClusterInputsLevel : ProofLevel
physicalYangMillsTinyAndBoundaryClusterInputsLevel = conditional
