module DASHI.Physics.YangMills.BalabanClayGate4GaugeClusterLocalInfluenceExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4DimockClusterWithHolesLocalInfluenceExact as Cluster

------------------------------------------------------------------------
-- Gauge weakening parameters and cluster local influence.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban. II. Large Fields",
-- Journal of Mathematical Physics 54 (9) (2013), article 092301.
-- arXiv:1212.5562v2. DOI: 10.1063/1.4821275.
--
-- A derivative with respect to a boundary weakening parameter must vanish when
-- the activity support is separated from that boundary.  This is the literal
-- support theorem required before a cluster can be classified as leading,
-- tiny or boundary-dependent; it is not inferred from a numerical smallness
-- estimate.
------------------------------------------------------------------------

data Empty : Set where

Not : Set → Set
Not proposition = proposition → Empty

infix 4 _≢_
_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = Not (left ≡ right)

record GaugeWeakeningLocalInfluence
    (Cluster Boundary Parameter Derivative : Set) : Set₁ where
  field
    supportTouches : Cluster → Boundary → Set
    separated : Cluster → Boundary → Set

    weakeningParameter : Boundary → Parameter
    activityDerivative : Cluster → Parameter → Derivative
    zeroDerivative : Derivative

    separatedMeansNoTouch : ∀ cluster boundary →
      separated cluster boundary →
      Not (supportTouches cluster boundary)

    derivativeVanishesWhenSeparated : ∀ cluster boundary →
      separated cluster boundary →
      activityDerivative cluster (weakeningParameter boundary)
      ≡ zeroDerivative

    nonzeroDerivativeForcesTouch : ∀ cluster boundary →
      activityDerivative cluster (weakeningParameter boundary)
      ≢ zeroDerivative →
      supportTouches cluster boundary

open GaugeWeakeningLocalInfluence public

record GaugeClusterWithHolesInputs
    (ClusterIndex Boundary Parameter Derivative Scalar : Set) : Set₁ where
  field
    influence : GaugeWeakeningLocalInfluence
      ClusterIndex Boundary Parameter Derivative

    genericCluster :
      Cluster.ClusterWithHolesLocalInfluenceData ClusterIndex Scalar

    BoundaryWitness : ClusterIndex → Set
    boundaryWitnessMeaning : ∀ cluster →
      BoundaryWitness cluster →
      Cluster.touchesHoleBoundary genericCluster cluster

    LeadingDerivativeSupportMeaning : Set
    TinyDerivativeSupportMeaning : Set

    leadingDerivativeSupportMeaning : LeadingDerivativeSupportMeaning
    tinyDerivativeSupportMeaning : TinyDerivativeSupportMeaning

open GaugeClusterWithHolesInputs public

gaugeClusterCorrectionEstimate :
  ∀ {ClusterIndex Boundary Parameter Derivative Scalar}
    (inputs : GaugeClusterWithHolesInputs
      ClusterIndex Boundary Parameter Derivative Scalar) →
  Cluster.LessEqual (Cluster.algebra (genericCluster inputs))
    (Cluster.absolute (Cluster.algebra (genericCluster inputs))
      (Cluster.correctionLog (genericCluster inputs)))
    (Cluster.add (Cluster.algebra (genericCluster inputs))
      (Cluster.tinyBudget (genericCluster inputs))
      (Cluster.boundaryBudget (genericCluster inputs)))
gaugeClusterCorrectionEstimate inputs =
  Cluster.clusterWithHolesCorrectionEstimate (genericCluster inputs)

gaugeWeakeningDerivativeSupportLevel : ProofLevel
gaugeWeakeningDerivativeSupportLevel = machineChecked

gaugeClusterCorrectionReuseLevel : ProofLevel
gaugeClusterCorrectionReuseLevel = machineChecked

physicalGaugeWeakeningDerivativeInputsLevel : ProofLevel
physicalGaugeWeakeningDerivativeInputsLevel = conditional

physicalGaugeBoundaryClusterClassificationInputsLevel : ProofLevel
physicalGaugeBoundaryClusterClassificationInputsLevel = conditional
