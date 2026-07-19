module DASHI.Biology.IntersectionalLongitudinalProxyTransitionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Residual
import DASHI.Biology.LongitudinalFMRIConnectomeDynamicsBridge as Imaging
import DASHI.Biology.InterventionConsentLongitudinalGovernance as Consent

------------------------------------------------------------------------
-- Intersectional longitudinal proxy-transition bridge.
--
-- This is the focused bridge missing between the existing axis-indexed
-- residual atlas, the population-over-time fMRI/connectome proxy lane, and
-- the consent-governed +1 transition lane.
--
-- It proves only structural preservation claims:
--   * longitudinal cohort observations retain their intersectional axes,
--   * population/time aggregation can raise a proxy to trajectory evidence,
--   * trajectory evidence does not become mechanism, diagnosis, treatment,
--     mind-reading, or hidden-chart recovery,
--   * a +1 handle changes admissible transitions only under consent gates.


data Never : Set where

------------------------------------------------------------------------
-- Axis preservation.


data AxisPreservingProjection :
  List Residual.IntersectionalAxis →
  List Residual.IntersectionalAxis →
  Set where
  preserveAxes :
    {axes : List Residual.IntersectionalAxis} →
    AxisPreservingProjection axes axes

canonicalAxesCannotProjectToEmpty :
  AxisPreservingProjection Residual.canonicalIntersectionalAxes [] →
  Never
canonicalAxesCannotProjectToEmpty ()

canonicalAxisProjection :
  AxisPreservingProjection
    Residual.canonicalIntersectionalAxes
    Residual.canonicalIntersectionalAxes
canonicalAxisProjection = preserveAxes

------------------------------------------------------------------------
-- Claim ladder.


data ProxyClaimLevel : Set where
  singleSessionProxy : ProxyClaimLevel
  longitudinalWithinSubjectProxy : ProxyClaimLevel
  populationTrajectoryCandidate : ProxyClaimLevel
  multimodalMechanismCandidate : ProxyClaimLevel
  causalMechanismPromotion : ProxyClaimLevel

AdmissibleProxyClaimLevel : ProxyClaimLevel → Set
AdmissibleProxyClaimLevel singleSessionProxy = ⊤
AdmissibleProxyClaimLevel longitudinalWithinSubjectProxy = ⊤
AdmissibleProxyClaimLevel populationTrajectoryCandidate = ⊤
AdmissibleProxyClaimLevel multimodalMechanismCandidate = ⊤
AdmissibleProxyClaimLevel causalMechanismPromotion = Never

causalMechanismPromotionRejected :
  AdmissibleProxyClaimLevel causalMechanismPromotion →
  Never
causalMechanismPromotionRejected impossible = impossible

------------------------------------------------------------------------
-- Local hypervoxel and trajectory rows.

record AxisIndexedHypervoxel : Set where
  constructor mkAxisIndexedHypervoxel
  field
    voxelBody : String
    voxelTime : Nat
    voxelPlace : String
    voxelRelation : String
    voxelInstitution : String
    voxelAxes : List Residual.IntersectionalAxis
    voxelAxesAreCanonical :
      voxelAxes ≡ Residual.canonicalIntersectionalAxes
    voxelAxisFree : Bool
    voxelAxisFreeIsFalse : voxelAxisFree ≡ false

open AxisIndexedHypervoxel public

canonicalAxisIndexedHypervoxel : AxisIndexedHypervoxel
canonicalAxisIndexedHypervoxel =
  mkAxisIndexedHypervoxel
    "body-memory carrier"
    zero
    "situated place"
    "situated relation"
    "situated institution"
    Residual.canonicalIntersectionalAxes
    refl
    false
    refl

record PopulationTrajectoryObservation : Set where
  constructor mkPopulationTrajectoryObservation
  field
    observationHypervoxel : AxisIndexedHypervoxel
    observationPopulationSize : Nat
    observationTimepoints : Nat
    observationClaimLevel : ProxyClaimLevel
    observationClaimLevelIsTrajectoryCandidate :
      observationClaimLevel ≡ populationTrajectoryCandidate
    observationClaimLevelAdmissible :
      AdmissibleProxyClaimLevel observationClaimLevel
    observationAxesPreserved :
      AxisPreservingProjection
        (voxelAxes observationHypervoxel)
        Residual.canonicalIntersectionalAxes
    observationMechanismPromoted : Bool
    observationMechanismPromotedIsFalse :
      observationMechanismPromoted ≡ false
    observationDiagnosisPromoted : Bool
    observationDiagnosisPromotedIsFalse :
      observationDiagnosisPromoted ≡ false
    observationHiddenChartRecovered : Bool
    observationHiddenChartRecoveredIsFalse :
      observationHiddenChartRecovered ≡ false
    observationReading : String

open PopulationTrajectoryObservation public

canonicalPopulationTrajectoryObservation : PopulationTrajectoryObservation
canonicalPopulationTrajectoryObservation =
  mkPopulationTrajectoryObservation
    canonicalAxisIndexedHypervoxel
    (suc zero)
    (suc (suc zero))
    populationTrajectoryCandidate
    refl
    tt
    preserveAxes
    false
    refl
    false
    refl
    false
    refl
    "Population-over-time BOLD/connectome data constrain an axis-indexed trajectory atlas; they do not recover a hidden chart or promote mechanism or diagnosis."

------------------------------------------------------------------------
-- +1 transition semantics.

record ConsentGovernedPlusOneTransition : Set where
  constructor mkConsentGovernedPlusOneTransition
  field
    transitionSource : AxisIndexedHypervoxel
    transitionTarget : AxisIndexedHypervoxel
    transitionAxesPreserved :
      AxisPreservingProjection
        (voxelAxes transitionSource)
        (voxelAxes transitionTarget)
    transitionConsentGovernance :
      Consent.InterventionConsentLongitudinalGovernance
    transitionConsentGovernanceIsCanonical :
      transitionConsentGovernance ≡
      Consent.canonicalInterventionConsentLongitudinalGovernance
    transitionChangesAdmissibleStructure : Bool
    transitionChangesAdmissibleStructureIsTrue :
      transitionChangesAdmissibleStructure ≡ true
    transitionCuresResidual : Bool
    transitionCuresResidualIsFalse :
      transitionCuresResidual ≡ false
    transitionForcesDisclosure : Bool
    transitionForcesDisclosureIsFalse :
      transitionForcesDisclosure ≡ false
    transitionClinicalAuthority : Bool
    transitionClinicalAuthorityIsFalse :
      transitionClinicalAuthority ≡ false
    transitionReading : String

open ConsentGovernedPlusOneTransition public

canonicalConsentGovernedPlusOneTransition : ConsentGovernedPlusOneTransition
canonicalConsentGovernedPlusOneTransition =
  mkConsentGovernedPlusOneTransition
    canonicalAxisIndexedHypervoxel
    (mkAxisIndexedHypervoxel
      "re-chartable body-memory carrier"
      (suc zero)
      "situated place"
      "situated relation"
      "situated institution"
      Residual.canonicalIntersectionalAxes
      refl
      false
      refl)
    preserveAxes
    Consent.canonicalInterventionConsentLongitudinalGovernance
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    "+1 changes the admissible transition structure under consent, pacing, stop, and non-forcing gates; it is not cure, disclosure, diagnosis, or authority."

------------------------------------------------------------------------
-- Aggregate bridge.

record IntersectionalLongitudinalProxyTransitionBridge : Set where
  constructor mkIntersectionalLongitudinalProxyTransitionBridge
  field
    residualDynamics :
      Residual.IntersectionalLongitudinalResidualDynamics
    residualDynamicsIsCanonical :
      residualDynamics ≡
      Residual.canonicalIntersectionalLongitudinalResidualDynamics
    imagingGovernance :
      Imaging.LongitudinalFMRIConnectomeDynamicsGovernance
    imagingGovernanceIsCanonical :
      imagingGovernance ≡
      Imaging.canonicalLongitudinalFMRIConnectomeDynamicsGovernance
    populationTrajectoryObservation :
      PopulationTrajectoryObservation
    plusOneTransition :
      ConsentGovernedPlusOneTransition
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    causalClosurePromoted : Bool
    causalClosurePromotedIsFalse : causalClosurePromoted ≡ false
    individualDiagnosisPromoted : Bool
    individualDiagnosisPromotedIsFalse : individualDiagnosisPromoted ≡ false
    bridgeReading : String

open IntersectionalLongitudinalProxyTransitionBridge public

canonicalIntersectionalLongitudinalProxyTransitionBridge :
  IntersectionalLongitudinalProxyTransitionBridge
canonicalIntersectionalLongitudinalProxyTransitionBridge =
  mkIntersectionalLongitudinalProxyTransitionBridge
    Residual.canonicalIntersectionalLongitudinalResidualDynamics
    refl
    Imaging.canonicalLongitudinalFMRIConnectomeDynamicsGovernance
    refl
    canonicalPopulationTrajectoryObservation
    canonicalConsentGovernedPlusOneTransition
    true
    refl
    false
    refl
    false
    refl
    "Axis-indexed longitudinal residuals, population proxy trajectories, and consent-governed +1 transitions are composed without axis erasure, causal closure, diagnosis, treatment, mind-reading, or hidden-chart recovery."

canonicalObservationAxesArePreserved :
  AxisPreservingProjection
    (voxelAxes
      (observationHypervoxel canonicalPopulationTrajectoryObservation))
    Residual.canonicalIntersectionalAxes
canonicalObservationAxesArePreserved =
  observationAxesPreserved canonicalPopulationTrajectoryObservation

canonicalPopulationTrajectoryDoesNotPromoteMechanism :
  observationMechanismPromoted canonicalPopulationTrajectoryObservation ≡ false
canonicalPopulationTrajectoryDoesNotPromoteMechanism =
  observationMechanismPromotedIsFalse canonicalPopulationTrajectoryObservation

canonicalPlusOneChangesTransitionsNotTruth :
  transitionChangesAdmissibleStructure canonicalConsentGovernedPlusOneTransition ≡ true
canonicalPlusOneChangesTransitionsNotTruth =
  transitionChangesAdmissibleStructureIsTrue canonicalConsentGovernedPlusOneTransition

canonicalPlusOneDoesNotCure :
  transitionCuresResidual canonicalConsentGovernedPlusOneTransition ≡ false
canonicalPlusOneDoesNotCure =
  transitionCuresResidualIsFalse canonicalConsentGovernedPlusOneTransition

canonicalBridgeCausalClosureBlocked :
  causalClosurePromoted canonicalIntersectionalLongitudinalProxyTransitionBridge ≡ false
canonicalBridgeCausalClosureBlocked =
  causalClosurePromotedIsFalse canonicalIntersectionalLongitudinalProxyTransitionBridge
