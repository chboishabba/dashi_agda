module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoNonAbelianTopologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- DEGENERACY-SAFE CONDITIONAL TOPOLOGY CONSUMER
--
-- Runtime companion:
--   scripts/co_tase2_nonabelian_topology.py
--
-- This owner records the repository-side capability to compute gauge-invariant
-- projector curvature and Wilson-loop spectra for an isolated band subspace of
-- a future literal same-object Co1/4TaSe2 Wannier Hamiltonian.  Degeneracies
-- inside the selected subspace are allowed; closure of the gap to its
-- complement is an explicit fail-closed boundary.
------------------------------------------------------------------------

record NonAbelianTopologyContract : Set where
  constructor non-abelian-topology-contract
  field
    literalSameObjectWannierRequired : Bool
    selectedSubspaceMustBeIsolatedFromComplement : Bool
    internalSelectedBandDegeneracyAllowed : Bool
    spectralProjectorDerivativeImplemented : Bool
    projectorTraceCurvatureImplemented : Bool
    wilsonLoopPolarTransportImplemented : Bool
    wilsonLoopSpectrumGaugeInvariantTarget : Bool
    metallicHallConductivityImplementedHere : Bool
    extrinsicDisorderTransportImplementedHere : Bool

open NonAbelianTopologyContract public

canonicalNonAbelianTopologyContract : NonAbelianTopologyContract
canonicalNonAbelianTopologyContract =
  non-abelian-topology-contract
    true true true
    true true true true
    false false

record AttributionBoundary : Set where
  constructor attribution-boundary
  field
    externalMaterialHamiltonianIsSourceObservation : Bool
    projectorCurvatureIsRepositoryComputedResult : Bool
    wilsonLoopSpectrumIsRepositoryComputedResult : Bool
    formalConsumerContractIsFormalResult : Bool
    familyLevelWeylClaimAutomaticallyTransfersToCoTa4Se8 : Bool
    computedTopologyAutomaticallyValidatesMaterialHamiltonian : Bool
    materialInterpretationRequiresSameObjectValidation : Bool

canonicalAttributionBoundary : AttributionBoundary
canonicalAttributionBoundary =
  attribution-boundary
    false true true true
    false false true

record NonAbelianTopologyStatus : Set where
  constructor non-abelian-topology-status
  field
    conditionalConsumerImplemented : Bool
    analyticRankOneWeylRegressionSpecified : Bool
    exactDegenerateRankTwoGaugeRegressionSpecified : Bool
    wilsonLoopGaugeRegressionSpecified : Bool
    literalCoMaterialSubspacePresent : Bool
    coProjectorTopologyExecuted : Bool
    coWilsonLoopExecuted : Bool
    coDegeneracySafeTransportExecuted : Bool

canonicalNonAbelianTopologyStatus : NonAbelianTopologyStatus
canonicalNonAbelianTopologyStatus =
  non-abelian-topology-status
    true true true true
    false false false false

record TransportPromotionBoundary : Set where
  constructor transport-promotion-boundary
  field
    localBerryCurvatureImpliesMetallicAHE : Bool
    isolatedSubspaceChernDataImpliesMetallicAHE : Bool
    intrinsicResponseImpliesFullMeasuredHallResponse : Bool
    disorderExtrinsicTermsMayRequireSeparateProducer : Bool
    fermiOccupationAndScatteringPrescriptionRequired : Bool

canonicalTransportPromotionBoundary : TransportPromotionBoundary
canonicalTransportPromotionBoundary =
  transport-promotion-boundary false false false true true
