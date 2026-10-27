module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoWannier3DResponseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- CONDITIONAL 3D MATERIAL RESPONSE CONSUMER
--
-- Runtime companion:
--   scripts/co_tase2_wannier3d_diagnostics.py
--
-- This owner records what the repository can compute once a literal same-object
-- SOC+exchange Wannier Hamiltonian and same-basis spin operators are supplied.
-- It does not promote the current source-compatible/toy Hamiltonians into the
-- material Hamiltonian and does not turn computed Berry/Weyl output into a
-- source observation.
------------------------------------------------------------------------

record Wannier3DResponseContract : Set where
  constructor wannier-3d-response-contract
  field
    literalMaterialWannierRequired : Bool
    sameBasisSpinOperatorsRequired : Bool
    full3DKGridImplemented : Bool
    analyticWannierDerivativeImplemented : Bool
    bandSpinExpectationImplemented : Bool
    berryCurvatureImplemented : Bool
    adjacentGapCandidateSearchImplemented : Bool
    berryFluxChiralityImplemented : Bool
    socContinuationRequiresSameGaugeBasis : Bool
    computedTopologyIsSourceObservation : Bool
    computedTopologyValidatesInputHamiltonian : Bool

open Wannier3DResponseContract public

canonicalWannier3DResponseContract : Wannier3DResponseContract
canonicalWannier3DResponseContract =
  wannier-3d-response-contract
    true true
    true true true true true true true
    false false

record Wannier3DResponseStatus : Set where
  constructor wannier-3d-response-status
  field
    conditionalConsumerImplemented : Bool
    analyticWeylRegressionPassedLocally : Bool
    literalCoMaterialArtifactPresent : Bool
    literalCoSpinOperatorArtifactPresent : Bool
    co3DSpinTextureExecuted : Bool
    coBerryTopologyExecuted : Bool
    coSOCContinuationExecuted : Bool

canonicalWannier3DResponseStatus : Wannier3DResponseStatus
canonicalWannier3DResponseStatus =
  wannier-3d-response-status
    true true
    false false false false false

record TopologyPromotionBoundary : Set where
  constructor topology-promotion-boundary
  field
    sahFamilyWeylClaimAutomaticallyTransfersToCoTa4Se8 : Bool
    smallDirectGapAutomaticallyImpliesWeylPoint : Bool
    nonzeroLocalBerryCurvatureAutomaticallyImpliesQuantizedChirality : Bool
    closedSurfaceFluxReceiptRequiredForWeylChirality : Bool
    sameObjectMaterialHamiltonianRequiredForCoClaim : Bool

canonicalTopologyPromotionBoundary : TopologyPromotionBoundary
canonicalTopologyPromotionBoundary =
  topology-promotion-boundary false false false true true
