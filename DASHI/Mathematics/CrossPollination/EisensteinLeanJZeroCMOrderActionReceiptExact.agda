module DASHI.Mathematics.CrossPollination.EisensteinLeanJZeroCMOrderActionReceiptExact where

------------------------------------------------------------------------
-- LEAN j=0 / EISENSTEIN-ORDER CM ACTION: CROSS-PROVER RECEIPT
--
-- This is a repository-internal formal-source receipt.  It does not import a
-- Lean proof object into Agda, and it does not promote a software-library or
-- mathematical reference into DASHI authorship.
--
-- The observed Lean branch extends the original norm-shell programme along the
-- SAME arithmetic lineage:
--
--   Z^2 coordinates
--     -> QuadraticAlgebra Int (-1) (-1) = Z[omega]
--     -> FractionRing Z[omega]
--     -> y^2 = x^3 + 1 with native Mathlib j = 0
--     -> Phi(x,y) = (omega*x,y) on Mathlib's actual affine point group
--     -> Phi^2 + Phi + 1 = 0
--     -> ring action Z[omega] -> End(E(K)).
--
-- Mathlib owns the imported affine Weierstrass point-group implementation and
-- generic QuadraticAlgebra lift.  DASHI/Lean owns the specialization and
-- composition on PR #69.  Faithfulness/geometric CM embedding, endomorphism
-- degree = norm, Hecke character, Euler-factor agreement and elliptic L-series
-- agreement remain explicitly unpaid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Interop.Round11MachinCrossProverRecognitionExact as Attribution

record LeanJZeroCMFormalSourceReceipt : Set where
  constructor lean-jzero-cm-formal-source-receipt
  field
    repository : String
    pullRequest : String
    branch : String
    commit : String
    endomorphismOwner : String
    endomorphismTheorem : String
    quadraticRelationTheorem : String
    concreteOwner : String
    nativeJTheorem : String
    concreteEndomorphism : String
    orderActionOwner : String
    orderActionDefinition : String
    coordinateActionTheorem : String
    importedMathlibPointGroupOwner : String
    importedMathlibQuadraticLiftOwner : String
    verificationStatus : String
    origin : Attribution.ClaimOrigin

open LeanJZeroCMFormalSourceReceipt public

leanJZeroCMReceipt : LeanJZeroCMFormalSourceReceipt
leanJZeroCMReceipt =
  lean-jzero-cm-formal-source-receipt
    "chboishabba/dashi_lean4"
    "PR #69"
    "agent/eisenstein-lattice-counting-maxcut-20261012"
    "c9c0b2718c08aa9294e6b8872c2e0e8a0a3bbc0f"
    "Integration/EisensteinJZeroCMEndomorphismExact.lean"
    "jZeroRotationEndomorphism"
    "jZeroRotationEndomorphism_quadraticRelation"
    "Integration/EisensteinJZeroCMConcreteExact.lean"
    "eisensteinJZeroCurve_j_eq_zero"
    "eisensteinCMEndomorphism"
    "Integration/EisensteinCMOrderActionExact.lean"
    "eisensteinOrderAction"
    "eisensteinOrderAction_coordinates"
    "Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean"
    "Mathlib/Algebra/QuadraticAlgebra/Basic.lean"
    "SOURCE-WRITTEN / PINNED-MATHLIB-4.28-API-AUDITED / KERNEL-PENDING"
    Attribution.leanFormalReconstruction

leanCMClaimOrigin : Attribution.ClaimOrigin
leanCMClaimOrigin = origin leanJZeroCMReceipt

------------------------------------------------------------------------
-- Claim-relative payment status.
------------------------------------------------------------------------

leanNativePointGroupEndomorphismSourceObserved : Bool
leanNativePointGroupEndomorphismSourceObserved = true

leanNativeJZeroSourceObserved : Bool
leanNativeJZeroSourceObserved = true

leanEisensteinQuadraticRelationSourceObserved : Bool
leanEisensteinQuadraticRelationSourceObserved = true

leanEisensteinOrderActionSourceObserved : Bool
leanEisensteinOrderActionSourceObserved = true

leanFaithfulGeometricCMEmbeddingObserved : Bool
leanFaithfulGeometricCMEmbeddingObserved = false

leanEndomorphismDegreeEqualsNormObserved : Bool
leanEndomorphismDegreeEqualsNormObserved = false

leanHeckeCharacterObserved : Bool
leanHeckeCharacterObserved = false

leanLocalEulerFactorAgreementObserved : Bool
leanLocalEulerFactorAgreementObserved = false

leanEllipticLSeriesAgreementObserved : Bool
leanEllipticLSeriesAgreementObserved = false

leanProofObjectImportedIntoAgda : Bool
leanProofObjectImportedIntoAgda = false

agdaCMEndomorphismTheoremInhabitedFromReceipt : Bool
agdaCMEndomorphismTheoremInhabitedFromReceipt = false

agdaEisensteinOrderActionInhabitedFromReceipt : Bool
agdaEisensteinOrderActionInhabitedFromReceipt = false

externalScientificSourceAcquiredByThisReceipt : Bool
externalScientificSourceAcquiredByThisReceipt = false

------------------------------------------------------------------------
-- Attribution firewall.
------------------------------------------------------------------------

record LeanJZeroCMAttributionBoundary : Set where
  constructor lean-jzero-cm-attribution-boundary
  field
    leanFormalReconstructionRecorded : Bool
    mathlibLibraryRoleRecorded : Bool
    agdaKernelAuthorityImported : Bool
    faithfulCMEmbeddingManufactured : Bool
    heckeAuthorityManufactured : Bool
    ellipticLAuthorityManufactured : Bool
    externalScientificAuthorityManufactured : Bool

canonicalLeanJZeroCMAttributionBoundary : LeanJZeroCMAttributionBoundary
canonicalLeanJZeroCMAttributionBoundary =
  lean-jzero-cm-attribution-boundary
    true
    true
    false
    false
    false
    false
    false
