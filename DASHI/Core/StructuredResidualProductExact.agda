module DASHI.Core.StructuredResidualProductExact where

------------------------------------------------------------------------
-- STRUCTURED RESIDUALS BEFORE GLOBAL SCALARISATION
--
-- Cross-project lesson: curvature/fabric defects, semantic ambiguity/source
-- conflict, and environmental conservation/calibration residuals are different
-- coordinates.  A global sum can preserve total magnitude while erasing which
-- coordinate carries the burden.  Consumer-local safety therefore needs the
-- structured carrier (or a proved descent theorem), not merely a scalar total.
--
-- This module contains both the exact two-coordinate non-descent kernel and a
-- typed four-axis cold-residual carrier for the recurrent cross-project split:
-- raw evidence, geometry/lineage, model/fidelity, and policy/authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel

------------------------------------------------------------------------
-- Minimal exact non-descent theorem for scalarisation.
------------------------------------------------------------------------

Residual2 : Set
Residual2 = Nat × Nat

scalarTotal : Residual2 → Nat
scalarTotal residual = proj₁ residual + proj₂ residual

firstCoordinate : Residual2 → Nat
firstCoordinate = proj₁

secondCoordinate : Residual2 → Nat
secondCoordinate = proj₂

one : Nat
one = suc zero

scalarTotalLosesFirstCoordinate :
  Kernel.ConsumerDescentDefect scalarTotal firstCoordinate
scalarTotalLosesFirstCoordinate =
  Kernel.consumerDescentDefect
    (one , zero)
    (zero , one)
    refl
    impossible
  where
    impossible : one ≡ zero → ⊥
    impossible ()

scalarTotalLosesSecondCoordinate :
  Kernel.ConsumerDescentDefect scalarTotal secondCoordinate
scalarTotalLosesSecondCoordinate =
  Kernel.consumerDescentDefect
    (one , zero)
    (zero , one)
    refl
    impossible
  where
    impossible : zero ≡ one → ⊥
    impossible ()

------------------------------------------------------------------------
-- Typed four-axis cold residual.
--
-- These coordinates intentionally have unrelated types.  No addition or norm
-- is available unless a domain/consumer supplies one.  This prevents a policy
-- authority defect from being silently added to a geometric or empirical
-- residual merely because a runtime wants one dashboard number.
------------------------------------------------------------------------

record StructuredResidual4
    (RawEvidence GeometryLineage ModelFidelity PolicyAuthority : Set) : Set where
  constructor structuredResidual4
  field
    rawEvidence : RawEvidence
    geometryLineage : GeometryLineage
    modelFidelity : ModelFidelity
    policyAuthority : PolicyAuthority

open StructuredResidual4 public

rebuildStructuredResidual4 :
  ∀ {RawEvidence GeometryLineage ModelFidelity PolicyAuthority} →
  (residual : StructuredResidual4
    RawEvidence GeometryLineage ModelFidelity PolicyAuthority) →
  structuredResidual4
    (rawEvidence residual)
    (geometryLineage residual)
    (modelFidelity residual)
    (policyAuthority residual)
  ≡ residual
rebuildStructuredResidual4 (structuredResidual4 raw geometry model policy) = refl

------------------------------------------------------------------------
-- Reopening is coordinate-specific.  A changed model calibration need not be
-- misreported as changed raw evidence; policy invalidation need not pretend the
-- geometry changed.  Dependency closure may of course make several coordinates
-- live at once, but that is a theorem/dataflow fact rather than scalarization.
------------------------------------------------------------------------

data ResidualAxis : Set where
  rawEvidenceAxis : ResidualAxis
  geometryLineageAxis : ResidualAxis
  modelFidelityAxis : ResidualAxis
  policyAuthorityAxis : ResidualAxis

record CoordinateReopening (axis : ResidualAxis) : Set where
  constructor coordinateReopening
  field
    affected : Bool

open CoordinateReopening public

record StructuredReopeningPlan : Set where
  constructor structuredReopeningPlan
  field
    rawEvidenceReopening : CoordinateReopening rawEvidenceAxis
    geometryLineageReopening : CoordinateReopening geometryLineageAxis
    modelFidelityReopening : CoordinateReopening modelFidelityAxis
    policyAuthorityReopening : CoordinateReopening policyAuthorityAxis

open StructuredReopeningPlan public

onlyModelFidelityAffected : StructuredReopeningPlan
onlyModelFidelityAffected =
  structuredReopeningPlan
    (coordinateReopening false)
    (coordinateReopening false)
    (coordinateReopening true)
    (coordinateReopening false)

modelOnlyDoesNotMarkRawEvidenceAffected :
  affected (rawEvidenceReopening onlyModelFidelityAffected) ≡ false
modelOnlyDoesNotMarkRawEvidenceAffected = refl
  where
    open import Agda.Builtin.Bool using (false)

record StructuredResidualBoundary : Set where
  constructor structuredResidualBoundary
  field
    equalGlobalTotalNeedNotMeanEqualLocalResidual : Bool
    coordinateConsumersNeedStructuredCarrierOrDescentProof : Bool
    residualCoordinatesNeedNotShareScientificUnits : Bool
    globalScalarisationIsAConsumerRelativeClaim : Bool
    typedColdResidualHasExactReconstruction : Bool
    reopeningCanRemainCoordinateSpecific : Bool

canonicalStructuredResidualBoundary : StructuredResidualBoundary
canonicalStructuredResidualBoundary =
  structuredResidualBoundary true true true true true true
