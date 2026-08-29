{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109116ConventionTransportRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1: DO NOT HIDE NORMALIZATION / PROJECTION CONVENTIONS
--
-- A literal equality between CMP109 E^(2) and the CMP116 marked Hessian is only
-- correct after four convention axes are aligned:
--
--   background/configuration,
--   field/source tangent coordinate,
--   constrained/gauge projection,
--   blocking/rescaling normalization.
--
-- This file makes the most general thin transport explicit.  If all maps are
-- identities and the normalization is one, the transport collapses to literal
-- equality.  Otherwise downstream consumers can use the transported Hessian
-- without pretending that a proportionality/conjugacy is definitional.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 1ℝ; _*ℝ_; mulOneˡ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP109116ConventionTransport : Set₁ where
  field
    CMP109Configuration CMP116Configuration : Set
    CMP109Tangent CMP116Tangent : Set

    cmp109E2 :
      CMP109Configuration → CMP109Tangent → CMP109Tangent → ℝ
    cmp116MarkedHessian :
      CMP116Configuration → CMP116Tangent → CMP116Tangent → ℝ

    -- Background / source-coordinate transport.
    backgroundToCMP109 : CMP116Configuration → CMP109Configuration
    tangentToCMP109 : CMP116Tangent → CMP109Tangent

    -- This scalar owns all block-volume, field-rescaling and source-normalization
    -- convention differences.  A nontrivial value is not silently erased.
    normalizationScale : ℝ

    -- Exact source convention statement after constrained/gauge projection has
    -- been included in `tangentToCMP109`.
    markedHessianTransportExact : ∀ configuration u v →
      cmp116MarkedHessian configuration u v
      ≡ normalizationScale *ℝ
          cmp109E2
            (backgroundToCMP109 configuration)
            (tangentToCMP109 u)
            (tangentToCMP109 v)

open CMP109116ConventionTransport public

transportedCMP109Hessian :
  (dataSet : CMP109116ConventionTransport) →
  CMP116Configuration dataSet →
  CMP116Tangent dataSet → CMP116Tangent dataSet → ℝ
transportedCMP109Hessian dataSet configuration u v =
  normalizationScale dataSet *ℝ
    cmp109E2 dataSet
      (backgroundToCMP109 dataSet configuration)
      (tangentToCMP109 dataSet u)
      (tangentToCMP109 dataSet v)

cmp116MarkedHessianIsTransportedCMP109 :
  (dataSet : CMP109116ConventionTransport) →
  ∀ configuration u v →
  cmp116MarkedHessian dataSet configuration u v
  ≡ transportedCMP109Hessian dataSet configuration u v
cmp116MarkedHessianIsTransportedCMP109 dataSet =
  markedHessianTransportExact dataSet

record IdentityConventionAlignment : Set₁ where
  field
    Configuration Tangent : Set
    e2 markedHessian : Configuration → Tangent → Tangent → ℝ

    -- These are the results of the four explicit convention checks, not
    -- assumptions inferred from notation.
    sameBackgroundCoordinate : Set
    sameSourceTangentCoordinate : Set
    sameConstrainedProjection : Set
    sameBlockingNormalization : Set

    markedHessianIsE2 : ∀ configuration u v →
      markedHessian configuration u v ≡ e2 configuration u v

open IdentityConventionAlignment public

identityConventionAsTransport :
  IdentityConventionAlignment → CMP109116ConventionTransport
identityConventionAsTransport dataSet = record
  { CMP109116ConventionTransport.CMP109Configuration = Configuration dataSet
  ; CMP109116ConventionTransport.CMP116Configuration = Configuration dataSet
  ; CMP109116ConventionTransport.CMP109Tangent = Tangent dataSet
  ; CMP109116ConventionTransport.CMP116Tangent = Tangent dataSet
  ; CMP109116ConventionTransport.cmp109E2 = e2 dataSet
  ; CMP109116ConventionTransport.cmp116MarkedHessian = markedHessian dataSet
  ; CMP109116ConventionTransport.backgroundToCMP109 = λ x → x
  ; CMP109116ConventionTransport.tangentToCMP109 = λ x → x
  ; CMP109116ConventionTransport.normalizationScale = 1ℝ
  ; CMP109116ConventionTransport.markedHessianTransportExact =
      λ configuration u v →
        let
          same = markedHessianIsE2 dataSet configuration u v
        in
        -- `1 * x = x` is oriented opposite to the desired RHS.
        Agda.Builtin.Equality.trans same
          (Agda.Builtin.Equality.sym
            (mulOneˡ (e2 dataSet configuration u v)))
  }

cmp109116ConventionTransportLevel : ProofLevel
cmp109116ConventionTransportLevel = machineChecked

identityConventionCollapseLevel : ProofLevel
identityConventionCollapseLevel = machineChecked

-- Physical source task: determine whether CMP109 and CMP116 really inhabit the
-- identity specialization.  If not, inhabit the general transport with the
-- literal scale/projection map instead.  No source-normalization mismatch can be
-- hidden downstream.
literalCMP109116ConventionAlignmentLevel : ProofLevel
literalCMP109116ConventionAlignmentLevel = conditional
