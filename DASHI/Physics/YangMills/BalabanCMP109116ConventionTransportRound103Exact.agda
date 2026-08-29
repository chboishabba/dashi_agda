{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109116ConventionTransportRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1: EXPLICIT NORMALIZATION / PROJECTION TRANSPORT
--
-- The general carrier permits genuinely different configuration/tangent
-- coordinates plus a scalar normalization.  The identity specialization has
-- literally the same types/maps and normalization one; therefore no decorative
-- `Set` fields are needed to assert what the executable data already enforce.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 1ℝ; _*ℝ_; *-comm; mulOneʳ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP109116ConventionTransport : Set₁ where
  field
    CMP109Configuration CMP116Configuration : Set
    CMP109Tangent CMP116Tangent : Set

    cmp109E2 :
      CMP109Configuration → CMP109Tangent → CMP109Tangent → ℝ
    cmp116MarkedHessian :
      CMP116Configuration → CMP116Tangent → CMP116Tangent → ℝ

    backgroundToCMP109 : CMP116Configuration → CMP109Configuration
    tangentToCMP109 : CMP116Tangent → CMP109Tangent
    normalizationScale : ℝ

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

oneTimes : ∀ x → 1ℝ *ℝ x ≡ x
oneTimes x = trans (*-comm 1ℝ x) (mulOneʳ x)

record IdentityConventionAlignment : Set₁ where
  field
    Configuration Tangent : Set
    e2 markedHessian : Configuration → Tangent → Tangent → ℝ
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
        trans
          (markedHessianIsE2 dataSet configuration u v)
          (sym (oneTimes (e2 dataSet configuration u v)))
  }

cmp109116ConventionTransportLevel : ProofLevel
cmp109116ConventionTransportLevel = machineChecked

identityConventionCollapseLevel : ProofLevel
identityConventionCollapseLevel = machineChecked

literalCMP109116ConventionAlignmentLevel : ProofLevel
literalCMP109116ConventionAlignmentLevel = conditional
