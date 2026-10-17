{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109CanonicalResidualInstantiationExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanBetaPrefixSensitivityToTubeContractionExact as Prefix
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as Producer

------------------------------------------------------------------------
-- CMP109 residual instantiation / canonical blocker classification.
--
-- PRIMARY SOURCE BOUNDARY
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The generated-history/raw-state context is calibrated against:
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- and
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- SOURCE CLAIM VERSUS DASHI EXTENSION
--
-- These papers own the source objects and estimates cited by the surrounding
-- Balaban lane.  The blocker taxonomy, package contraction, and the abstract
-- D1 transport record below are a DASHI EXTENSION.  They are not attributed
-- back to Bałaban and do not manufacture a source theorem inhabitant.
------------------------------------------------------------------------

data CMP109BlockerKind : Set where
  wrongCarrier : CMP109BlockerKind
  sameObjectAttachmentMissing : CMP109BlockerKind
  quantitativeEstimateMissing : CMP109BlockerKind
  sourceReconstructionMissing : CMP109BlockerKind
  transportEqualityMissing : CMP109BlockerKind
  genuinelyNewMathematics : CMP109BlockerKind

generatedHistoryResponseBlocker : CMP109BlockerKind
generatedHistoryResponseBlocker = sourceReconstructionMissing

-- The algebraic beta-difference identity already exists non-Round.  The live
-- debt is identifying the selected literal CMP109 shooting map and generated
-- histories with that exact carrier.
betaDifferenceBlocker : CMP109BlockerKind
betaDifferenceBlocker = sameObjectAttachmentMissing

-- Round152 exposed the historical formulation, but no non-Round selected
-- first-order transport equality was found.  The live debt is therefore the
-- same-object chain-rule transport, not a second generic derivative calculus.
physicalCompositeD1Blocker : CMP109BlockerKind
physicalCompositeD1Blocker = transportEqualityMissing

------------------------------------------------------------------------
-- 1. Generated-history response: sharpen to the existing non-Round producer.
------------------------------------------------------------------------

record CMP109GeneratedHistoryResponseResidual (cutoff : Nat) : Set₁ where
  field
    literalGeneratedHistoryResponseProducer :
      Producer.WardQuarticResponseProducer cutoff

------------------------------------------------------------------------
-- 2. Beta difference: structural decomposition is already paid.
------------------------------------------------------------------------

record SelectedCMP109BetaDifferenceAttachment (TubePoint : Set) : Set₁ where
  field
    selectedShootingMap : Prefix.BetaPrefixShootingMap TubePoint
    selectedLeftHistory : TubePoint
    selectedRightHistory : TubePoint

------------------------------------------------------------------------

open SelectedCMP109BetaDifferenceAttachment public

selectedBetaDifferenceDecomposition :
  ∀ {TubePoint}
    (attachment : SelectedCMP109BetaDifferenceAttachment TubePoint) →
  Prefix.initialInverseSquare (selectedShootingMap attachment)
      (Prefix.renormalisationMap (selectedShootingMap attachment)
        (selectedLeftHistory attachment))
    Prefix.-ℝ
  Prefix.initialInverseSquare (selectedShootingMap attachment)
      (Prefix.renormalisationMap (selectedShootingMap attachment)
        (selectedRightHistory attachment))
  ≡
  Prefix.cumulativeBeta (selectedShootingMap attachment)
      (selectedLeftHistory attachment)
    Prefix.-ℝ
  Prefix.cumulativeBeta (selectedShootingMap attachment)
      (selectedRightHistory attachment)
selectedBetaDifferenceDecomposition attachment =
  Prefix.sourceMapDifferenceIsBetaDifference
    (selectedShootingMap attachment)
    (selectedLeftHistory attachment)
    (selectedRightHistory attachment)

------------------------------------------------------------------------
-- 3. Physical composite D1: smallest non-Round transport equality.
--
-- DASHI extension: this record deliberately forgets the historical Round152
-- scheduler/carrier graph and keeps only the theorem content still needed by
-- the canonical consumer.  A future selected physical source must instantiate
-- this equality on its actual component/background/tangent carrier.
------------------------------------------------------------------------

record PhysicalCompositeD1TransportResidual
    (Component Background Tangent Scalar : Set) : Set₁ where
  field
    physicalCompositeD1 : Component → Background → Tangent → Scalar
    substitutedD1 : Component → Background → Tangent → Scalar
    physicalCompositeD1IsSubstitutedD1 :
      ∀ component background tangent →
      physicalCompositeD1 component background tangent
      ≡ substitutedD1 component background tangent

------------------------------------------------------------------------

open PhysicalCompositeD1TransportResidual public

------------------------------------------------------------------------
-- Canonical narrowed CMP109 package.
------------------------------------------------------------------------

record CMP109CanonicalResidualInstantiation
    (TubePoint : Set)
    (cutoff : Nat)
    (Component Background Tangent Scalar : Set) : Set₁ where
  field
    generatedHistoryResponse : CMP109GeneratedHistoryResponseResidual cutoff
    betaDifferenceAttachment : SelectedCMP109BetaDifferenceAttachment TubePoint
    physicalCompositeD1Transport :
      PhysicalCompositeD1TransportResidual
        Component Background Tangent Scalar

------------------------------------------------------------------------

open CMP109CanonicalResidualInstantiation public

-- Package contraction is not Clay promotion.
clayPromotion : Bool
clayPromotion = false
