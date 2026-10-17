{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109CanonicalResidualInstantiationExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (_-ℝ_)

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
-- Balaban lane.  The blocker taxonomy, package contraction, same-object
-- attachment relations, and the abstract D1 transport record below are a
-- DASHI EXTENSION.  They are not attributed back to Bałaban and do not
-- manufacture a source theorem inhabitant.
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
-- histories with that exact source carrier.
betaDifferenceBlocker : CMP109BlockerKind
betaDifferenceBlocker = sameObjectAttachmentMissing

-- Round152 exposed the historical formulation, but no non-Round selected
-- first-order transport equality was found.  The live debt is therefore the
-- same-object chain-rule transport, not a second generic derivative calculus.
physicalCompositeD1Blocker : CMP109BlockerKind
physicalCompositeD1Blocker = transportEqualityMissing

------------------------------------------------------------------------
-- 1. Generated-history response: sharpen to the existing non-Round producer.
--
-- The residual is not merely a producer floating in space: it must be attached
-- to the SAME selected literal source object consumed by the other CMP109
-- payments.
------------------------------------------------------------------------

record CMP109GeneratedHistoryResponseResidual
    {SelectedSource : Set}
    (selectedSource : SelectedSource)
    (cutoff : Nat) : Set₁ where
  field
    literalGeneratedHistoryResponseProducer :
      Producer.WardQuarticResponseProducer cutoff

    ProducerBelongsToSelectedSource :
      SelectedSource → Producer.WardQuarticResponseProducer cutoff → Set

    producerBelongsToSelectedSource :
      ProducerBelongsToSelectedSource
        selectedSource literalGeneratedHistoryResponseProducer

------------------------------------------------------------------------
-- 2. Beta difference: structural decomposition is already paid.
------------------------------------------------------------------------

record SelectedCMP109BetaDifferenceAttachment
    {SelectedSource : Set}
    (selectedSource : SelectedSource)
    (TubePoint : Set) : Set₁ where
  field
    selectedShootingMap : Prefix.BetaPrefixShootingMap TubePoint
    selectedLeftHistory : TubePoint
    selectedRightHistory : TubePoint

    ShootingMapBelongsToSelectedSource :
      SelectedSource → Prefix.BetaPrefixShootingMap TubePoint → Set

    shootingMapBelongsToSelectedSource :
      ShootingMapBelongsToSelectedSource selectedSource selectedShootingMap

------------------------------------------------------------------------

open SelectedCMP109BetaDifferenceAttachment public

selectedBetaDifferenceDecomposition :
  ∀ {SelectedSource TubePoint}
    {selectedSource : SelectedSource}
    (attachment :
      SelectedCMP109BetaDifferenceAttachment selectedSource TubePoint) →
  Prefix.initialInverseSquare (selectedShootingMap attachment)
      (Prefix.renormalisationMap (selectedShootingMap attachment)
        (selectedLeftHistory attachment))
    -ℝ
  Prefix.initialInverseSquare (selectedShootingMap attachment)
      (Prefix.renormalisationMap (selectedShootingMap attachment)
        (selectedRightHistory attachment))
  ≡
  Prefix.cumulativeBeta (selectedShootingMap attachment)
      (selectedLeftHistory attachment)
    -ℝ
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
-- the canonical consumer.  Both D1 functions must be attached to the same
-- selected source object before the transport equality counts as a payment.
------------------------------------------------------------------------

record PhysicalCompositeD1TransportResidual
    {SelectedSource : Set}
    (selectedSource : SelectedSource)
    (Component Background Tangent Scalar : Set) : Set₁ where
  field
    physicalCompositeD1 : Component → Background → Tangent → Scalar
    substitutedD1 : Component → Background → Tangent → Scalar

    D1BelongsToSelectedSource :
      SelectedSource →
      (Component → Background → Tangent → Scalar) → Set

    physicalCompositeD1BelongsToSelectedSource :
      D1BelongsToSelectedSource selectedSource physicalCompositeD1

    substitutedD1BelongsToSelectedSource :
      D1BelongsToSelectedSource selectedSource substitutedD1

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
    {SelectedSource : Set}
    (selectedSource : SelectedSource)
    (TubePoint : Set)
    (cutoff : Nat)
    (Component Background Tangent Scalar : Set) : Set₁ where
  field
    generatedHistoryResponse :
      CMP109GeneratedHistoryResponseResidual selectedSource cutoff

    betaDifferenceAttachment :
      SelectedCMP109BetaDifferenceAttachment selectedSource TubePoint

    physicalCompositeD1Transport :
      PhysicalCompositeD1TransportResidual
        selectedSource Component Background Tangent Scalar

------------------------------------------------------------------------

open CMP109CanonicalResidualInstantiation public

-- Package contraction is not Clay promotion.
clayPromotion : Bool
clayPromotion = false
