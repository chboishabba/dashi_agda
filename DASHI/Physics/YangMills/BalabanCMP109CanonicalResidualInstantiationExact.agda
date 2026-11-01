{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109CanonicalResidualInstantiationExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

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
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- SOURCE CLAIM VERSUS DASHI EXTENSION
--
-- The blocker taxonomy, package contraction, same-object attachment interfaces,
-- and abstract D1 transport surface are DASHI EXTENSIONS.  This safe canonical
-- module intentionally imports no postulated real-analysis authority.  The
-- existing concrete beta-difference proof is connected only by the separate
-- non-safe `BalabanCMP109BetaDifferenceRealAnalysisBridgeExact` module.
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

betaDifferenceBlocker : CMP109BlockerKind
betaDifferenceBlocker = sameObjectAttachmentMissing

physicalCompositeD1Blocker : CMP109BlockerKind
physicalCompositeD1Blocker = transportEqualityMissing

------------------------------------------------------------------------
-- 1. Generated-history response.
--
-- The source-attachment relation is fixed OUTSIDE the residual record.  The
-- residual constructor supplies only a producer and evidence in that externally
-- fixed relation; it cannot define the relation itself.
------------------------------------------------------------------------

record CMP109GeneratedHistoryResponseResidual
    {SelectedSource : Set}
    (selectedSource : SelectedSource)
    (Producer : Set)
    (ProducerBelongsToSelectedSource : SelectedSource → Producer → Set) : Set₁ where
  field
    literalGeneratedHistoryResponseProducer : Producer
    producerAttachment :
      ProducerBelongsToSelectedSource
        selectedSource literalGeneratedHistoryResponseProducer

------------------------------------------------------------------------
-- 2. Beta difference.
--
-- This safe surface is parameterized over the shooting-map interface and over
-- the beta-difference algebra theorem.  The concrete theorem from the existing
-- real-analysis lane is applied only in the explicitly non-safe bridge module.
------------------------------------------------------------------------

record SelectedCMP109BetaDifferenceAttachment
    {SelectedSource : Set}
    (selectedSource : SelectedSource)
    (TubePoint ShootingMap Scalar : Set)
    (ShootingMapBelongsToSelectedSource : SelectedSource → ShootingMap → Set)
    (initialInverseSquare : ShootingMap → TubePoint → Scalar)
    (renormalisationMap : ShootingMap → TubePoint → TubePoint)
    (cumulativeBeta : ShootingMap → TubePoint → Scalar)
    (minus : Scalar → Scalar → Scalar)
    (betaDifferenceAlgebra :
      ∀ shootingMap left right →
      minus
        (initialInverseSquare shootingMap (renormalisationMap shootingMap left))
        (initialInverseSquare shootingMap (renormalisationMap shootingMap right))
      ≡
      minus
        (cumulativeBeta shootingMap left)
        (cumulativeBeta shootingMap right)) : Set₁ where
  field
    selectedShootingMap : ShootingMap
    selectedLeftHistory : TubePoint
    selectedRightHistory : TubePoint
    shootingMapAttachment :
      ShootingMapBelongsToSelectedSource selectedSource selectedShootingMap

------------------------------------------------------------------------

open SelectedCMP109BetaDifferenceAttachment public

selectedBetaDifferenceDecomposition :
  ∀ {SelectedSource TubePoint ShootingMap Scalar}
    (selectedSource : SelectedSource)
    (ShootingMapBelongsToSelectedSource : SelectedSource → ShootingMap → Set)
    (initialInverseSquare : ShootingMap → TubePoint → Scalar)
    (renormalisationMap : ShootingMap → TubePoint → TubePoint)
    (cumulativeBeta : ShootingMap → TubePoint → Scalar)
    (minus : Scalar → Scalar → Scalar)
    (betaDifferenceAlgebra :
      ∀ shootingMap left right →
      minus
        (initialInverseSquare shootingMap (renormalisationMap shootingMap left))
        (initialInverseSquare shootingMap (renormalisationMap shootingMap right))
      ≡
      minus
        (cumulativeBeta shootingMap left)
        (cumulativeBeta shootingMap right))
    (attachment :
      SelectedCMP109BetaDifferenceAttachment
        selectedSource TubePoint ShootingMap Scalar
        ShootingMapBelongsToSelectedSource
        initialInverseSquare renormalisationMap cumulativeBeta minus
        betaDifferenceAlgebra) →
  minus
    (initialInverseSquare (selectedShootingMap attachment)
      (renormalisationMap (selectedShootingMap attachment)
        (selectedLeftHistory attachment)))
    (initialInverseSquare (selectedShootingMap attachment)
      (renormalisationMap (selectedShootingMap attachment)
        (selectedRightHistory attachment)))
  ≡
  minus
    (cumulativeBeta (selectedShootingMap attachment)
      (selectedLeftHistory attachment))
    (cumulativeBeta (selectedShootingMap attachment)
      (selectedRightHistory attachment))
selectedBetaDifferenceDecomposition
    selectedSource ShootingMapBelongsToSelectedSource
    initialInverseSquare renormalisationMap cumulativeBeta minus
    betaDifferenceAlgebra attachment =
  betaDifferenceAlgebra
    (selectedShootingMap attachment)
    (selectedLeftHistory attachment)
    (selectedRightHistory attachment)

------------------------------------------------------------------------
-- 3. Physical composite D1.
--
-- Both reference functions, the source-attachment relation, and both attachment
-- proofs are external parameters fixed before the residual record is built.
-- The residual record can only carry the live transport equality; it cannot
-- choose `substitutedD1 = physicalCompositeD1` during construction.
------------------------------------------------------------------------

record PhysicalCompositeD1TransportResidual
    {SelectedSource : Set}
    (selectedSource : SelectedSource)
    (Component Background Tangent Scalar : Set)
    (physicalCompositeD1 substitutedD1 :
      Component → Background → Tangent → Scalar)
    (D1BelongsToSelectedSource :
      SelectedSource → (Component → Background → Tangent → Scalar) → Set)
    (physicalCompositeD1Attachment :
      D1BelongsToSelectedSource selectedSource physicalCompositeD1)
    (substitutedD1Attachment :
      D1BelongsToSelectedSource selectedSource substitutedD1) : Set₁ where
  field
    physicalCompositeD1IsSubstitutedD1 :
      ∀ component background tangent →
      physicalCompositeD1 component background tangent
      ≡ substitutedD1 component background tangent

------------------------------------------------------------------------

open PhysicalCompositeD1TransportResidual public

-- Package contraction is not Clay promotion.
clayPromotion : Bool
clayPromotion = false
