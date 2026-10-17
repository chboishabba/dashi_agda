{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109CanonicalSourceSemanticsObligationsExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanCMP109CanonicalResidualInstantiationExact as Inst

------------------------------------------------------------------------
-- Canonical non-Round owner for the residual CMP109 source-semantics package.
--
-- All carrier types, source-attachment relations, selected D1 functions, and
-- the beta algebra theorem are PARAMETERS fixed by the selected source context.
-- They are not record fields chosen by the residual constructor.
------------------------------------------------------------------------

record CMP109CanonicalSourceSemanticsObligations
    (SelectedSource : Set)
    (selectedSource : SelectedSource)
    (Producer : Set)
    (ProducerBelongsToSelectedSource : SelectedSource → Producer → Set)
    (TubePoint ShootingMap BetaScalar : Set)
    (ShootingMapBelongsToSelectedSource : SelectedSource → ShootingMap → Set)
    (initialInverseSquare : ShootingMap → TubePoint → BetaScalar)
    (renormalisationMap : ShootingMap → TubePoint → TubePoint)
    (cumulativeBeta : ShootingMap → TubePoint → BetaScalar)
    (minus : BetaScalar → BetaScalar → BetaScalar)
    (betaDifferenceAlgebra :
      ∀ shootingMap left right →
      minus
        (initialInverseSquare shootingMap (renormalisationMap shootingMap left))
        (initialInverseSquare shootingMap (renormalisationMap shootingMap right))
      ≡
      minus
        (cumulativeBeta shootingMap left)
        (cumulativeBeta shootingMap right))
    (Component Background Tangent D1Scalar : Set)
    (physicalCompositeD1 substitutedD1 :
      Component → Background → Tangent → D1Scalar)
    (D1BelongsToSelectedSource :
      SelectedSource → (Component → Background → Tangent → D1Scalar) → Set)
    (physicalCompositeD1BelongsToSelectedSource :
      D1BelongsToSelectedSource selectedSource physicalCompositeD1)
    (substitutedD1BelongsToSelectedSource :
      D1BelongsToSelectedSource selectedSource substitutedD1)
    (cutoff : Nat) : Set₁ where
  field
    generatedHistoryResponseProducer :
      Inst.CMP109GeneratedHistoryResponseResidual
        selectedSource Producer ProducerBelongsToSelectedSource

    betaDifferenceDecomposition :
      Inst.SelectedCMP109BetaDifferenceAttachment
        selectedSource TubePoint ShootingMap BetaScalar
        ShootingMapBelongsToSelectedSource
        initialInverseSquare renormalisationMap cumulativeBeta minus
        betaDifferenceAlgebra

    physicalCompositeD1ChainRule :
      Inst.PhysicalCompositeD1TransportResidual
        selectedSource Component Background Tangent D1Scalar
        physicalCompositeD1 substitutedD1
        D1BelongsToSelectedSource
        physicalCompositeD1BelongsToSelectedSource
        substitutedD1BelongsToSelectedSource

------------------------------------------------------------------------

open CMP109CanonicalSourceSemanticsObligations public

sourceSemanticsExtractionCreatesInhabitant : Bool
sourceSemanticsExtractionCreatesInhabitant = false

clayPromotion : Bool
clayPromotion = false
