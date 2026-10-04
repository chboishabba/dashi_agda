{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1SourceLocalizedGeometryExact where

------------------------------------------------------------------------
-- SOURCE-PIN THE LAST LOCAL E1 GEOMETRY.
--
-- Round103 already selects ONE literal CMP109/CMP116 continuation together
-- with its scale, volume, background/tangent carrier and localized activities.
-- The finite E1 compiler is therefore instantiated on exactly
--
--   Source.atScaleVolume source scale volume.
--
-- No arbitrary FiniteLocalizedEffectiveAction remains.  The physical leaves
-- are now only the actual Euclidean actions on Tangent/Component and the two
-- literal local covariance laws.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

import DASHI.Physics.Foundations.CMP119CosmologyE1ComponentPermutationExact as PermE1
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1

record LiteralSourceLocalizedEuclideanGeometry
    (carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier)
    (calculus :
      D1.FirstVariationLinearity
        (Source.Background (Carrier.source carrier))
        (Source.Tangent (Carrier.source carrier)))
    (EuclideanAction : Set)
    : Set₁ where
  field
    actBackground :
      EuclideanAction →
      Source.Background (Carrier.source carrier) →
      Source.Background (Carrier.source carrier)

    actTangent :
      EuclideanAction →
      Source.Tangent (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier)

    actComponent :
      EuclideanAction →
      Source.Component (Carrier.source carrier) →
      Source.Component (Carrier.source carrier)

    componentPermutation :
      ∀ action →
      Finite.mapList (actComponent action)
        (Source.components (Carrier.source carrier)
          (Carrier.scale carrier) (Carrier.volume carrier))
      Perm.↭
      Source.components (Carrier.source carrier)
        (Carrier.scale carrier) (Carrier.volume carrier)

    localizedActivityCovariant :
      ∀ action component background →
      Source.cmp116PhysicalLocalizedActivity
        (Carrier.source carrier)
        (Carrier.scale carrier)
        (Carrier.volume carrier)
        (actComponent action component)
        (actBackground action background)
      ≡
      Source.cmp116PhysicalLocalizedActivity
        (Carrier.source carrier)
        (Carrier.scale carrier)
        (Carrier.volume carrier)
        component background

    localizedD1Covariant :
      ∀ action component background tangent →
      D1.firstVariation calculus
        (Source.cmp116PhysicalLocalizedActivity
          (Carrier.source carrier)
          (Carrier.scale carrier)
          (Carrier.volume carrier)
          (actComponent action component))
        (actBackground action background)
        (actTangent action tangent)
      ≡
      D1.firstVariation calculus
        (Source.cmp116PhysicalLocalizedActivity
          (Carrier.source carrier)
          (Carrier.scale carrier)
          (Carrier.volume carrier)
          component)
        background tangent

open LiteralSourceLocalizedEuclideanGeometry public

asComponentPermutationCovariance :
  ∀ {carrier calculus EuclideanAction} →
  LiteralSourceLocalizedEuclideanGeometry
    carrier calculus EuclideanAction →
  PermE1.LocalizedComponentPermutationCovariance
    (Carrier.finiteAction carrier)
    calculus
    EuclideanAction
asComponentPermutationCovariance geometry = record
  { PermE1.LocalizedComponentPermutationCovariance.actConfiguration =
      actBackground geometry
  ; PermE1.LocalizedComponentPermutationCovariance.actTangent =
      actTangent geometry
  ; PermE1.LocalizedComponentPermutationCovariance.actComponent =
      actComponent geometry
  ; PermE1.LocalizedComponentPermutationCovariance.componentPermutation =
      componentPermutation geometry
  ; PermE1.LocalizedComponentPermutationCovariance.localActivityCovariant =
      localizedActivityCovariant geometry
  ; PermE1.LocalizedComponentPermutationCovariance.localD1Covariant =
      localizedD1Covariant geometry
  }

sourceLocalizedFiniteActionNoLongerArbitrary : Bool
sourceLocalizedFiniteActionNoLongerArbitrary = true

remainingE1GeometryIsLiteralTangentComponentActionAndLocalCovariance : Bool
remainingE1GeometryIsLiteralTangentComponentActionAndLocalCovariance = true
