{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1SourceDerivativeNaturalityExact where

------------------------------------------------------------------------
-- PREFERRED SOURCE-LOCAL E1 ROUTE.
--
-- Pin the calculus-level derivative naturality law to the exact Round103
-- CMP109/CMP116 carrier.  Local D1 covariance then becomes compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

import DASHI.Physics.Foundations.CMP119CosmologyE1DerivativeNaturalityExact as Natural
import DASHI.Physics.Foundations.CMP119CosmologyE1ComponentPermutationExact as PermE1
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1

record LiteralSourceDerivativeNaturality
    (carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier)
    (calculus :
      D1.FirstVariationLinearity
        (Source.Background (Carrier.source carrier))
        (Source.Tangent (Carrier.source carrier)))
    (EuclideanAction : Set)
    : Set₁ where
  field
    derivativeNaturality :
      Natural.EuclideanFirstVariationNaturality
        (Source.Background (Carrier.source carrier))
        (Source.Tangent (Carrier.source carrier))
        EuclideanAction calculus

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
        (Natural.actConfiguration derivativeNaturality action background)
      ≡
      Source.cmp116PhysicalLocalizedActivity
        (Carrier.source carrier)
        (Carrier.scale carrier)
        (Carrier.volume carrier)
        component background

open LiteralSourceDerivativeNaturality public

asLocalizedActivityEuclideanGeometry :
  ∀ {carrier calculus EuclideanAction} →
  LiteralSourceDerivativeNaturality carrier calculus EuclideanAction →
  Natural.LocalizedActivityEuclideanGeometry
    (Carrier.finiteAction carrier) calculus EuclideanAction
asLocalizedActivityEuclideanGeometry data = record
  { Natural.LocalizedActivityEuclideanGeometry.derivativeNaturality =
      derivativeNaturality data
  ; Natural.LocalizedActivityEuclideanGeometry.actComponent =
      actComponent data
  ; Natural.LocalizedActivityEuclideanGeometry.componentPermutation =
      componentPermutation data
  ; Natural.LocalizedActivityEuclideanGeometry.localActivityCovariant =
      localizedActivityCovariant data
  }

asComponentPermutationCovariance :
  ∀ {carrier calculus EuclideanAction} →
  LiteralSourceDerivativeNaturality carrier calculus EuclideanAction →
  PermE1.LocalizedComponentPermutationCovariance
    (Carrier.finiteAction carrier) calculus EuclideanAction
asComponentPermutationCovariance data =
  Natural.asComponentPermutationCovariance
    (asLocalizedActivityEuclideanGeometry data)

sourceLocalD1CovarianceIsCompilerOutput : Bool
sourceLocalD1CovarianceIsCompilerOutput = true

sourceE1HardCalculusLeafIsOneDerivativeNaturalityLaw : Bool
sourceE1HardCalculusLeafIsOneDerivativeNaturalityLaw = true
