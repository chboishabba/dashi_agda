{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1SourcePotentialCovarianceExact where

------------------------------------------------------------------------
-- P1 SOURCE GEOMETRY: POTENTIAL COVARIANCE DOES NOT NEED D1 COVARIANCE.
--
-- The older E1 geometry records bundled two logically distinct facts:
--   (a) finite component permutation + local-activity covariance;
--   (b) covariance of the derivative itself.
--
-- For the path-derivative proof of P1 only (a) is needed to prove invariance of
-- the scalar effective potential.  Differentiated covariance is then derived
-- afterwards from ordinary directional-derivative semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyE1ComponentPermutationExact as Permutation
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite

record LiteralSourcePotentialEuclideanGeometry
    (carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier)
    (EuclideanAction : Set) : Set₁ where
  field
    actBackground :
      EuclideanAction →
      Source.Background (Carrier.source carrier) →
      Source.Background (Carrier.source carrier)

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

open LiteralSourcePotentialEuclideanGeometry public

localizedPotentialCovariant :
  ∀ {carrier EuclideanAction}
    (geometry : LiteralSourcePotentialEuclideanGeometry carrier EuclideanAction)
    action background →
  Finite.localizedPotential (Carrier.finiteAction carrier)
    (actBackground geometry action background)
  ≡
  Finite.localizedPotential (Carrier.finiteAction carrier) background
localizedPotentialCovariant {carrier = carrier} geometry action background =
  let
    components =
      Source.components (Carrier.source carrier)
        (Carrier.scale carrier) (Carrier.volume carrier)

    movedWeight =
      λ component →
        Source.cmp116PhysicalLocalizedActivity
          (Carrier.source carrier)
          (Carrier.scale carrier)
          (Carrier.volume carrier)
          component
          (actBackground geometry action background)

    permutedWeight =
      λ component →
        Source.cmp116PhysicalLocalizedActivity
          (Carrier.source carrier)
          (Carrier.scale carrier)
          (Carrier.volume carrier)
          (actComponent geometry action component)
          (actBackground geometry action background)

    originalWeight =
      λ component →
        Source.cmp116PhysicalLocalizedActivity
          (Carrier.source carrier)
          (Carrier.scale carrier)
          (Carrier.volume carrier)
          component background

    reindex :
      Finite.sumℝ (Finite.mapList movedWeight components)
      ≡ Finite.sumℝ (Finite.mapList permutedWeight components)
    reindex =
      trans
        (sym
          (Permutation.sumPermutationInvariant
            (Permutation.mapPermutation movedWeight
              (componentPermutation geometry action))))
        (cong Finite.sumℝ
          (Permutation.mapComposition movedWeight
            (actComponent geometry action) components))
  in
  trans reindex
    (DASHI.Physics.Foundations.CMP119CosmologyE1LocalizedD1CovarianceExact.sumMappedCong
      permutedWeight originalWeight components
      (λ component →
        localizedActivityCovariant geometry action component background))

effectivePotentialCovariant :
  ∀ {carrier EuclideanAction}
    (geometry : LiteralSourcePotentialEuclideanGeometry carrier EuclideanAction)
    action background →
  Carrier.effectivePotential carrier
    (actBackground geometry action background)
  ≡ Carrier.effectivePotential carrier background
effectivePotentialCovariant {carrier = carrier} geometry action background =
  trans
    (Source.effectivePotentialIsLocalizedCompositeSum
      (Carrier.source carrier)
      (Carrier.scale carrier)
      (Carrier.volume carrier)
      (actBackground geometry action background))
    (trans
      (localizedPotentialCovariant geometry action background)
      (sym
        (Source.effectivePotentialIsLocalizedCompositeSum
          (Carrier.source carrier)
          (Carrier.scale carrier)
          (Carrier.volume carrier)
          background)))

potentialCovarianceNeedsNoDerivativeCovariancePremise : Bool
potentialCovarianceNeedsNoDerivativeCovariancePremise = true

p1DerivativeCovarianceCanBeDerivedAfterPotentialCovariance : Bool
p1DerivativeCovarianceCanBeDerivedAfterPotentialCovariance = true
