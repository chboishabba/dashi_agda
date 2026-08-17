module DASHI.Moonshine.DeltaNormalizedWeight12SameObjectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre, "A Course in Arithmetic", GTM 7, Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- Toshitsune Miyake, "Modular Forms", Springer Monographs in Mathematics,
-- 2006. DOI: 10.1007/3-540-29593-3.
--
-- ARISTOTLE / HARMONIC CONTEXT
--
-- The later supplied Delta development proves the genuine analytic chain
-- Delta=eta^24 -> logarithmic derivative -> E2 quasimodular defect ->
-- S-transformation -> full modularity.  DASHI does not yet have the eta/E2
-- analytic substrate needed to reproduce that proof route source-for-source.
--
-- DASHI CONTRIBUTION
--
-- The repository DOES already prove all-SL2(Z) weight-12 transformation of
-- D=E4^3-E6^2 from an explicit Eisenstein lattice-reindexing theorem.  This
-- file removes two downstream pseudo-frontiers:
--
--  * any normalization commuting with multiplication by the automorphy factor
--    inherits weight 12 automatically (in particular division by 1728 once
--    instantiated in a concrete scalar field);
--  * once eta^24 is identified pointwise with that normalized Delta, its full
--    weight-12 transformation is derived, not accepted independently.
--
-- Thus the remaining source-parity theorem is sharply the genuine analytic
-- eta^24 / E2 identification route, not S/T modularity again.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Disc

record WeightCompatibleNormalization
    (M : Eisenstein.EisensteinAnalyticModel) : Set₁ where
  field
    normalize : Eisenstein.Scalar M → Eisenstein.Scalar M
    normalizeWeightAction :
      (factor value : Eisenstein.Scalar M) →
      normalize (Eisenstein._*ˢ_ M factor value)
      ≡ Eisenstein._*ˢ_ M factor (normalize value)

open WeightCompatibleNormalization public

normalizedDelta :
  (M : Eisenstein.EisensteinAnalyticModel) →
  Disc.DiscriminantAlgebra M →
  WeightCompatibleNormalization M →
  Eisenstein.Parameter M → Eisenstein.Scalar M
normalizedDelta M A N tau =
  normalize N (Disc.unnormalisedDiscriminant M A tau)

normalizedDeltaTransformsAtWeight12 :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Disc.DiscriminantAlgebra M) →
  (N : WeightCompatibleNormalization M) →
  (g : Eisenstein.SL2Z) →
  (tau : Eisenstein.Parameter M) →
  normalizedDelta M A N (Eisenstein.actParameter M g tau)
  ≡ Eisenstein._*ˢ_ M
      (Eisenstein.power M (Eisenstein.denominator M g tau) 12)
      (normalizedDelta M A N tau)
normalizedDeltaTransformsAtWeight12 M A N g tau =
  trans
    (cong (normalize N)
      (Disc.unnormalisedDiscriminantTransformation M A g tau))
    (normalizeWeightAction N
      (Eisenstein.power M (Eisenstein.denominator M g tau) 12)
      (Disc.unnormalisedDiscriminant M A tau))

record Eta24SameObject
    (M : Eisenstein.EisensteinAnalyticModel)
    (A : Disc.DiscriminantAlgebra M)
    (N : WeightCompatibleNormalization M) : Set₁ where
  field
    eta24 : Eisenstein.Parameter M → Eisenstein.Scalar M
    eta24IsNormalizedDelta :
      (tau : Eisenstein.Parameter M) →
      eta24 tau ≡ normalizedDelta M A N tau

open Eta24SameObject public

eta24TransformsAtWeight12 :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Disc.DiscriminantAlgebra M) →
  (N : WeightCompatibleNormalization M) →
  (same : Eta24SameObject M A N) →
  (g : Eisenstein.SL2Z) →
  (tau : Eisenstein.Parameter M) →
  eta24 same (Eisenstein.actParameter M g tau)
  ≡ Eisenstein._*ˢ_ M
      (Eisenstein.power M (Eisenstein.denominator M g tau) 12)
      (eta24 same tau)
eta24TransformsAtWeight12 M A N same g tau =
  trans
    (eta24IsNormalizedDelta same (Eisenstein.actParameter M g tau))
    (trans
      (normalizedDeltaTransformsAtWeight12 M A N g tau)
      (cong
        (λ value →
          Eisenstein._*ˢ_ M
            (Eisenstein.power M (Eisenstein.denominator M g tau) 12)
            value)
        (sym (eta24IsNormalizedDelta same tau))))

record DeltaAnalyticParityBoundary : Set where
  field
    unnormalisedWeight12AlreadyDerived : Bool
    normalizationTransportDerived : Bool
    eta24ModularityDerivedFromSameObject : Bool
    eta24EqualsNormalizedDiscriminantConstructedHere : Bool
    e2LogDerivativeProofRouteConstructedHere : Bool

canonicalDeltaAnalyticParityBoundary : DeltaAnalyticParityBoundary
canonicalDeltaAnalyticParityBoundary = record
  { unnormalisedWeight12AlreadyDerived = true
  ; normalizationTransportDerived = true
  ; eta24ModularityDerivedFromSameObject = true
  ; eta24EqualsNormalizedDiscriminantConstructedHere = false
  ; e2LogDerivativeProofRouteConstructedHere = false
  }
