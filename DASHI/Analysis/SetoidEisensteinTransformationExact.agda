module DASHI.Analysis.SetoidEisensteinTransformationExact where

------------------------------------------------------------------------
-- SETOID-NATIVE EISENSTEIN LATTICE REINDEXING
--
-- CROSS-POLLINATION
--
-- The repository already owns the exact SL2(Z) lattice-index bijection and
-- propositional-equality Eisenstein transformation theorem.  The constructive
-- Bishop complex carrier used by the current q-series theorem is intentionally
-- setoid-native, however, so propositional equality is the wrong boundary.
--
-- This owner factors the reindexing argument through an arbitrary equivalence
-- relation.  It reuses the existing LatticePoint / SL2Z / forwardIndex objects
-- and requires only the same three analytic sum laws:
--
--   pointwise congruence
--   reindex invariance
--   factor extraction
--
-- plus the local transformed-summand law.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Legacy

record SetoidEisensteinAnalyticModel : Set₁ where
  field
    Scalar : Set
    _≈ˢ_ : Scalar → Scalar → Set
    equivTrans :
      ∀ {x y z : Scalar} →
      x ≈ˢ y → y ≈ˢ z → x ≈ˢ z

    _*ˢ_ : Scalar → Scalar → Scalar

    Parameter : Set
    actParameter : Legacy.SL2Z → Parameter → Parameter
    denominator : Legacy.SL2Z → Parameter → Scalar
    power : Scalar → Nat → Scalar

    summand : Nat → Legacy.LatticePoint → Parameter → Scalar
    eisensteinSum : (Legacy.LatticePoint → Scalar) → Scalar

    pointwiseCongruence :
      ∀ {f h : Legacy.LatticePoint → Scalar} →
      ((p : Legacy.LatticePoint) → f p ≈ˢ h p) →
      eisensteinSum f ≈ˢ eisensteinSum h

    reindexInvariant :
      (g : Legacy.SL2Z) →
      (f : Legacy.LatticePoint → Scalar) →
      eisensteinSum (λ p → f (Legacy.forwardIndex g p))
      ≈ˢ eisensteinSum f

    factorOut :
      (factor : Scalar) →
      (f : Legacy.LatticePoint → Scalar) →
      eisensteinSum (λ p → factor *ˢ f p)
      ≈ˢ factor *ˢ eisensteinSum f

    summandTransformation :
      (weight : Nat) →
      (g : Legacy.SL2Z) →
      (tau : Parameter) →
      (p : Legacy.LatticePoint) →
      summand weight p (actParameter g tau)
      ≈ˢ
      power (denominator g tau) weight
        *ˢ summand weight (Legacy.forwardIndex g p) tau

open SetoidEisensteinAnalyticModel public

SetoidEisensteinSeries :
  (M : SetoidEisensteinAnalyticModel) →
  Nat → Parameter M → Scalar M
SetoidEisensteinSeries M weight tau =
  eisensteinSum M (λ p → summand M weight p tau)

setoidEisensteinTransformation :
  (M : SetoidEisensteinAnalyticModel) →
  (weight : Nat) →
  (g : Legacy.SL2Z) →
  (tau : Parameter M) →
  _≈ˢ_ M
    (SetoidEisensteinSeries M weight (actParameter M g tau))
    (_*ˢ_ M
      (power M (denominator M g tau) weight)
      (SetoidEisensteinSeries M weight tau))
setoidEisensteinTransformation M weight g tau =
  equivTrans M
    (pointwiseCongruence M
      (summandTransformation M weight g tau))
    (equivTrans M
      (factorOut M
        (power M (denominator M g tau) weight)
        (λ p → summand M weight (Legacy.forwardIndex g p) tau))
      (reindexInvariant M g
        (λ p → summand M weight p tau)))

------------------------------------------------------------------------
-- Backward-compatible adapter: the old theorem is a special case with
-- propositional equality as the setoid relation.
------------------------------------------------------------------------

legacyAsSetoid :
  Legacy.EisensteinAnalyticModel →
  SetoidEisensteinAnalyticModel
legacyAsSetoid M =
  record
    { Scalar = Legacy.Scalar M
    ; _≈ˢ_ = _≡_
    ; equivTrans = trans
    ; _*ˢ_ = Legacy._*ˢ_ M
    ; Parameter = Legacy.Parameter M
    ; actParameter = Legacy.actParameter M
    ; denominator = Legacy.denominator M
    ; power = Legacy.power M
    ; summand = Legacy.summand M
    ; eisensteinSum = Legacy.eisensteinSum M
    ; pointwiseCongruence = Legacy.pointwiseCongruence M
    ; reindexInvariant = Legacy.reindexInvariant M
    ; factorOut = Legacy.factorOut M
    ; summandTransformation = Legacy.summandTransformation M
    }
