module DASHI.Physics.Closure.ConeWidthDefectScalingBase where

open import Level using (zero)
open import DASHI.MDL.MDLDescentTradeoff
  using (AddMonoid; OrderedMonoid)

----------------------------------------------------------------------
-- Abstract cone-width defect scaling model.
--
-- Provides an ordered carrier with multiplication and four distinguished
-- constants:
--
--   • ε      — near-extremizer cone width
--   • α      — cross-defect linear constant
--   • β      — pure-defect quadratic constant
--   • η-cross — cross-defect term (sup-normalized)
--   • η-pure  — pure-defect term  (sup-normalized)
--
-- Lemma B (internal):
--     η-cross ≤ α · ε      (cross defect is linear in cone width)
--     η-pure  ≤ β · ε·ε    (pure defect is quadratic in cone width)
--
-- The multiplication operation _*_ is part of the model interface but
-- is not required to satisfy full semiring laws — only the monotonicity
-- needed for scaling inequalities is carried.

record ConeWidthDefectScalingModel : Set₁ where
  constructor mkConeWidthDefectScalingModel
  field
    orderedMonoid : OrderedMonoid {zero}

  open OrderedMonoid orderedMonoid public
  open AddMonoid M public

  field
    _*_ : N → N → N

    ε α β : N
    η-cross η-pure : N

    cross≤αε : η-cross ≤ (α * ε)
    pure≤βε² : η-pure ≤ (β * (ε * ε))

    *-mono : ∀ a b c d → a ≤ b → c ≤ d → (a * c) ≤ (b * d)

  total≤αε+βε² : (η-cross + η-pure) ≤ ((α * ε) + (β * (ε * ε)))
  total≤αε+βε² =
    mono+ η-cross (α * ε) η-pure (β * (ε * ε))
      cross≤αε
      pure≤βε²

open ConeWidthDefectScalingModel public
