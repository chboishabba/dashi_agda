module DASHI.Analysis.StrictKernelMomentRatioTwoSupportExact where

------------------------------------------------------------------------
-- Exact two-support strict-kernel -> moment-determinant identity.
--
-- For support points u<v with increasing score q_u<q_v, positive base
-- weights w_u,w_v, and a two-height kernel K, define
--
--   M0(h) = w_u K(h,u) + w_v K(h,v)
--   Mq(h) = q_u w_u K(h,u) + q_v w_v K(h,v).
--
-- Then
--
--   M0(a) Mq(p) - Mq(a) M0(p)
--     = w_u w_v (q_v-q_u)
--       [K(a,u)K(p,v)-K(a,v)K(p,u)].
--
-- Thus on two supports the moment determinant is literally the strict TP2
-- kernel minor multiplied by the positive support/score prefactor.  This is
-- the finite algebraic core of the continuum symmetrized double-integral
-- identity used by G21.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

moment0 : ℚ → ℚ → ℚ → ℚ → ℚ
moment0 wu wv ku kv = wu * ku + wv * kv

momentQ : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
momentQ qu qv wu wv ku kv =
  qu * wu * ku + qv * wv * kv

tp2Minor : ℚ → ℚ → ℚ → ℚ → ℚ
tp2Minor kau kav kpu kpv = kau * kpv - kav * kpu

twoSupportMomentDeterminant :
  ℚ → ℚ →
  ℚ → ℚ →
  ℚ → ℚ →
  ℚ → ℚ →
  ℚ
twoSupportMomentDeterminant qu qv wu wv kau kav kpu kpv =
  moment0 wu wv kau kav * momentQ qu qv wu wv kpu kpv
  -
  momentQ qu qv wu wv kau kav * moment0 wu wv kpu kpv

twoSupportTP2MomentIdentity :
  (qu qv wu wv kau kav kpu kpv : ℚ) →
  twoSupportMomentDeterminant qu qv wu wv kau kav kpu kpv
  ≡
  (wu * wv * (qv - qu)) * tp2Minor kau kav kpu kpv
twoSupportTP2MomentIdentity qu qv wu wv kau kav kpu kpv =
  solve (qu ∷ qv ∷ wu ∷ wv ∷ kau ∷ kav ∷ kpu ∷ kpv ∷ [])

------------------------------------------------------------------------
-- Odd G21 naming specialization.  Substituting
--
--   K(h,u)=sinh(h u),  q(u)=u^2,
--
-- turns this identity into the two-support version of
--
--   N1(a) N3(p) - N3(a) N1(p) > 0
--
-- whenever the sinh kernel minor and support/weight factors are positive.
------------------------------------------------------------------------

oddTwoSupportCompositionIdentity :
  (u2 v2 wu wv sinhAU sinhAV sinhPU sinhPV : ℚ) →
  twoSupportMomentDeterminant
    u2 v2 wu wv sinhAU sinhAV sinhPU sinhPV
  ≡
  (wu * wv * (v2 - u2))
    * (sinhAU * sinhPV - sinhAV * sinhPU)
oddTwoSupportCompositionIdentity = twoSupportTP2MomentIdentity

record TwoSupportTP2CompositionBoundary : Set where
  constructor twoSupportTP2CompositionBoundary
  field
    exactTwoSupportCompositionDerived : Bool
    exactTwoSupportCompositionDerivedIsTrue :
      exactTwoSupportCompositionDerived ≡ true
    oddSinhSpecializationIdentityDerived : Bool
    oddSinhSpecializationIdentityDerivedIsTrue :
      oddSinhSpecializationIdentityDerived ≡ true
    strictOrderFromPositiveFactorsDerived : Bool
    strictOrderFromPositiveFactorsDerivedIsFalse :
      strictOrderFromPositiveFactorsDerived ≡ false
    continuumIntegralCompositionDerived : Bool
    continuumIntegralCompositionDerivedIsFalse :
      continuumIntegralCompositionDerived ≡ false

canonicalTwoSupportTP2CompositionBoundary : TwoSupportTP2CompositionBoundary
canonicalTwoSupportTP2CompositionBoundary =
  twoSupportTP2CompositionBoundary true refl true refl false refl false refl
