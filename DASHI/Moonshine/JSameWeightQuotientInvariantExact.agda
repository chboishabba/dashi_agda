module DASHI.Moonshine.JSameWeightQuotientInvariantExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Delta

------------------------------------------------------------------------
-- SAME-WEIGHT QUOTIENT INVARIANCE FOR THE J RATIO
--
-- Existing repo theorems already pay:
--
--   E4(g tau)   = d^4  E4(tau)
--   E4(g tau)^3 = d^12 E4(tau)^3
--   D(g tau)    = d^12 D(tau)
--
-- where D = E4^3 - E6^2 and d is the modular automorphy denominator.
--
-- The only algebraic weld required to obtain weight-zero invariance of
-- E4^3 / D is cancellation of the common weight-12 factor.  That cancellation
-- is intentionally parameterised behind explicit safety witnesses instead of
-- silently assuming division by zero cannot occur.
------------------------------------------------------------------------

record QuotientCancellationAlgebra
    (M : Eisenstein.EisensteinAnalyticModel) : Set₁ where
  field
    _/ˢ_ : Eisenstein.Scalar M → Eisenstein.Scalar M → Eisenstein.Scalar M

    ScalingSafe : Eisenstein.Scalar M → Set
    DenominatorSafe : Eisenstein.Scalar M → Set

    cancelCommonScale :
      (factor numerator denominator : Eisenstein.Scalar M) →
      ScalingSafe factor →
      DenominatorSafe denominator →
      _/ˢ_
        (Eisenstein._*ˢ_ M factor numerator)
        (Eisenstein._*ˢ_ M factor denominator)
      ≡ _/ˢ_ numerator denominator

open QuotientCancellationAlgebra public

jNumerator :
  (M : Eisenstein.EisensteinAnalyticModel) →
  Eisenstein.Parameter M →
  Eisenstein.Scalar M
jNumerator M tau = Delta.cube M (Delta.E4 M tau)

jDenominator :
  (M : Eisenstein.EisensteinAnalyticModel) →
  Delta.DiscriminantAlgebra M →
  Eisenstein.Parameter M →
  Eisenstein.Scalar M
jDenominator M A = Delta.unnormalisedDiscriminant M A

jRatio :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Delta.DiscriminantAlgebra M) →
  (Q : QuotientCancellationAlgebra M) →
  Eisenstein.Parameter M →
  Eisenstein.Scalar M
jRatio M A Q tau = _/ˢ_ Q (jNumerator M tau) (jDenominator M A tau)

------------------------------------------------------------------------
-- Numerator carries the same weight-12 factor as the discriminant.
------------------------------------------------------------------------

jNumeratorTransformation :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Delta.DiscriminantAlgebra M) →
  (g : Eisenstein.SL2Z) →
  (tau : Eisenstein.Parameter M) →
  jNumerator M (Eisenstein.actParameter M g tau)
  ≡ Eisenstein._*ˢ_ M
      (Eisenstein.power M (Eisenstein.denominator M g tau) 12)
      (jNumerator M tau)
jNumeratorTransformation M A g tau =
  trans
    (cong (Delta.cube M)
      (Eisenstein.eisensteinTransformation M 4 g tau))
    (Delta.scaledCubeWeight4 M A
      (Eisenstein.denominator M g tau)
      (Delta.E4 M tau))

------------------------------------------------------------------------
-- Conditional exact weight-zero invariance.
--
-- This is the algebraic modularity step.  It does NOT prove either safety
-- witness.  In a concrete complex model they correspond to the nonvanishing
-- obligations required to form/cancel the quotient on the intended domain.
------------------------------------------------------------------------

jRatioInvariant :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Delta.DiscriminantAlgebra M) →
  (Q : QuotientCancellationAlgebra M) →
  (g : Eisenstein.SL2Z) →
  (tau : Eisenstein.Parameter M) →
  ScalingSafe Q
    (Eisenstein.power M (Eisenstein.denominator M g tau) 12) →
  DenominatorSafe Q (jDenominator M A tau) →
  jRatio M A Q (Eisenstein.actParameter M g tau)
  ≡ jRatio M A Q tau
jRatioInvariant M A Q g tau scaleSafe denominatorSafe =
  trans
    (cong₂ (_/ˢ_ Q)
      (jNumeratorTransformation M A g tau)
      (Delta.unnormalisedDiscriminantTransformation M A g tau))
    (cancelCommonScale Q
      (Eisenstein.power M (Eisenstein.denominator M g tau) 12)
      (jNumerator M tau)
      (jDenominator M A tau)
      scaleSafe denominatorSafe)

------------------------------------------------------------------------
-- Status boundary.
------------------------------------------------------------------------

record JWeightZeroQuotientBoundary : Set where
  constructor j-weight-zero-quotient-boundary
  field
    numeratorWeight12Paid : Set
    denominatorWeight12Paid : Set
    commonScaleCancellationInterfacePaid : Set
    quotientInvarianceConditionalOnSafetyPaid : Set
    automorphyScaleSafetyConcrete : Set
    denominatorNonvanishingConcrete : Set
    meromorphicDomainConcrete : Set

canonicalJWeightZeroQuotientBoundary : JWeightZeroQuotientBoundary
canonicalJWeightZeroQuotientBoundary =
  j-weight-zero-quotient-boundary
    (∀ {M : Eisenstein.EisensteinAnalyticModel}
       {A : Delta.DiscriminantAlgebra M}
       {g : Eisenstein.SL2Z}
       {tau : Eisenstein.Parameter M} →
       jNumerator M (Eisenstein.actParameter M g tau)
       ≡ Eisenstein._*ˢ_ M
           (Eisenstein.power M (Eisenstein.denominator M g tau) 12)
           (jNumerator M tau))
    (∀ {M : Eisenstein.EisensteinAnalyticModel}
       {A : Delta.DiscriminantAlgebra M}
       {g : Eisenstein.SL2Z}
       {tau : Eisenstein.Parameter M} →
       jDenominator M A (Eisenstein.actParameter M g tau)
       ≡ Eisenstein._*ˢ_ M
           (Eisenstein.power M (Eisenstein.denominator M g tau) 12)
           (jDenominator M A tau))
    (∀ {M : Eisenstein.EisensteinAnalyticModel} →
       QuotientCancellationAlgebra M → Set)
    (∀ {M : Eisenstein.EisensteinAnalyticModel}
       {A : Delta.DiscriminantAlgebra M}
       {Q : QuotientCancellationAlgebra M} →
       ((g : Eisenstein.SL2Z) →
        (tau : Eisenstein.Parameter M) →
        ScalingSafe Q
          (Eisenstein.power M (Eisenstein.denominator M g tau) 12) →
        DenominatorSafe Q (jDenominator M A tau) →
        jRatio M A Q (Eisenstein.actParameter M g tau)
        ≡ jRatio M A Q tau))
    Set Set Set
