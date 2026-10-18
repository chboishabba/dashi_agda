{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityWilsonPlaquetteBasisOrientationExact where

------------------------------------------------------------------------
-- EXACT SOURCE CONVENTION CONVERSION (finite rational localized action).
--
-- Wilson (1974), "Confinement of Quarks",
-- DOI: 10.1103/PhysRevD.10.2445.
-- Bałaban CMP109 (1987), DOI: 10.1007/BF01215223.
-- Bałaban CMP119 (1988), DOI: 10.1007/BF01217741.
--
-- The selected SU(N) Wilson carrier in
-- BalabanClayT4SUNWilsonActionConventionExact uses
--    W+ = sum_p (1 - Re Tr U_p / N),    S_W = u * W+.
-- An equivalent negative-cost basis is W- = - W+:
--    S_W = c * W-  with c = -u.
--
-- The - sign is thus a BASIS ORIENTATION, not a distinct physical beta sign.
-- Here the normalizations are computed on the T4 rational localized carrier.
-- This does NOT assert that the external CMP119 selected source has yet been
-- instantiated in that carrier; that same-object comparison is separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Inverse

positiveWilsonBasis : T4.LocalizedAction
positiveWilsonBasis = T4.plaquetteBasisAction

negativeWilsonBasis : T4.LocalizedAction
negativeWilsonBasis = T4.scaleLocalizedAction (- 1ℚ) positiveWilsonBasis

positiveWilsonAction negativeWilsonAction : ℚ → T4.LocalizedAction
positiveWilsonAction u = T4.scaleLocalizedAction u positiveWilsonBasis
negativeWilsonAction c = T4.scaleLocalizedAction c negativeWilsonBasis

negativeWilsonBasisPlaquetteCoefficient :
  T4.plaquetteCoefficientProjector negativeWilsonBasis ≡ - 1ℚ
negativeWilsonBasisPlaquetteCoefficient = refl

negativeWilsonActionProjectedCoefficient :
  ∀ c → T4.plaquetteCoefficientProjector (negativeWilsonAction c) ≡ - c
negativeWilsonActionProjectedCoefficient c = Ring.solve-∀ c

sameWilsonActionOppositeBasis :
  ∀ u → positiveWilsonAction u ≡ negativeWilsonAction (- u)
sameWilsonActionOppositeBasis u =
  cong₂ T4.localizedAction (Ring.solve-∀ u) (Ring.solve-∀ u)

------------------------------------------------------------------------
-- STANDARD BARE WILSON NORMALIZATION VS REPOSITORY UNIT-COEFFICIENT
-- CONVENTION. For SU(N), with W = sum_p [1 - Re Tr U_p / N],
-- the standard continuum-matched bare coefficient is 2N / g_0^2.
-- For SU(2), this is FOUR times inverse-square coupling, not ONE.
-- Moving the factor four into the basis gives a coefficient of +/-u.
-- Do not identify these two conventions without this conversion.
--
-- Primary: Wilson, Phys. Rev. D 10 (1974), DOI above.
-- Lattice normalizations: check trace and generator conventions on the
-- selected CMP119 *renormalized* action, not only on a bare Wilson lattice.
------------------------------------------------------------------------

four : ℚ
four = (1ℚ + 1ℚ) + (1ℚ + 1ℚ)
  where
    open import Data.Rational.Base using (_+_)

standardSU2WilsonAction : ℚ → T4.LocalizedAction
standardSU2WilsonAction u =
  T4.scaleLocalizedAction (four * u) positiveWilsonBasis

negativeStandardSU2WilsonAction : ℚ → T4.LocalizedAction
negativeStandardSU2WilsonAction c =
  T4.scaleLocalizedAction c negativeWilsonBasis

standardSU2WilsonSameNegativeOrientation :
  ∀ u →
  standardSU2WilsonAction u
  ≡ negativeStandardSU2WilsonAction (- (four * u))
standardSU2WilsonSameNegativeOrientation u =
  cong₂ T4.localizedAction (Ring.solve-∀ u) (Ring.solve-∀ u)

factorFourAbsorbedNegativeBasis : T4.LocalizedAction
factorFourAbsorbedNegativeBasis =
  T4.scaleLocalizedAction four negativeWilsonBasis

standardSU2WilsonSameRenormalizedUnitCoefficient :
  ∀ u →
  standardSU2WilsonAction u
  ≡ T4.scaleLocalizedAction (- u) factorFourAbsorbedNegativeBasis
standardSU2WilsonSameRenormalizedUnitCoefficient u =
  cong₂ T4.localizedAction (Ring.solve-∀ u) (Ring.solve-∀ u)

fourNormalizedBasisHasPlaquetteCoefficientMinusFour :
  T4.plaquetteCoefficientProjector factorFourAbsorbedNegativeBasis
  ≡ - four
fourNormalizedBasisHasPlaquetteCoefficientMinusFour =
  Ring.solve []
