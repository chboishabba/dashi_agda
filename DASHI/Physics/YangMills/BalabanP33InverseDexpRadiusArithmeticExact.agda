module DASHI.Physics.YangMills.BalabanP33InverseDexpRadiusArithmeticExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- Once the constructive Bernoulli coefficient satisfies beta(t) <= 1/6, the
-- concrete reduced SU(2) inverse-dexp estimate is
--
--   ||dexp_X^-1-I|| <= t/2 + t^2/6,  t = ||ad_X||.
--
-- At the literal P33 operator radius rho=1/8192 this envelope is
--
--   24577 / 402653184,
--
-- leaving the exact positive slack
--
--   24575 / 402653184
--
-- before rho.  This module performs that calibration with exact rationals.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

oneHalf oneSixth : ℚ
oneHalf = + 1 / 2
oneSixth = + 1 / 6

p33OperatorRadius : ℚ
p33OperatorRadius = + 1 / 8192

inverseDexpEnvelope : ℚ → ℚ
inverseDexpEnvelope t =
  oneHalf * t + oneSixth * t * t

inverseDexpEnvelopeAtRadius : ℚ
inverseDexpEnvelopeAtRadius = + 24577 / 402653184

inverseDexpEnvelopeSlack : ℚ
inverseDexpEnvelopeSlack = + 24575 / 402653184

inverseDexpEnvelopeValueExact :
  inverseDexpEnvelope p33OperatorRadius
  ≡ inverseDexpEnvelopeAtRadius
inverseDexpEnvelopeValueExact = ℚRing.solve []

inverseDexpEnvelopePlusSlackExact :
  inverseDexpEnvelope p33OperatorRadius
    + inverseDexpEnvelopeSlack
  ≡ p33OperatorRadius
inverseDexpEnvelopePlusSlackExact = ℚRing.solve []

inverseDexpEnvelopeSlackNonnegative :
  0ℚ ≤ inverseDexpEnvelopeSlack
inverseDexpEnvelopeSlackNonnegative =
  ℚP.nonNegative⁻¹ inverseDexpEnvelopeSlack

inverseDexpEnvelopeAtRadiusBelowRadius :
  inverseDexpEnvelope p33OperatorRadius ≤ p33OperatorRadius
inverseDexpEnvelopeAtRadiusBelowRadius =
  subst
    (λ upper → inverseDexpEnvelope p33OperatorRadius ≤ upper)
    inverseDexpEnvelopePlusSlackExact
    (subst
      (λ lower →
        lower
        ≤ inverseDexpEnvelope p33OperatorRadius
          + inverseDexpEnvelopeSlack)
      (sym (ℚP.+-identityʳ
        (inverseDexpEnvelope p33OperatorRadius)))
      (ℚP.+-mono-≤ ℚP.≤-refl
        inverseDexpEnvelopeSlackNonnegative))

p33InverseDexpRadiusCalibrationLevel : ProofLevel
p33InverseDexpRadiusCalibrationLevel = machineChecked

p33InverseDexpPositiveSlackLevel : ProofLevel
p33InverseDexpPositiveSlackLevel = machineChecked
