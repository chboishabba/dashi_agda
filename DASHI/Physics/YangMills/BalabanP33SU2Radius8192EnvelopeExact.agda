module DASHI.Physics.YangMills.BalabanP33SU2Radius8192EnvelopeExact where

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
-- Perform the exact rational small-radius arithmetic after fixing DASHI's
-- quaternion-commutator normalization gamma=2.  The operator target is
--
--   rho = 1/8192.
--
-- To obtain ||Ad(exp X)-I|| <= rho from the elementary envelope
--
--   t + t^2/2,
--
-- it is sufficient to have ||ad_X|| <= rho/2.  Since ||ad_X|| = 2||X|| in
-- the concrete normalization, this corresponds to the Lie-coordinate radius
-- 1/32768.  For the paired dexp/dexp^-1 envelope
--
--   t + t^2/3,
--
-- the full operator radius t <= rho remains below 2 rho with an explicit
-- positive rational slack.  These are closed rational calculations, not
-- floating-point diagnostics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

oneHalf oneThird two : ℚ
oneHalf = + 1 / 2
oneThird = + 1 / 3
two = + 2 / 1

p33OperatorRadius : ℚ
p33OperatorRadius = + 1 / 8192

p33HalfOperatorRadius : ℚ
p33HalfOperatorRadius = + 1 / 16384

p33GammaTwoLieCoordinateRadius : ℚ
p33GammaTwoLieCoordinateRadius = + 1 / 32768

halfOperatorRadiusExact :
  two * p33HalfOperatorRadius ≡ p33OperatorRadius
halfOperatorRadiusExact = ℚRing.solve []

gammaTwoCoordinateRadiusExact :
  two * p33GammaTwoLieCoordinateRadius ≡ p33HalfOperatorRadius
gammaTwoCoordinateRadiusExact = ℚRing.solve []

adTaylorEnvelope : ℚ → ℚ
adTaylorEnvelope t = t + oneHalf * t * t

dexpPairTaylorEnvelope : ℚ → ℚ
dexpPairTaylorEnvelope t = t + oneThird * t * t

adEnvelopeSlack : ℚ
adEnvelopeSlack = + 32767 / 536870912

dexpPairEnvelopeSlack : ℚ
dexpPairEnvelopeSlack = + 24575 / 201326592

adEnvelopePlusSlackExact :
  adTaylorEnvelope p33HalfOperatorRadius + adEnvelopeSlack
  ≡ p33OperatorRadius
adEnvelopePlusSlackExact = ℚRing.solve []

dexpPairEnvelopePlusSlackExact :
  dexpPairTaylorEnvelope p33OperatorRadius + dexpPairEnvelopeSlack
  ≡ two * p33OperatorRadius
dexpPairEnvelopePlusSlackExact = ℚRing.solve []

adEnvelopeSlackNonnegative : 0ℚ ≤ adEnvelopeSlack
adEnvelopeSlackNonnegative = ℚP.nonNegative⁻¹ adEnvelopeSlack

dexpPairEnvelopeSlackNonnegative : 0ℚ ≤ dexpPairEnvelopeSlack
dexpPairEnvelopeSlackNonnegative =
  ℚP.nonNegative⁻¹ dexpPairEnvelopeSlack

adEnvelopeAtHalfRadiusBelowConfiguredRadius :
  adTaylorEnvelope p33HalfOperatorRadius ≤ p33OperatorRadius
adEnvelopeAtHalfRadiusBelowConfiguredRadius =
  subst
    (λ upper → adTaylorEnvelope p33HalfOperatorRadius ≤ upper)
    adEnvelopePlusSlackExact
    (subst
      (λ lower →
        lower
        ≤ adTaylorEnvelope p33HalfOperatorRadius + adEnvelopeSlack)
      (sym (ℚP.+-identityʳ (adTaylorEnvelope p33HalfOperatorRadius)))
      (ℚP.+-mono-≤ ℚP.≤-refl adEnvelopeSlackNonnegative))

dexpPairEnvelopeAtRadiusBelowTwiceRadius :
  dexpPairTaylorEnvelope p33OperatorRadius
  ≤ two * p33OperatorRadius
dexpPairEnvelopeAtRadiusBelowTwiceRadius =
  subst
    (λ upper → dexpPairTaylorEnvelope p33OperatorRadius ≤ upper)
    dexpPairEnvelopePlusSlackExact
    (subst
      (λ lower →
        lower
        ≤ dexpPairTaylorEnvelope p33OperatorRadius
          + dexpPairEnvelopeSlack)
      (sym (ℚP.+-identityʳ
        (dexpPairTaylorEnvelope p33OperatorRadius)))
      (ℚP.+-mono-≤ ℚP.≤-refl
        dexpPairEnvelopeSlackNonnegative))

p33GammaTwoRadiusCalibrationLevel : ProofLevel
p33GammaTwoRadiusCalibrationLevel = machineChecked

p33AdjointTaylorEnvelopeArithmeticLevel : ProofLevel
p33AdjointTaylorEnvelopeArithmeticLevel = machineChecked

p33DexpPairTaylorEnvelopeArithmeticLevel : ProofLevel
p33DexpPairTaylorEnvelopeArithmeticLevel = machineChecked
