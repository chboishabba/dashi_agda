module DASHI.Physics.YangMills.BalabanSelectedGaugeRedundancyHolonomyGuardExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Falsify a tempting but incorrect shortcut in the reduced-multiplier lane.
-- At the identity background the constant gauge multipliers are zero modes of
-- the adjoint divergence.  They cannot simply be declared to remain zero
-- modes for every nearby covariant background: a non-central holonomy rotates
-- a constant Lie-algebra direction.
--
-- The counterexample is not a large-field artefact.  Using the rational
-- Cayley/Pythagorean parametrisation
--
--   U(t) = ((1-t^2)/(1+t^2), 2t/(1+t^2), 0, 0),
--
-- at t = rho = 1/8192, U(t) is an exact rational unit quaternion and lies
-- inside the repository's relaxed inverse-link radius.  Nevertheless its
-- adjoint action moves the y Lie direction.  Hence a background-uniform
-- reduced carrier must be proved from the actual holonomy/redundancy fibre;
-- it cannot be obtained by deleting the three flat constant rows once and for
-- all.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open ℚP using (_≤?_; _<?_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Nullary.Negation.Core using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeSignedLowerExact as Signed
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

cayleyDenominator : ℚ
cayleyDenominator = 1ℚ + Signed.rho * Signed.rho

nearIdentityScalar : ℚ
nearIdentityScalar =
  (1ℚ - Signed.rho * Signed.rho) / cayleyDenominator

nearIdentityX : ℚ
nearIdentityX =
  ((+ 2 / 1) * Signed.rho) / cayleyDenominator

nearIdentityUnit : Q.RationalQuaternion
nearIdentityUnit = Q.quat nearIdentityScalar nearIdentityX 0ℚ 0ℚ

nearIdentityUnitNormExact :
  Physical.quaternionNormSq nearIdentityUnit ≡ 1ℚ
nearIdentityUnitNormExact = ℚRing.solve []

nearIdentityInverseDefect : Q.RationalQuaternion
nearIdentityInverseDefect =
  Telescope._-q_ (Physical.quaternionConjugate nearIdentityUnit) Q.oneQ

nearIdentityInsideRelaxedRadius :
  Norm.normSq nearIdentityInverseDefect ≤ Relaxed.fourRhoSquare
nearIdentityInsideRelaxedRadius =
  toWitness
    {a? = Norm.normSq nearIdentityInverseDefect ≤? Relaxed.fourRhoSquare} _

yDirection : Q.RationalQuaternion
yDirection = Q.quat 0ℚ 0ℚ 1ℚ 0ℚ

rotatedY : Q.RationalQuaternion
rotatedY = Adjoint.adjointTransport nearIdentityUnit yDirection

rotatedYQ3Exact :
  Q.q3 rotatedY
  ≡ ((+ 4 / 1) * Signed.rho
      * (1ℚ - Signed.rho * Signed.rho))
      / (cayleyDenominator * cayleyDenominator)
rotatedYQ3Exact = ℚRing.solve []

rotatedYQ3Positive : 0ℚ < Q.q3 rotatedY
rotatedYQ3Positive =
  subst
    (λ value → 0ℚ < value)
    (sym rotatedYQ3Exact)
    (toWitness
      {a? = 0ℚ <?
        (((+ 4 / 1) * Signed.rho
          * (1ℚ - Signed.rho * Signed.rho))
          / (cayleyDenominator * cayleyDenominator))} _)

nearIdentityHolonomyMovesY : ¬ (rotatedY ≡ yDirection)
nearIdentityHolonomyMovesY equality =
  let
    q3Equality : Q.q3 rotatedY ≡ 0ℚ
    q3Equality = cong Q.q3 equality

    impossible : 0ℚ < 0ℚ
    impossible =
      subst (λ value → 0ℚ < value) q3Equality rotatedYQ3Positive
  in
  ℚP.<-irrefl 0ℚ impossible

constantCovariantDifference : Q.RationalQuaternion
constantCovariantDifference =
  Telescope._-q_ yDirection rotatedY

constantCovariantDifferenceQ3Negative :
  Q.q3 constantCovariantDifference < 0ℚ
constantCovariantDifferenceQ3Negative =
  subst
    (λ value → value < 0ℚ)
    (ℚRing.solve-∀ (Q.q3 rotatedY))
    (ℚP.neg-mono-< rotatedYQ3Positive)

flatConstantRedundancyNotAutomaticallyTransported :
  ¬ (Adjoint.adjointTransport nearIdentityUnit yDirection ≡ yDirection)
flatConstantRedundancyNotAutomaticallyTransported = nearIdentityHolonomyMovesY

selectedGaugeHolonomyGuardLevel : ProofLevel
selectedGaugeHolonomyGuardLevel = machineChecked
