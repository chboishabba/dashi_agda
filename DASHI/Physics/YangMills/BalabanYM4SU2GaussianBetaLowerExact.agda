module DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Dashen and David J. Gross,
-- "Relationship between Lattice and Continuum Definitions of the Gauge-Theory
-- Coupling", Physical Review D 23 (1981), 2340--2344.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Extract an explicit finite-lattice lower bound for the Gaussian beta piece
-- in the repository's SU(2) convention.  C_A=2 turns the universal inverse-
-- coupling coefficient (11 C_A)/24 into 11/12.  Hence any certified lower
-- bound ell_* on the normalized lattice log step gives
--
--       beta_Z >= (11/12) ell_*.
--
-- This separates the genuinely finite Brillouin/log certificate from the
-- group-theory coefficient, which is exact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

su2Casimir gaussianSU2Coefficient : ℚ
su2Casimir = + 2 / 1
gaussianSU2Coefficient = + 11 / 12

su2InverseCouplingCoefficientExact :
  Beta.pureYMInverseCouplingCoefficient su2Casimir ≡ gaussianSU2Coefficient
su2InverseCouplingCoefficientExact = ℚRing.solve []

record SU2GaussianStepCertificate {Scale : Set}
    (oneLoop : Plaquette.OneLoopVacuumPolarizationData Scale)
    (scale : Scale) : Set where
  field
    casimirIsSU2 : Plaquette.casimirAdjoint oneLoop ≡ su2Casimir
    logFloor : ℚ
    logFloorNonnegative : 0ℚ ≤ logFloor
    logStepNonnegative : 0ℚ ≤ Plaquette.logBlocking oneLoop scale
    logFloorBelowStep : logFloor ≤ Plaquette.logBlocking oneLoop scale

open SU2GaussianStepCertificate public

literalGaussianIsElevenTwelfthsTimesLog :
  ∀ {Scale} {oneLoop : Plaquette.OneLoopVacuumPolarizationData Scale} {scale}
    (certificate : SU2GaussianStepCertificate oneLoop scale) →
  Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop scale
  ≡ gaussianSU2Coefficient * Plaquette.logBlocking oneLoop scale
literalGaussianIsElevenTwelfthsTimesLog {oneLoop = oneLoop} {scale = scale} certificate =
  trans
    (cong
      (λ c → Beta.pureYMInverseCouplingCoefficient c
        * Plaquette.logBlocking oneLoop scale)
      (casimirIsSU2 certificate))
    (cong
      (λ coefficient → coefficient * Plaquette.logBlocking oneLoop scale)
      su2InverseCouplingCoefficientExact)

su2GaussianFiniteLatticeLower :
  ∀ {Scale} {oneLoop : Plaquette.OneLoopVacuumPolarizationData Scale} {scale}
    (certificate : SU2GaussianStepCertificate oneLoop scale) →
  gaussianSU2Coefficient * logFloor certificate
  ≤ Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop scale
su2GaussianFiniteLatticeLower {oneLoop = oneLoop} {scale = scale} certificate =
  let
    scaled = Norm.scaleNonnegative gaussianSU2Coefficient
      (ℚP.nonNegative⁻¹ gaussianSU2Coefficient)
      (logFloorBelowStep certificate)
  in
  subst
    (λ upper → gaussianSU2Coefficient * logFloor certificate ≤ upper)
    (literalGaussianIsElevenTwelfthsTimesLog certificate)
    scaled

su2GaussianLowerNonnegative :
  ∀ {Scale} {oneLoop : Plaquette.OneLoopVacuumPolarizationData Scale} {scale}
    (certificate : SU2GaussianStepCertificate oneLoop scale) →
  0ℚ ≤ gaussianSU2Coefficient * logFloor certificate
su2GaussianLowerNonnegative certificate =
  ℚP.*-mono-≤
    (ℚP.nonNegative⁻¹ gaussianSU2Coefficient)
    (logFloorNonnegative certificate)
    ℚP.≤-refl ℚP.≤-refl

ym4SU2GaussianCoefficientExactLevel : ProofLevel
ym4SU2GaussianCoefficientExactLevel = machineChecked

ym4SU2GaussianFiniteLatticeLowerLevel : ProofLevel
ym4SU2GaussianFiniteLatticeLowerLevel = machineChecked
