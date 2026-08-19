module DASHI.Physics.YangMills.BalabanSU2OneLoopInfraredCoefficientFromLiteralScalarExact where

------------------------------------------------------------------------
-- ROUND65: THE FOUR-ORBIT REGULAR REMAINDER IS NOT beta_0
--
-- PRIMARY SOURCES
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- R. Dashen and D. J. Gross,
-- "Relationship between lattice and continuum definitions of the gauge-theory
-- coupling", Physical Review D 23 (1981), 2340--2348.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The literal scalar-reduction API already separates
--
--   scalarIntegrand = continuumSingular + regularIntegrand
--
-- and pins the coefficient of the singular logarithmic term to 11/24 before
-- the regular Brillouin remainder is intervalized.  The SU(2) colour factor is
-- C_A=2, so the coefficient multiplying 1/pi^2 in the inverse-coupling flow is
-- exactly
--
--   2 * 11/24 = 11/12.
--
-- Therefore the four-orbit Bishop computation controls the finite REGULAR
-- matching/remainder, not the universal asymptotic-freedom coefficient itself.
-- This file makes that distinction theorem-visible and removes "discover beta0
-- numerically from four representatives" from the hard frontier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Literal
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopConventionExact as Convention
import DASHI.Physics.YangMills.BalabanSU2OneLoopNormalizationSanityExact as Sanity

su2LiteralInfraredInverseCouplingCoefficient :
  ∀ {expressions ward}
    (scalarData : Literal.LiteralScalarIntegrandExpression expressions ward) → ℚ
su2LiteralInfraredInverseCouplingCoefficient scalarData =
  Convention.adjointCasimirSU2 * Literal.infraredCoefficient scalarData

su2LiteralInfraredCoefficientExact :
  ∀ {expressions ward}
    (scalarData : Literal.LiteralScalarIntegrandExpression expressions ward) →
  su2LiteralInfraredInverseCouplingCoefficient scalarData
  ≡ Sanity.su2InverseCouplingCoefficient
su2LiteralInfraredCoefficientExact scalarData =
  trans
    (cong
      (Convention.adjointCasimirSU2 *_)
      (Literal.infraredCoefficientExact scalarData))
    (ℚRing.solve [])

su2LiteralInfraredCoefficientIsElevenTwelfths :
  ∀ {expressions ward}
    (scalarData : Literal.LiteralScalarIntegrandExpression expressions ward) →
  su2LiteralInfraredInverseCouplingCoefficient scalarData ≡ (+ 11 / 12)
su2LiteralInfraredCoefficientIsElevenTwelfths = su2LiteralInfraredCoefficientExact

literalScalarReductionToUniversalBetaCoefficientLevel : ProofLevel
literalScalarReductionToUniversalBetaCoefficientLevel = machineChecked

-- Still physical: construct the literal Wilson/FP/Haar Ward scalar reduction
-- on the source carrier.  Once that same-object scalarData exists, beta0's sign
-- and normalization are no longer separate numerical producers.
literalWilsonGhostHaarWardScalarReductionLevel : ProofLevel
literalWilsonGhostHaarWardScalarReductionLevel = conditional

-- Separately physical: the four-orbit Bishop calculation bounds the finite
-- regular matching/remainder entering the full one-step coefficient.
literalFourOrbitRegularMatchingRemainderLevel : ProofLevel
literalFourOrbitRegularMatchingRemainderLevel = conditional
