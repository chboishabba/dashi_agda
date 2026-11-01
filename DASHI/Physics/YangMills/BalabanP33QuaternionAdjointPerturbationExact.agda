module DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Expose the exact algebra behind the gauge-background perturbation:
--
--   U X U^-1 - X
--     = (U-1) X U^-1 + X (U^-1-1).
--
-- For the rational SU(2) carrier U^-1 is quaternion conjugation.  The theorem
-- is then specialized to the repository's literal physical background link.
-- Consequently the later gauge estimate has two concrete link-defect terms;
-- it cannot insert an anonymous adjoint-transport error.
--
-- This module proves the factorization and conjugation identities only.  The
-- quantitative norm estimate
--
--   ||Ad_U X-X|| <= 2 ||U-1|| ||X||
--
-- still requires the ordered rational quaternion norm triangle and
-- submultiplicativity lemmas.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (PositiveBond)
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope

adjointTransport :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
adjointTransport unit value =
  unit Q.*q (value Q.*q Physical.quaternionConjugate unit)

adjointDefect :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
adjointDefect unit value =
  Telescope._-q_ (adjointTransport unit value) value

adjointDefectFactorization :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
adjointDefectFactorization unit value =
  ((Telescope._-q_ unit Q.oneQ) Q.*q
      (value Q.*q Physical.quaternionConjugate unit))
  Q.+q
  (value Q.*q
    (Telescope._-q_
      (Physical.quaternionConjugate unit) Q.oneQ))

adjointDefectFactorizationExact : ∀ unit value →
  adjointDefect unit value ≡ adjointDefectFactorization unit value
adjointDefectFactorizationExact
    (Q.quat u0 u1 u2 u3)
    (Q.quat x0 x1 x2 x3) =
  Q.quaternionExt
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)

conjugateDifferenceFromIdentityExact : ∀ unit →
  Telescope._-q_ (Physical.quaternionConjugate unit) Q.oneQ
  ≡ Physical.quaternionConjugate
      (Telescope._-q_ unit Q.oneQ)
conjugateDifferenceFromIdentityExact (Q.quat u0 u1 u2 u3) =
  Q.quaternionExt
    (ℚRing.solve-∀ u0)
    (ℚRing.solve-∀ u1)
    (ℚRing.solve-∀ u2)
    (ℚRing.solve-∀ u3)

conjugateNormSqExact : ∀ value →
  Physical.quaternionNormSq (Physical.quaternionConjugate value)
  ≡ Physical.quaternionNormSq value
conjugateNormSqExact (Q.quat x0 x1 x2 x3) =
  ℚRing.solve-∀ x0 x1 x2 x3

physicalLinkAdjointTransport :
  Physical.RationalSU2Background4 →
  PositiveBond Path4.side4 →
  Q.RationalQuaternion →
  Q.RationalQuaternion
physicalLinkAdjointTransport background bond value =
  Physical.link background bond Q.*q
    (value Q.*q Physical.inverseLink background bond)

physicalLinkAdjointDefect :
  Physical.RationalSU2Background4 →
  PositiveBond Path4.side4 →
  Q.RationalQuaternion →
  Q.RationalQuaternion
physicalLinkAdjointDefect background bond value =
  Telescope._-q_
    (physicalLinkAdjointTransport background bond value)
    value

physicalLinkAdjointDefectFactorizationExact :
  ∀ background bond value →
  physicalLinkAdjointDefect background bond value
  ≡
  ((Telescope._-q_ (Physical.link background bond) Q.oneQ) Q.*q
      (value Q.*q Physical.inverseLink background bond))
  Q.+q
  (value Q.*q
    (Telescope._-q_ (Physical.inverseLink background bond) Q.oneQ))
physicalLinkAdjointDefectFactorizationExact background bond value =
  adjointDefectFactorizationExact (Physical.link background bond) value

quaternionAdjointDefectFactorizationLevel : ProofLevel
quaternionAdjointDefectFactorizationLevel = machineChecked

physicalGaugeAdjointNormEstimateLevel : ProofLevel
physicalGaugeAdjointNormEstimateLevel = conditional
