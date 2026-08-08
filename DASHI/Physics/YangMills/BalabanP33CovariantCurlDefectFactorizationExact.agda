module DASHI.Physics.YangMills.BalabanP33CovariantCurlDefectFactorizationExact where

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
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Subtract the flat oriented curl from the right-trivialized physical curl and
-- prove that the result is exactly the signed sum of four adjoint-transport
-- defects.  Each defect is then replaced by the already checked factorization
--
--   Ad_U X - X
--     = (U-1) X U^-1 + X (U^-1-1).
--
-- This is the algebraic input needed for a sharp correlated estimate.  It
-- exposes where the selected-background equation must improve on independent
-- link-radius bounds: the prefixes A, AB and ABC^-1 are shared across slots.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33PhysicalCovariantPlaquetteCurlExact as Curl
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates

flatOrientedPlaquetteCurl :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
flatOrientedPlaquetteCurl x0 x1 x2 x3 =
  x0 Q.+q
  (x1 Q.+q
  (Q.negQ x2 Q.+q
  (Q.negQ x3 Q.+q Q.zeroQ)))

covariantCurlDefect :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
covariantCurlDefect a b c x0 x1 x2 x3 =
  Telescope._-q_
    (Curl.covariantPlaquetteCurl a b c x0 x1 x2 x3)
    (flatOrientedPlaquetteCurl x0 x1 x2 x3)

adjointDefectCurlSum :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
adjointDefectCurlSum a b c x0 x1 x2 x3 =
  Adjoint.adjointDefect a x0
  Q.+q
  (Adjoint.adjointDefect (Curl.prefixAB a b) x1
  Q.+q
  (Q.negQ (Adjoint.adjointDefect (Curl.prefixAB a b) x2)
  Q.+q
  (Q.negQ
    (Adjoint.adjointDefect (Curl.prefixABCInverse a b c) x3)
  Q.+q Q.zeroQ)))

covariantCurlDefectIsAdjointDefectSum :
  ∀ a b c x0 x1 x2 x3 →
  covariantCurlDefect a b c x0 x1 x2 x3
  ≡ adjointDefectCurlSum a b c x0 x1 x2 x3
covariantCurlDefectIsAdjointDefectSum
    (Q.quat a0 a1 a2 a3)
    (Q.quat b0 b1 b2 b3)
    (Q.quat c0 c1 c2 c3)
    (Q.quat x00 x01 x02 x03)
    (Q.quat x10 x11 x12 x13)
    (Q.quat x20 x21 x22 x23)
    (Q.quat x30 x31 x32 x33) =
  Q.quaternionExt
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      x00 x01 x02 x03 x10 x11 x12 x13
      x20 x21 x22 x23 x30 x31 x32 x33)
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      x00 x01 x02 x03 x10 x11 x12 x13
      x20 x21 x22 x23 x30 x31 x32 x33)
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      x00 x01 x02 x03 x10 x11 x12 x13
      x20 x21 x22 x23 x30 x31 x32 x33)
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      x00 x01 x02 x03 x10 x11 x12 x13
      x20 x21 x22 x23 x30 x31 x32 x33)

factorizedAdjointDefectCurlSum :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
factorizedAdjointDefectCurlSum a b c x0 x1 x2 x3 =
  Adjoint.adjointDefectFactorization a x0
  Q.+q
  (Adjoint.adjointDefectFactorization (Curl.prefixAB a b) x1
  Q.+q
  (Q.negQ
    (Adjoint.adjointDefectFactorization (Curl.prefixAB a b) x2)
  Q.+q
  (Q.negQ
    (Adjoint.adjointDefectFactorization
      (Curl.prefixABCInverse a b c) x3)
  Q.+q Q.zeroQ)))

adjointDefectCurlSumFactorizes :
  ∀ a b c x0 x1 x2 x3 →
  adjointDefectCurlSum a b c x0 x1 x2 x3
  ≡ factorizedAdjointDefectCurlSum a b c x0 x1 x2 x3
adjointDefectCurlSumFactorizes a b c x0 x1 x2 x3
  rewrite Adjoint.adjointDefectFactorizationExact a x0
        | Adjoint.adjointDefectFactorizationExact (Curl.prefixAB a b) x1
        | Adjoint.adjointDefectFactorizationExact (Curl.prefixAB a b) x2
        | Adjoint.adjointDefectFactorizationExact
            (Curl.prefixABCInverse a b c) x3 =
  refl

covariantCurlDefectFactorizationExact :
  ∀ a b c x0 x1 x2 x3 →
  covariantCurlDefect a b c x0 x1 x2 x3
  ≡ factorizedAdjointDefectCurlSum a b c x0 x1 x2 x3
covariantCurlDefectFactorizationExact a b c x0 x1 x2 x3 =
  trans
    (covariantCurlDefectIsAdjointDefectSum a b c x0 x1 x2 x3)
    (adjointDefectCurlSumFactorizes a b c x0 x1 x2 x3)

physicalFlatPlaquetteCurl :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Q.RationalQuaternion
physicalFlatPlaquetteCurl field plaquette =
  flatOrientedPlaquetteCurl
    (Curl.physicalInsertion0 field plaquette)
    (Curl.physicalInsertion1 field plaquette)
    (Curl.physicalInsertion2 field plaquette)
    (Curl.physicalInsertion3 field plaquette)

physicalCovariantCurlDefect :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Q.RationalQuaternion
physicalCovariantCurlDefect background field plaquette =
  Telescope._-q_
    (Curl.physicalCovariantPlaquetteCurl background field plaquette)
    (physicalFlatPlaquetteCurl field plaquette)

physicalCovariantCurlDefectFactorizationExact :
  ∀ background field plaquette →
  physicalCovariantCurlDefect background field plaquette
  ≡ factorizedAdjointDefectCurlSum
      (Curl.physicalFactorA background plaquette)
      (Curl.physicalFactorB background plaquette)
      (Curl.physicalPositiveFactorC background plaquette)
      (Curl.physicalInsertion0 field plaquette)
      (Curl.physicalInsertion1 field plaquette)
      (Curl.physicalInsertion2 field plaquette)
      (Curl.physicalInsertion3 field plaquette)
physicalCovariantCurlDefectFactorizationExact background field plaquette =
  covariantCurlDefectFactorizationExact
    (Curl.physicalFactorA background plaquette)
    (Curl.physicalFactorB background plaquette)
    (Curl.physicalPositiveFactorC background plaquette)
    (Curl.physicalInsertion0 field plaquette)
    (Curl.physicalInsertion1 field plaquette)
    (Curl.physicalInsertion2 field plaquette)
    (Curl.physicalInsertion3 field plaquette)

covariantCurlDefectFactorizationLevel : ProofLevel
covariantCurlDefectFactorizationLevel = machineChecked

physicalCorrelatedCurvatureEstimateLevel : ProofLevel
physicalCorrelatedCurvatureEstimateLevel = conditional
