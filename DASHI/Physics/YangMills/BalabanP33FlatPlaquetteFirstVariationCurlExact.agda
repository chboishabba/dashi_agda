module DASHI.Physics.YangMills.BalabanP33FlatPlaquetteFirstVariationCurlExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Prove the first-derivative companion to the existing flat Hessian identity.
-- The ordered first derivative of the four right-exponential flat link jets is
-- exactly the pure quaternion of the oriented plaquette curl.  In particular,
-- its scalar part vanishes, as required at the Wilson-action identity
-- background.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalPlaquetteFirstVariationExact as First
import DASHI.Physics.YangMills.BalabanP33PhysicalCovariantPlaquetteCurlExact as Curl
import DASHI.Physics.YangMills.BalabanP33CovariantCurlDefectFactorizationExact as Defect

flatOrientedPlaquetteFirstVariation :
  Q.RationalVector3 → Q.RationalVector3 →
  Q.RationalVector3 → Q.RationalVector3 →
  Q.RationalQuaternion
flatOrientedPlaquetteFirstVariation forward0 forward1 inverse2 inverse3 =
  Q.orderedFirstProduct
    (Q.flatOrientedPlaquetteJets forward0 forward1 inverse2 inverse3)

flatFirstVariationIsPureCurl :
  ∀ forward0 forward1 inverse2 inverse3 →
  flatOrientedPlaquetteFirstVariation
    forward0 forward1 inverse2 inverse3
  ≡ Q.pureQuaternion
      (Q.plaquetteCurlVector forward0 forward1 inverse2 inverse3)
flatFirstVariationIsPureCurl
    (Q.vec3 x0 y0 z0) (Q.vec3 x1 y1 z1)
    (Q.vec3 x2 y2 z2) (Q.vec3 x3 y3 z3) =
  Q.quaternionExt
    (ℚRing.solve-∀
      x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3)
    (ℚRing.solve-∀
      x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3)
    (ℚRing.solve-∀
      x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3)
    (ℚRing.solve-∀
      x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3)

flatFirstVariationScalarPartZero :
  ∀ forward0 forward1 inverse2 inverse3 →
  Q.q0
    (flatOrientedPlaquetteFirstVariation
      forward0 forward1 inverse2 inverse3)
  ≡ Q.q0 Q.zeroQ
flatFirstVariationScalarPartZero
    forward0 forward1 inverse2 inverse3 =
  trans
    (cong Q.q0
      (flatFirstVariationIsPureCurl
        forward0 forward1 inverse2 inverse3))
    (ℚRing.solve [])

physicalIdentityFirstVariationIsFlatCurl :
  ∀ field plaquette →
  First.plaquetteFirstVariation
    Physical.identityBackground field plaquette
  ≡ Defect.physicalFlatPlaquetteCurl field plaquette
physicalIdentityFirstVariationIsFlatCurl field plaquette =
  let
    x0 = Curl.physicalInsertion0 field plaquette
    x1 = Curl.physicalInsertion1 field plaquette
    x2 = Curl.physicalInsertion2 field plaquette
    x3 = Curl.physicalInsertion3 field plaquette
  in
  trans
    (Curl.physicalFirstVariationIsRightExponentialRaw
      Physical.identityBackground field plaquette)
    (Q.quaternionExt
      (ℚRing.solve-∀
        (Q.q0 x0) (Q.q1 x0) (Q.q2 x0) (Q.q3 x0)
        (Q.q0 x1) (Q.q1 x1) (Q.q2 x1) (Q.q3 x1)
        (Q.q0 x2) (Q.q1 x2) (Q.q2 x2) (Q.q3 x2)
        (Q.q0 x3) (Q.q1 x3) (Q.q2 x3) (Q.q3 x3))
      (ℚRing.solve-∀
        (Q.q0 x0) (Q.q1 x0) (Q.q2 x0) (Q.q3 x0)
        (Q.q0 x1) (Q.q1 x1) (Q.q2 x1) (Q.q3 x1)
        (Q.q0 x2) (Q.q1 x2) (Q.q2 x2) (Q.q3 x2)
        (Q.q0 x3) (Q.q1 x3) (Q.q2 x3) (Q.q3 x3))
      (ℚRing.solve-∀
        (Q.q0 x0) (Q.q1 x0) (Q.q2 x0) (Q.q3 x0)
        (Q.q0 x1) (Q.q1 x1) (Q.q2 x1) (Q.q3 x1)
        (Q.q0 x2) (Q.q1 x2) (Q.q2 x2) (Q.q3 x2)
        (Q.q0 x3) (Q.q1 x3) (Q.q2 x3) (Q.q3 x3))
      (ℚRing.solve-∀
        (Q.q0 x0) (Q.q1 x0) (Q.q2 x0) (Q.q3 x0)
        (Q.q0 x1) (Q.q1 x1) (Q.q2 x1) (Q.q3 x1)
        (Q.q0 x2) (Q.q1 x2) (Q.q2 x2) (Q.q3 x2)
        (Q.q0 x3) (Q.q1 x3) (Q.q2 x3) (Q.q3 x3)))

flatPlaquetteFirstVariationCurlLevel : ProofLevel
flatPlaquetteFirstVariationCurlLevel = machineChecked

physicalIdentityFirstVariationLevel : ProofLevel
physicalIdentityFirstVariationLevel = machineChecked
