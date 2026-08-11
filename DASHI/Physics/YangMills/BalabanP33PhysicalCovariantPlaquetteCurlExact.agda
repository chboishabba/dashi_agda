module DASHI.Physics.YangMills.BalabanP33PhysicalCovariantPlaquetteCurlExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Right-trivialize the literal four-link first variation.  For the oriented
-- plaquette
--
--   P = A B C^-1 D^-1
--
-- and right-exponential insertions X0,...,X3, exact quaternion multiplication
-- gives
--
--   P' P^-1
--     = Ad_A X0 + Ad_{AB} X1
--       - Ad_{AB} X2 - Ad_{ABC^-1} X3.
--
-- The repeated `Ad_{AB}` is not a typo: differentiating C(t)^-1 on the left
-- gives `-X2 C^-1`.  The transport order is therefore derived from the actual
-- positive/inverse jets, rather than selected by analogy with a continuum
-- formula.  A norm-weighted polynomial theorem is first proved for arbitrary
-- rational quaternions; the unit-link hypotheses then remove every weight.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge4
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33PhysicalPlaquetteFirstVariationExact as First

scaleQ : ℚ → Q.RationalQuaternion → Q.RationalQuaternion
scaleQ scale (Q.quat q0 q1 q2 q3) =
  Q.quat (scale * q0) (scale * q1) (scale * q2) (scale * q3)

scaleOneExact : ∀ value → scaleQ 1ℚ value ≡ value
scaleOneExact (Q.quat q0 q1 q2 q3) =
  Q.quaternionExt
    (ℚRing.solve-∀ q0) (ℚRing.solve-∀ q1)
    (ℚRing.solve-∀ q2) (ℚRing.solve-∀ q3)

plaquetteProduct :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
plaquetteProduct a b c d =
  a Q.*q
    (b Q.*q
      (Physical.quaternionConjugate c Q.*q
        (Physical.quaternionConjugate d Q.*q Q.oneQ)))

plaquetteRightInverse :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
plaquetteRightInverse a b c d =
  d Q.*q
    (c Q.*q
      (Physical.quaternionConjugate b Q.*q
        (Physical.quaternionConjugate a Q.*q Q.oneQ)))

rightExponentialPlaquetteFirstVariation :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
rightExponentialPlaquetteFirstVariation a b c d x0 x1 x2 x3 =
  ((a Q.*q x0) Q.*q
      (b Q.*q
        (Physical.quaternionConjugate c Q.*q
          (Physical.quaternionConjugate d Q.*q Q.oneQ))))
  Q.+q
  ((a Q.*q
      ((b Q.*q x1) Q.*q
        (Physical.quaternionConjugate c Q.*q
          (Physical.quaternionConjugate d Q.*q Q.oneQ))))
  Q.+q
  ((a Q.*q
      (b Q.*q
        ((Q.negQ x2 Q.*q Physical.quaternionConjugate c) Q.*q
          (Physical.quaternionConjugate d Q.*q Q.oneQ))))
  Q.+q
  ((a Q.*q
      (b Q.*q
        (Physical.quaternionConjugate c Q.*q
          ((Q.negQ x3 Q.*q Physical.quaternionConjugate d)
            Q.*q Q.oneQ))))
  Q.+q Q.zeroQ)))

prefixAB : Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
prefixAB a b = a Q.*q b

prefixABCInverse :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
prefixABCInverse a b c =
  a Q.*q (b Q.*q Physical.quaternionConjugate c)

covariantPlaquetteCurl :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
covariantPlaquetteCurl a b c x0 x1 x2 x3 =
  Adjoint.adjointTransport a x0
  Q.+q
  (Adjoint.adjointTransport (prefixAB a b) x1
  Q.+q
  (Q.negQ (Adjoint.adjointTransport (prefixAB a b) x2)
  Q.+q
  (Q.negQ
    (Adjoint.adjointTransport (prefixABCInverse a b c) x3)
  Q.+q Q.zeroQ)))

weightedCovariantPlaquetteCurl :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
weightedCovariantPlaquetteCurl a b c d x0 x1 x2 x3 =
  scaleQ
    (Physical.quaternionNormSq b
      * Physical.quaternionNormSq c
      * Physical.quaternionNormSq d)
    (Adjoint.adjointTransport a x0)
  Q.+q
  (scaleQ
    (Physical.quaternionNormSq c * Physical.quaternionNormSq d)
    (Adjoint.adjointTransport (prefixAB a b) x1)
  Q.+q
  (Q.negQ
    (scaleQ
      (Physical.quaternionNormSq c * Physical.quaternionNormSq d)
      (Adjoint.adjointTransport (prefixAB a b) x2))
  Q.+q
  (Q.negQ
    (scaleQ
      (Physical.quaternionNormSq d)
      (Adjoint.adjointTransport (prefixABCInverse a b c) x3))
  Q.+q Q.zeroQ)))

rightTrivializedFirstVariationWithNormWeights :
  ∀ a b c d x0 x1 x2 x3 →
  rightExponentialPlaquetteFirstVariation a b c d x0 x1 x2 x3
    Q.*q plaquetteRightInverse a b c d
  ≡ weightedCovariantPlaquetteCurl a b c d x0 x1 x2 x3
rightTrivializedFirstVariationWithNormWeights
    (Q.quat a0 a1 a2 a3)
    (Q.quat b0 b1 b2 b3)
    (Q.quat c0 c1 c2 c3)
    (Q.quat d0 d1 d2 d3)
    (Q.quat x00 x01 x02 x03)
    (Q.quat x10 x11 x12 x13)
    (Q.quat x20 x21 x22 x23)
    (Q.quat x30 x31 x32 x33) =
  Q.quaternionExt
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3
      x00 x01 x02 x03 x10 x11 x12 x13
      x20 x21 x22 x23 x30 x31 x32 x33)
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3
      x00 x01 x02 x03 x10 x11 x12 x13
      x20 x21 x22 x23 x30 x31 x32 x33)
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3
      x00 x01 x02 x03 x10 x11 x12 x13
      x20 x21 x22 x23 x30 x31 x32 x33)
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3
      x00 x01 x02 x03 x10 x11 x12 x13
      x20 x21 x22 x23 x30 x31 x32 x33)

weightedCurlAtUnitNormExact :
  ∀ a b c d x0 x1 x2 x3 →
  Physical.quaternionNormSq b ≡ 1ℚ →
  Physical.quaternionNormSq c ≡ 1ℚ →
  Physical.quaternionNormSq d ≡ 1ℚ →
  weightedCovariantPlaquetteCurl a b c d x0 x1 x2 x3
  ≡ covariantPlaquetteCurl a b c x0 x1 x2 x3
weightedCurlAtUnitNormExact a b c d x0 x1 x2 x3 bUnit cUnit dUnit
  rewrite bUnit | cUnit | dUnit
        | scaleOneExact (Adjoint.adjointTransport a x0)
        | scaleOneExact (Adjoint.adjointTransport (prefixAB a b) x1)
        | scaleOneExact (Adjoint.adjointTransport (prefixAB a b) x2)
        | scaleOneExact
            (Adjoint.adjointTransport (prefixABCInverse a b c) x3) =
  refl

scalarQuaternion : ℚ → Q.RationalQuaternion
scalarQuaternion value = Q.quat value 0ℚ 0ℚ 0ℚ

plaquetteProductTimesRightInverseWithNorms :
  ∀ a b c d →
  plaquetteProduct a b c d Q.*q plaquetteRightInverse a b c d
  ≡ scalarQuaternion
      (Physical.quaternionNormSq a
        * Physical.quaternionNormSq b
        * Physical.quaternionNormSq c
        * Physical.quaternionNormSq d)
plaquetteProductTimesRightInverseWithNorms
    (Q.quat a0 a1 a2 a3)
    (Q.quat b0 b1 b2 b3)
    (Q.quat c0 c1 c2 c3)
    (Q.quat d0 d1 d2 d3) =
  Q.quaternionExt
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3
      c0 c1 c2 c3 d0 d1 d2 d3)
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3
      c0 c1 c2 c3 d0 d1 d2 d3)
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3
      c0 c1 c2 c3 d0 d1 d2 d3)
    (ℚRing.solve-∀
      a0 a1 a2 a3 b0 b1 b2 b3
      c0 c1 c2 c3 d0 d1 d2 d3)

------------------------------------------------------------------------
-- Literal side-four physical instantiation.
------------------------------------------------------------------------

physicalFactorA :
  Physical.RationalSU2Background4 → Physical.Plaquette4 →
  Q.RationalQuaternion
physicalFactorA background (pair site axes) =
  Physical.link background (pair site (Physical.pairLeft axes))

physicalFactorB :
  Physical.RationalSU2Background4 → Physical.Plaquette4 →
  Q.RationalQuaternion
physicalFactorB background (pair site axes) =
  Physical.link background
    (pair (Hodge4.shiftForward (Physical.pairLeft axes) site)
      (Physical.pairRight axes))

physicalPositiveFactorC :
  Physical.RationalSU2Background4 → Physical.Plaquette4 →
  Q.RationalQuaternion
physicalPositiveFactorC background (pair site axes) =
  Physical.link background
    (pair (Hodge4.shiftForward (Physical.pairRight axes) site)
      (Physical.pairLeft axes))

physicalPositiveFactorD :
  Physical.RationalSU2Background4 → Physical.Plaquette4 →
  Q.RationalQuaternion
physicalPositiveFactorD background (pair site axes) =
  Physical.link background (pair site (Physical.pairRight axes))

physicalInsertion0 :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Q.RationalQuaternion
physicalInsertion0 field (pair site axes) =
  Q.pureQuaternion
    (Physical.insertionAt field (Physical.pairLeft axes) site)

physicalInsertion1 :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Q.RationalQuaternion
physicalInsertion1 field (pair site axes) =
  Q.pureQuaternion
    (Physical.insertionAt field (Physical.pairRight axes)
      (Hodge4.shiftForward (Physical.pairLeft axes) site))

physicalInsertion2 :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Q.RationalQuaternion
physicalInsertion2 field (pair site axes) =
  Q.pureQuaternion
    (Physical.insertionAt field (Physical.pairLeft axes)
      (Hodge4.shiftForward (Physical.pairRight axes) site))

physicalInsertion3 :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Q.RationalQuaternion
physicalInsertion3 field (pair site axes) =
  Q.pureQuaternion
    (Physical.insertionAt field (Physical.pairRight axes) site)

physicalPlaquetteFirstVariationRaw :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Q.RationalQuaternion
physicalPlaquetteFirstVariationRaw background field plaquette =
  rightExponentialPlaquetteFirstVariation
    (physicalFactorA background plaquette)
    (physicalFactorB background plaquette)
    (physicalPositiveFactorC background plaquette)
    (physicalPositiveFactorD background plaquette)
    (physicalInsertion0 field plaquette)
    (physicalInsertion1 field plaquette)
    (physicalInsertion2 field plaquette)
    (physicalInsertion3 field plaquette)

physicalPlaquetteRightInverse :
  Physical.RationalSU2Background4 → Physical.Plaquette4 →
  Q.RationalQuaternion
physicalPlaquetteRightInverse background plaquette =
  plaquetteRightInverse
    (physicalFactorA background plaquette)
    (physicalFactorB background plaquette)
    (physicalPositiveFactorC background plaquette)
    (physicalPositiveFactorD background plaquette)

physicalCovariantPlaquetteCurl :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Q.RationalQuaternion
physicalCovariantPlaquetteCurl background field plaquette =
  covariantPlaquetteCurl
    (physicalFactorA background plaquette)
    (physicalFactorB background plaquette)
    (physicalPositiveFactorC background plaquette)
    (physicalInsertion0 field plaquette)
    (physicalInsertion1 field plaquette)
    (physicalInsertion2 field plaquette)
    (physicalInsertion3 field plaquette)

physicalFirstVariationIsRightExponentialRaw :
  ∀ background field plaquette →
  First.plaquetteFirstVariation background field plaquette
  ≡ physicalPlaquetteFirstVariationRaw background field plaquette
physicalFirstVariationIsRightExponentialRaw background field (pair site axes) =
  trans
    (First.plaquetteFirstVariationIsFourOrderedSum
      background field (pair site axes))
    refl

physicalPlaquetteRightInverseExact :
  ∀ background plaquette →
  plaquetteProduct
    (physicalFactorA background plaquette)
    (physicalFactorB background plaquette)
    (physicalPositiveFactorC background plaquette)
    (physicalPositiveFactorD background plaquette)
    Q.*q physicalPlaquetteRightInverse background plaquette
  ≡ Q.oneQ
physicalPlaquetteRightInverseExact background plaquette@(pair site axes) =
  let
    a = physicalFactorA background plaquette
    b = physicalFactorB background plaquette
    c = physicalPositiveFactorC background plaquette
    d = physicalPositiveFactorD background plaquette

    productNormExact :
      Physical.quaternionNormSq a
        * Physical.quaternionNormSq b
        * Physical.quaternionNormSq c
        * Physical.quaternionNormSq d
      ≡ 1ℚ
    productNormExact
      rewrite Physical.unitNorm background
          (pair site (Physical.pairLeft axes))
        | Physical.unitNorm background
          (pair (Hodge4.shiftForward (Physical.pairLeft axes) site)
            (Physical.pairRight axes))
        | Physical.unitNorm background
          (pair (Hodge4.shiftForward (Physical.pairRight axes) site)
            (Physical.pairLeft axes))
        | Physical.unitNorm background
          (pair site (Physical.pairRight axes)) =
      ℚRing.solve []
  in
  trans
    (plaquetteProductTimesRightInverseWithNorms a b c d)
    (cong scalarQuaternion productNormExact)

physicalPlaquetteFirstVariationIsCovariantCurl :
  ∀ background field plaquette →
  First.plaquetteFirstVariation background field plaquette
    Q.*q physicalPlaquetteRightInverse background plaquette
  ≡ physicalCovariantPlaquetteCurl background field plaquette
physicalPlaquetteFirstVariationIsCovariantCurl
    background field plaquette@(pair site axes) =
  let
    a = physicalFactorA background plaquette
    b = physicalFactorB background plaquette
    c = physicalPositiveFactorC background plaquette
    d = physicalPositiveFactorD background plaquette
    x0 = physicalInsertion0 field plaquette
    x1 = physicalInsertion1 field plaquette
    x2 = physicalInsertion2 field plaquette
    x3 = physicalInsertion3 field plaquette

    actualToRaw :
      First.plaquetteFirstVariation background field plaquette
        Q.*q physicalPlaquetteRightInverse background plaquette
      ≡ rightExponentialPlaquetteFirstVariation a b c d x0 x1 x2 x3
          Q.*q plaquetteRightInverse a b c d
    actualToRaw =
      cong
        (λ selected → selected Q.*q plaquetteRightInverse a b c d)
        (physicalFirstVariationIsRightExponentialRaw
          background field plaquette)

    rawToWeighted =
      rightTrivializedFirstVariationWithNormWeights
        a b c d x0 x1 x2 x3

    weightedToCurl =
      weightedCurlAtUnitNormExact a b c d x0 x1 x2 x3
        (Physical.unitNorm background
          (pair (Hodge4.shiftForward (Physical.pairLeft axes) site)
            (Physical.pairRight axes)))
        (Physical.unitNorm background
          (pair (Hodge4.shiftForward (Physical.pairRight axes) site)
            (Physical.pairLeft axes)))
        (Physical.unitNorm background
          (pair site (Physical.pairRight axes)))
  in
  trans actualToRaw (trans rawToWeighted weightedToCurl)

physicalPlaquetteCovariantCurlLevel : ProofLevel
physicalPlaquetteCovariantCurlLevel = machineChecked

physicalPlaquetteTransportOrderLevel : ProofLevel
physicalPlaquetteTransportOrderLevel = machineChecked
