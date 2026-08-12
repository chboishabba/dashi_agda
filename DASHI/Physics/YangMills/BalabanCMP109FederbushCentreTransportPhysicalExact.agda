module DASHI.Physics.YangMills.BalabanCMP109FederbushCentreTransportPhysicalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Identify the centre-transport T_j in the differentiated Federbush equation
-- with the literal adjoint of the relative product W_j = U_j V^-1.  For left
-- trivialized tangents,
--
--   d(U V^-1) (U V^-1)^-1 = u - Ad_{U V^-1} v,
--
-- so T = Ad_W; it is not an independently supplied 3x3 matrix.
--
-- The module also proves the two-background square-root-free estimate.  For
-- unit U,U',V,V',
--
--   N(W-W') <= 2 ( N(U-U') + N(V-V') ),
--
-- and therefore
--
--   N((T-T')X)
--     <= 8 ( N(U-U') + N(V-V') ) N(X).
--
-- This is the physical transport modulus upstream of the Lie-3 column-mass
-- projection.  It preserves the source ordering U V^-1 exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (_+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Four
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanCMP109QuaternionAdjointTwoBackgroundExact as TwoAd

relativeProduct : Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
relativeProduct input centre = input Q.*q Physical.quaternionConjugate centre

centreTransportAction :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
centreTransportAction input centre value =
  Adjoint.adjointTransport (relativeProduct input centre) value

relativeProductDifferenceFactorization :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
relativeProductDifferenceFactorization u v u' v' =
  ((Four._-q_ u u') Q.*q Physical.quaternionConjugate v)
  Q.+q
  (u' Q.*q
    (Four._-q_
      (Physical.quaternionConjugate v)
      (Physical.quaternionConjugate v')))

relativeProductDifferenceFactorizationExact : ∀ u v u' v' →
  Four._-q_ (relativeProduct u v) (relativeProduct u' v')
  ≡ relativeProductDifferenceFactorization u v u' v'
relativeProductDifferenceFactorizationExact
    (Q.quat u0 u1 u2 u3)
    (Q.quat v0 v1 v2 v3)
    (Q.quat p0 p1 p2 p3)
    (Q.quat q0 q1 q2 q3) =
  Q.quaternionExt
    (ℚRing.solve-∀ u0 u1 u2 u3 v0 v1 v2 v3 p0 p1 p2 p3 q0 q1 q2 q3)
    (ℚRing.solve-∀ u0 u1 u2 u3 v0 v1 v2 v3 p0 p1 p2 p3 q0 q1 q2 q3)
    (ℚRing.solve-∀ u0 u1 u2 u3 v0 v1 v2 v3 p0 p1 p2 p3 q0 q1 q2 q3)
    (ℚRing.solve-∀ u0 u1 u2 u3 v0 v1 v2 v3 p0 p1 p2 p3 q0 q1 q2 q3)

relativeProductUnit : ∀ input centre →
  Norm.normSq input ≡ + 1 / 1 →
  Norm.normSq centre ≡ + 1 / 1 →
  Norm.normSq (relativeProduct input centre) ≡ + 1 / 1
relativeProductUnit input centre inputUnit centreUnit
  rewrite Norm.normSqMultiplyExact input (Physical.quaternionConjugate centre)
        | Norm.normSqConjugateExact centre
        | inputUnit | centreUnit =
  ℚRing.solve []

relativeProductDifferenceNormSqBound : ∀ u v u' v' →
  Norm.normSq v ≡ + 1 / 1 →
  Norm.normSq u' ≡ + 1 / 1 →
  Norm.normSq
    (Four._-q_ (relativeProduct u v) (relativeProduct u' v'))
  ≤ (+ 2 / 1)
      * (Norm.normSq (Four._-q_ u u')
        + Norm.normSq (Four._-q_ v v'))
relativeProductDifferenceNormSqBound u v u' v' vUnit u'Unit =
  let
    left = (Four._-q_ u u') Q.*q Physical.quaternionConjugate v
    right = u' Q.*q
      (Four._-q_
        (Physical.quaternionConjugate v)
        (Physical.quaternionConjugate v'))

    leftNorm : Norm.normSq left ≡ Norm.normSq (Four._-q_ u u')
    leftNorm
      rewrite Norm.normSqMultiplyExact
        (Four._-q_ u u') (Physical.quaternionConjugate v)
        | Norm.normSqConjugateExact v | vUnit =
      ℚRing.solve-∀ (Norm.normSq (Four._-q_ u u'))

    rightNorm : Norm.normSq right ≡ Norm.normSq (Four._-q_ v v')
    rightNorm
      rewrite Norm.normSqMultiplyExact u'
        (Four._-q_
          (Physical.quaternionConjugate v)
          (Physical.quaternionConjugate v'))
        | TwoAd.conjugateDifferenceNormSqExact v v'
        | u'Unit =
      ℚRing.solve-∀ (Norm.normSq (Four._-q_ v v'))

    additive = Norm.normSqAddBound left right
    factorized :
      Norm.normSq (relativeProductDifferenceFactorization u v u' v')
      ≤ (+ 2 / 1)
          * (Norm.normSq (Four._-q_ u u')
            + Norm.normSq (Four._-q_ v v'))
    factorized =
      subst
        (λ middle → Norm.normSq (left Q.+q right) ≤ (+ 2 / 1) * middle)
        (cong₂ _+_ leftNorm rightNorm)
        additive
  in
  subst
    (λ lower →
      Norm.normSq lower
      ≤ (+ 2 / 1)
          * (Norm.normSq (Four._-q_ u u')
            + Norm.normSq (Four._-q_ v v')))
    (sym (relativeProductDifferenceFactorizationExact u v u' v'))
    factorized

centreTransportDifferenceNormSqBound : ∀ u v u' v' value →
  Norm.normSq u ≡ + 1 / 1 →
  Norm.normSq v ≡ + 1 / 1 →
  Norm.normSq u' ≡ + 1 / 1 →
  Norm.normSq v' ≡ + 1 / 1 →
  Norm.normSq
    (Four._-q_
      (centreTransportAction u v value)
      (centreTransportAction u' v' value))
  ≤ (+ 8 / 1)
      * (Norm.normSq (Four._-q_ u u')
        + Norm.normSq (Four._-q_ v v'))
      * Norm.normSq value
centreTransportDifferenceNormSqBound
    u v u' v' value uUnit vUnit u'Unit v'Unit =
  let
    w = relativeProduct u v
    w' = relativeProduct u' v'
    adjointBound = TwoAd.unitAdjointDifferenceNormSqBound
      w w' value
      (relativeProductUnit u v uUnit vUnit)
      (relativeProductUnit u' v' u'Unit v'Unit)
    relativeBound = relativeProductDifferenceNormSqBound
      u v u' v' vUnit u'Unit
    scaleNN = ℚP.nonNegative⁻¹ ((+ 4 / 1) * Norm.normSq value)
    scaledRelative = Norm.scaleNonnegative
      ((+ 4 / 1) * Norm.normSq value)
      scaleNN relativeBound
  in
  ℚP.≤-trans adjointBound
    (subst
      (λ upper →
        (+ 4 / 1)
          * Norm.normSq (Four._-q_ w w')
          * Norm.normSq value
        ≤ upper)
      (ℚRing.solve-∀
        (Norm.normSq (Four._-q_ u u'))
        (Norm.normSq (Four._-q_ v v'))
        (Norm.normSq value))
      scaledRelative)

cmp109FederbushRelativeProductPhysicalLevel : ProofLevel
cmp109FederbushRelativeProductPhysicalLevel = machineChecked

cmp109FederbushCentreTransportPhysicalLevel : ProofLevel
cmp109FederbushCentreTransportPhysicalLevel = machineChecked

cmp109FederbushCentreTransportTwoBackgroundNormLevel : ProofLevel
cmp109FederbushCentreTransportTwoBackgroundNormLevel = machineChecked
