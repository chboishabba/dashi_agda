module DASHI.Physics.YangMills.BalabanP33QuaternionAdjointNormSquaredExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway and Derek A. Smith,
-- "On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry",
-- A K Peters, 2003. DOI: 10.1201/9781439864180.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- DASHI CONTRIBUTION
--
-- Close the generic quantitative part of the background-gauge adjoint defect
-- over exact rational norm squares.  For a unit quaternion U,
--
--   N(Ad_U X-X) <= 4 N(U-1) N(X).
--
-- The proof uses the exact two-term factorization
--
--   (U-1) X U^-1 + X (U^-1-1),
--
-- norm multiplicativity, conjugation invariance and the proved two-term
-- square inequality.  It is specialized both to a physical background link
-- and to its inverse, the latter being the transport occurring in the literal
-- covariant backward divergence.
--
-- The remaining gauge estimate is now the finite site/direction incidence and
-- comparison between the summed coordinate defect and the flat divergence;
-- no adjoint norm estimate remains as an external premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

normSqMatchesPhysicalNormSq : ∀ value →
  Norm.normSq value ≡ Physical.quaternionNormSq value
normSqMatchesPhysicalNormSq (Q.quat q0 q1 q2 q3) = refl

physicalConjugateNormSqExact : ∀ value →
  Norm.normSq (Physical.quaternionConjugate value) ≡ Norm.normSq value
physicalConjugateNormSqExact (Q.quat q0 q1 q2 q3) =
  ℚRing.solve-∀ q0 q1 q2 q3

inverseDifferenceNormSqExact : ∀ unit →
  Norm.normSq
    (Telescope._-q_ (Physical.quaternionConjugate unit) Q.oneQ)
  ≡ Norm.normSq (Telescope._-q_ unit Q.oneQ)
inverseDifferenceNormSqExact unit =
  trans
    (cong Norm.normSq
      (Adjoint.conjugateDifferenceFromIdentityExact unit))
    (physicalConjugateNormSqExact
      (Telescope._-q_ unit Q.oneQ))

adjointLeftTerm adjointRightTerm :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
adjointLeftTerm unit value =
  (Telescope._-q_ unit Q.oneQ) Q.*q
    (value Q.*q Physical.quaternionConjugate unit)
adjointRightTerm unit value =
  value Q.*q
    (Telescope._-q_ (Physical.quaternionConjugate unit) Q.oneQ)

adjointLeftTermNormSqExact : ∀ unit value →
  Norm.normSq (adjointLeftTerm unit value)
  ≡ Norm.normSq (Telescope._-q_ unit Q.oneQ)
    * Norm.normSq value * Norm.normSq unit
adjointLeftTermNormSqExact unit value
  rewrite Norm.normSqMultiplyExact
      (Telescope._-q_ unit Q.oneQ)
      (value Q.*q Physical.quaternionConjugate unit)
        | Norm.normSqMultiplyExact value
      (Physical.quaternionConjugate unit)
        | physicalConjugateNormSqExact unit =
  ℚRing.solve-∀
    (Norm.normSq (Telescope._-q_ unit Q.oneQ))
    (Norm.normSq value)
    (Norm.normSq unit)

adjointRightTermNormSqExact : ∀ unit value →
  Norm.normSq (adjointRightTerm unit value)
  ≡ Norm.normSq value
    * Norm.normSq (Telescope._-q_ unit Q.oneQ)
adjointRightTermNormSqExact unit value
  rewrite Norm.normSqMultiplyExact value
      (Telescope._-q_ (Physical.quaternionConjugate unit) Q.oneQ)
        | inverseDifferenceNormSqExact unit =
  refl

unitAdjointDefectNormSqBound : ∀ unit value →
  Norm.normSq unit ≡ + 1 / 1 →
  Norm.normSq (Adjoint.adjointDefect unit value)
  ≤ (+ 4 / 1)
      * Norm.normSq (Telescope._-q_ unit Q.oneQ)
      * Norm.normSq value
unitAdjointDefectNormSqBound unit value unitNorm =
  let
    left = adjointLeftTerm unit value
    right = adjointRightTerm unit value
    defectFactorization = Adjoint.adjointDefectFactorization unit value

    additiveBound :
      Norm.normSq (left Q.+q right)
      ≤ (+ 2 / 1) * (Norm.normSq left + Norm.normSq right)
    additiveBound = Norm.normSqAddBound left right

    termSumExact :
      Norm.normSq left + Norm.normSq right
      ≡ (+ 2 / 1)
          * (Norm.normSq (Telescope._-q_ unit Q.oneQ)
            * Norm.normSq value)
    termSumExact
      rewrite adjointLeftTermNormSqExact unit value
            | adjointRightTermNormSqExact unit value
            | unitNorm =
      ℚRing.solve-∀
        (Norm.normSq (Telescope._-q_ unit Q.oneQ))
        (Norm.normSq value)

    factorizedBound :
      Norm.normSq defectFactorization
      ≤ (+ 4 / 1)
          * Norm.normSq (Telescope._-q_ unit Q.oneQ)
          * Norm.normSq value
    factorizedBound =
      subst
        (λ upper → Norm.normSq (left Q.+q right) ≤ upper)
        (trans
          (cong ((+ 2 / 1) *_) termSumExact)
          (ℚRing.solve-∀
            (Norm.normSq (Telescope._-q_ unit Q.oneQ))
            (Norm.normSq value)))
        additiveBound
  in
  subst
    (λ lower →
      Norm.normSq lower
      ≤ (+ 4 / 1)
          * Norm.normSq (Telescope._-q_ unit Q.oneQ)
          * Norm.normSq value)
    (sym (Adjoint.adjointDefectFactorizationExact unit value))
    factorizedBound

physicalLinkNormSqExact :
  ∀ background bond →
  Norm.normSq (Physical.link background bond) ≡ + 1 / 1
physicalLinkNormSqExact background bond =
  trans
    (normSqMatchesPhysicalNormSq (Physical.link background bond))
    (Physical.unitNorm background bond)

physicalInverseLinkNormSqExact :
  ∀ background bond →
  Norm.normSq (Physical.inverseLink background bond) ≡ + 1 / 1
physicalInverseLinkNormSqExact background bond =
  trans
    (physicalConjugateNormSqExact (Physical.link background bond))
    (physicalLinkNormSqExact background bond)

physicalLinkAdjointDefectNormSqBound :
  ∀ background bond value →
  Norm.normSq
    (Adjoint.physicalLinkAdjointDefect background bond value)
  ≤ (+ 4 / 1)
      * Norm.normSq
          (Telescope._-q_ (Physical.link background bond) Q.oneQ)
      * Norm.normSq value
physicalLinkAdjointDefectNormSqBound background bond value =
  unitAdjointDefectNormSqBound
    (Physical.link background bond) value
    (physicalLinkNormSqExact background bond)

physicalInverseLinkAdjointDefectNormSqBound :
  ∀ background bond value →
  Norm.normSq
    (Adjoint.adjointDefect
      (Physical.inverseLink background bond) value)
  ≤ (+ 4 / 1)
      * Norm.normSq
          (Telescope._-q_ (Physical.inverseLink background bond) Q.oneQ)
      * Norm.normSq value
physicalInverseLinkAdjointDefectNormSqBound background bond value =
  unitAdjointDefectNormSqBound
    (Physical.inverseLink background bond) value
    (physicalInverseLinkNormSqExact background bond)

quaternionAdjointNormSquaredLevel : ProofLevel
quaternionAdjointNormSquaredLevel = machineChecked

physicalLinkAdjointNormSquaredLevel : ProofLevel
physicalLinkAdjointNormSquaredLevel = machineChecked

physicalGaugeGlobalIncidenceLevel : ProofLevel
physicalGaugeGlobalIncidenceLevel = conditional
