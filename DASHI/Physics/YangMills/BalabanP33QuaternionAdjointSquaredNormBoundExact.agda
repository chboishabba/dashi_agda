module DASHI.Physics.YangMills.BalabanP33QuaternionAdjointSquaredNormBoundExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- John H. Conway and Derek A. Smith,
-- "On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry",
-- A K Peters, 2003. DOI: 10.1201/9781439864180.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- An older adjoint-perturbation module left the quantitative estimate open
-- because rational quaternion norm multiplicativity/triangle control had not
-- yet been constructed.  Those lemmas now exist.  This file cross-pollinates
-- the two generations and proves, without square roots,
--
--   N(Ad_U X - X) <= 4 N(U-1) N(X)
--
-- for every literal unit-quaternion background link U.  This is exactly the
-- squared form of ||Ad_U X-X|| <= 2 ||U-1|| ||X|| and is directly consumable by
-- rational finite-energy/ghost estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

normSqIsPhysicalNormSq : ∀ value →
  Norm.normSq value ≡ Physical.quaternionNormSq value
normSqIsPhysicalNormSq (Q.quat q0 q1 q2 q3) = ℚRing.solve-∀ q0 q1 q2 q3

inverseLinkNormSqExact : ∀ background bond →
  Norm.normSq (Physical.inverseLink background bond) ≡ 1ℚ
inverseLinkNormSqExact background bond =
  trans
    (normSqIsPhysicalNormSq (Physical.inverseLink background bond))
    (trans
      (Adjoint.conjugateNormSqExact (Physical.link background bond))
      (Physical.unitNorm background bond))

conjugateDefectNormSqExact : ∀ unit →
  Norm.normSq
    (Telescope._-q_ (Physical.quaternionConjugate unit) Q.oneQ)
  ≡ Norm.normSq (Telescope._-q_ unit Q.oneQ)
conjugateDefectNormSqExact unit =
  trans
    (cong Norm.normSq (Adjoint.conjugateDifferenceFromIdentityExact unit))
    (trans
      (normSqIsPhysicalNormSq
        (Physical.quaternionConjugate
          (Telescope._-q_ unit Q.oneQ)))
      (trans
        (Adjoint.conjugateNormSqExact (Telescope._-q_ unit Q.oneQ))
        (sym (normSqIsPhysicalNormSq (Telescope._-q_ unit Q.oneQ)))))

leftAdjointFactorNormSqExact : ∀ background bond value →
  Norm.normSq
    ((Telescope._-q_ (Physical.link background bond) Q.oneQ) Q.*q
      (value Q.*q Physical.inverseLink background bond))
  ≡ Norm.normSq (Telescope._-q_ (Physical.link background bond) Q.oneQ)
      * Norm.normSq value
leftAdjointFactorNormSqExact background bond value
  rewrite Norm.normSqMultiplyExact
      (Telescope._-q_ (Physical.link background bond) Q.oneQ)
      (value Q.*q Physical.inverseLink background bond)
        | Norm.normSqMultiplyExact value (Physical.inverseLink background bond)
        | inverseLinkNormSqExact background bond =
  ℚRing.solve-∀
    (Norm.normSq (Telescope._-q_ (Physical.link background bond) Q.oneQ))
    (Norm.normSq value)

rightAdjointFactorNormSqExact : ∀ background bond value →
  Norm.normSq
    (value Q.*q
      (Telescope._-q_ (Physical.inverseLink background bond) Q.oneQ))
  ≡ Norm.normSq (Telescope._-q_ (Physical.link background bond) Q.oneQ)
      * Norm.normSq value
rightAdjointFactorNormSqExact background bond value
  rewrite Norm.normSqMultiplyExact value
      (Telescope._-q_ (Physical.inverseLink background bond) Q.oneQ)
        | conjugateDefectNormSqExact (Physical.link background bond) =
  ℚRing.solve-∀
    (Norm.normSq (Telescope._-q_ (Physical.link background bond) Q.oneQ))
    (Norm.normSq value)

physicalLinkAdjointDefectSquaredBound : ∀ background bond value →
  Norm.normSq (Adjoint.physicalLinkAdjointDefect background bond value)
  ≤ (+ 4 / 1)
      * (Norm.normSq (Telescope._-q_ (Physical.link background bond) Q.oneQ)
        * Norm.normSq value)
physicalLinkAdjointDefectSquaredBound background bond value =
  let
    left =
      (Telescope._-q_ (Physical.link background bond) Q.oneQ) Q.*q
        (value Q.*q Physical.inverseLink background bond)
    right =
      value Q.*q
        (Telescope._-q_ (Physical.inverseLink background bond) Q.oneQ)

    factorized :
      Adjoint.physicalLinkAdjointDefect background bond value
      ≡ left Q.+q right
    factorized = Adjoint.physicalLinkAdjointDefectFactorizationExact
      background bond value

    triangle :
      Norm.normSq (left Q.+q right)
      ≤ (+ 2 / 1) * (Norm.normSq left + Norm.normSq right)
    triangle = Norm.normSqAddBound left right

    rewritten :
      Norm.normSq (left Q.+q right)
      ≤ (+ 4 / 1)
          * (Norm.normSq
              (Telescope._-q_ (Physical.link background bond) Q.oneQ)
            * Norm.normSq value)
    rewritten =
      subst
        (λ leftNorm →
          Norm.normSq (left Q.+q right)
          ≤ (+ 2 / 1) * (leftNorm + Norm.normSq right))
        (leftAdjointFactorNormSqExact background bond value)
        (subst
          (λ rightNorm →
            Norm.normSq (left Q.+q right)
            ≤ (+ 2 / 1)
                * (Norm.normSq
                    (Telescope._-q_ (Physical.link background bond) Q.oneQ)
                    * Norm.normSq value + rightNorm))
          (rightAdjointFactorNormSqExact background bond value)
          (subst
            (λ upper → Norm.normSq (left Q.+q right) ≤ upper)
            (ℚRing.solve-∀
              (Norm.normSq
                (Telescope._-q_ (Physical.link background bond) Q.oneQ))
              (Norm.normSq value))
            triangle))
  in
  subst
    (λ selected →
      Norm.normSq selected
      ≤ (+ 4 / 1)
          * (Norm.normSq
              (Telescope._-q_ (Physical.link background bond) Q.oneQ)
            * Norm.normSq value))
    (sym factorized)
    rewritten

physicalGaugeAdjointSquaredNormEstimateLevel : ProofLevel
physicalGaugeAdjointSquaredNormEstimateLevel = machineChecked
