module DASHI.Physics.YangMills.BalabanP33PhysicalLinkJetSelectedFactorNormExact where

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
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Close the selected-factor algebra left by the physical Wilson telescope.
-- For either a positive or inverse physical link jet, the norm square of the
-- selected background-minus-flat factor is exactly
--
--   value  : delta,
--   first  : delta * N(X),
--   second : delta * N(X)^2,
--
-- where delta = N(U-1).  The inverse-link statement uses the proved equality
-- N(U^-1-1)=N(U-1).
--
-- Thus every physical placement weight is reducible to a literal link defect
-- and the appropriate insertion charge.  The remaining W-local analysis is
-- the signed aggregation and the proof that the actual selected background
-- supplies the required uniform link-defect radius.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointNormSquaredExact as AdjointNorm
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonPlacementTelescopeExact as Placement

selectedDefectWeight : Placement.FactorSelection → ℚ → ℚ → ℚ
selectedDefectWeight Placement.valueSelection linkDefect insertionNorm =
  linkDefect
selectedDefectWeight Placement.firstSelection linkDefect insertionNorm =
  linkDefect * insertionNorm
selectedDefectWeight Placement.secondSelection linkDefect insertionNorm =
  linkDefect * insertionNorm * insertionNorm

normSqNegExact : ∀ value →
  Norm.normSq (Q.negQ value) ≡ Norm.normSq value
normSqNegExact (Q.quat q0 q1 q2 q3) =
  ℚRing.solve-∀ q0 q1 q2 q3

positiveSelectionDefectNormalForm :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Placement.FactorSelection → Q.RationalQuaternion
positiveSelectionDefectNormalForm unit insertion Placement.valueSelection =
  Telescope._-q_ unit Q.oneQ
positiveSelectionDefectNormalForm unit insertion Placement.firstSelection =
  (Telescope._-q_ unit Q.oneQ) Q.*q insertion
positiveSelectionDefectNormalForm unit insertion Placement.secondSelection =
  ((Telescope._-q_ unit Q.oneQ) Q.*q insertion) Q.*q insertion

inverseSelectionDefectNormalForm :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Placement.FactorSelection → Q.RationalQuaternion
inverseSelectionDefectNormalForm unit insertion Placement.valueSelection =
  Telescope._-q_ (Physical.quaternionConjugate unit) Q.oneQ
inverseSelectionDefectNormalForm unit insertion Placement.firstSelection =
  Q.negQ
    (insertion Q.*q
      (Telescope._-q_ (Physical.quaternionConjugate unit) Q.oneQ))
inverseSelectionDefectNormalForm unit insertion Placement.secondSelection =
  (insertion Q.*q insertion) Q.*q
    (Telescope._-q_ (Physical.quaternionConjugate unit) Q.oneQ)

positiveSelectedFactorDefect :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Placement.FactorSelection → Q.RationalQuaternion
positiveSelectedFactorDefect unit insertion selection =
  Telescope._-q_
    (Placement.applySelection selection
      (Physical.positiveLinkJet unit insertion))
    (Placement.applySelection selection
      (Physical.positiveLinkJet Q.oneQ insertion))

inverseSelectedFactorDefect :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Placement.FactorSelection → Q.RationalQuaternion
inverseSelectedFactorDefect unit insertion selection =
  Telescope._-q_
    (Placement.applySelection selection
      (Physical.inverseLinkJet unit insertion))
    (Placement.applySelection selection
      (Physical.inverseLinkJet Q.oneQ insertion))

positiveSelectedFactorDefectExact : ∀ unit insertion selection →
  positiveSelectedFactorDefect unit insertion selection
  ≡ positiveSelectionDefectNormalForm unit insertion selection
positiveSelectedFactorDefectExact
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Placement.valueSelection =
  Q.quaternionExt
    (ℚRing.solve-∀ u0) (ℚRing.solve-∀ u1)
    (ℚRing.solve-∀ u2) (ℚRing.solve-∀ u3)
positiveSelectedFactorDefectExact
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Placement.firstSelection =
  Q.quaternionExt
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
positiveSelectedFactorDefectExact
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Placement.secondSelection =
  Q.quaternionExt
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)

inverseSelectedFactorDefectExact : ∀ unit insertion selection →
  inverseSelectedFactorDefect unit insertion selection
  ≡ inverseSelectionDefectNormalForm unit insertion selection
inverseSelectedFactorDefectExact
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Placement.valueSelection =
  Q.quaternionExt
    (ℚRing.solve-∀ u0) (ℚRing.solve-∀ u1)
    (ℚRing.solve-∀ u2) (ℚRing.solve-∀ u3)
inverseSelectedFactorDefectExact
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Placement.firstSelection =
  Q.quaternionExt
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
inverseSelectedFactorDefectExact
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3)
    Placement.secondSelection =
  Q.quaternionExt
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3)

positiveSelectedFactorNormSqExact : ∀ unit insertion selection →
  Norm.normSq (positiveSelectedFactorDefect unit insertion selection)
  ≡ selectedDefectWeight selection
      (Norm.normSq (Telescope._-q_ unit Q.oneQ))
      (Norm.normSq insertion)
positiveSelectedFactorNormSqExact unit insertion Placement.valueSelection =
  cong Norm.normSq
    (positiveSelectedFactorDefectExact
      unit insertion Placement.valueSelection)
positiveSelectedFactorNormSqExact unit insertion Placement.firstSelection =
  trans
    (cong Norm.normSq
      (positiveSelectedFactorDefectExact
        unit insertion Placement.firstSelection))
    (Norm.normSqMultiplyExact
      (Telescope._-q_ unit Q.oneQ) insertion)
positiveSelectedFactorNormSqExact unit insertion Placement.secondSelection =
  trans
    (cong Norm.normSq
      (positiveSelectedFactorDefectExact
        unit insertion Placement.secondSelection))
    (trans
      (Norm.normSqMultiplyExact
        ((Telescope._-q_ unit Q.oneQ) Q.*q insertion)
        insertion)
      (cong (_* Norm.normSq insertion)
        (Norm.normSqMultiplyExact
          (Telescope._-q_ unit Q.oneQ) insertion)))

inverseSelectedFactorNormSqExact : ∀ unit insertion selection →
  Norm.normSq (inverseSelectedFactorDefect unit insertion selection)
  ≡ selectedDefectWeight selection
      (Norm.normSq (Telescope._-q_ unit Q.oneQ))
      (Norm.normSq insertion)
inverseSelectedFactorNormSqExact unit insertion Placement.valueSelection =
  trans
    (cong Norm.normSq
      (inverseSelectedFactorDefectExact
        unit insertion Placement.valueSelection))
    (AdjointNorm.inverseDifferenceNormSqExact unit)
inverseSelectedFactorNormSqExact unit insertion Placement.firstSelection =
  trans
    (cong Norm.normSq
      (inverseSelectedFactorDefectExact
        unit insertion Placement.firstSelection))
    (trans
      (normSqNegExact
        (insertion Q.*q
          (Telescope._-q_
            (Physical.quaternionConjugate unit) Q.oneQ)))
      (trans
        (Norm.normSqMultiplyExact insertion
          (Telescope._-q_
            (Physical.quaternionConjugate unit) Q.oneQ))
        (trans
          (cong (Norm.normSq insertion *_)
            (AdjointNorm.inverseDifferenceNormSqExact unit))
          (ℚRing.solve-∀
            (Norm.normSq (Telescope._-q_ unit Q.oneQ))
            (Norm.normSq insertion)))))
inverseSelectedFactorNormSqExact unit insertion Placement.secondSelection =
  trans
    (cong Norm.normSq
      (inverseSelectedFactorDefectExact
        unit insertion Placement.secondSelection))
    (trans
      (Norm.normSqMultiplyExact
        (insertion Q.*q insertion)
        (Telescope._-q_
          (Physical.quaternionConjugate unit) Q.oneQ))
      (trans
        (cong (_* Norm.normSq
          (Telescope._-q_
            (Physical.quaternionConjugate unit) Q.oneQ))
          (Norm.normSqMultiplyExact insertion insertion))
        (trans
          (cong
            ((Norm.normSq insertion * Norm.normSq insertion) *_)
            (AdjointNorm.inverseDifferenceNormSqExact unit))
          (ℚRing.solve-∀
            (Norm.normSq (Telescope._-q_ unit Q.oneQ))
            (Norm.normSq insertion)))))

physicalLinkJetSelectedFactorExactLevel : ProofLevel
physicalLinkJetSelectedFactorExactLevel = machineChecked

physicalLinkJetSelectedFactorNormLevel : ProofLevel
physicalLinkJetSelectedFactorNormLevel = machineChecked

physicalSelectedBackgroundLinkRadiusLevel : ProofLevel
physicalSelectedBackgroundLinkRadiusLevel = conditional
