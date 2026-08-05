module DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasEntryDecayExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Werner Kirsch,
-- "An Invitation to Random Schrödinger Operators",
-- Panoramas et Synthèses 25 (2008), 1--119; arXiv:0709.3707.
-- No DOI was assigned to the cited survey chapter.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Close the remaining norm-to-entry socket of the physical Combes--Thomas
-- promotion.  From:
--
--   * the literal original right inverse H G = I;
--   * the squared tilted lower bound
--       (1/4096)||x||^2 <= ||H_D x||^2;
--   * exact finite matrix/action associativity;
--
-- the module proves
--
--       ||G_D v||^2 <= 4096 ||v||^2,
--       |G_D(x,y)| <= 64,
--       |G(root,y)| <= 64 t^d(root,y).
--
-- Thus the tilted entry bound is produced, not stored as an independent record
-- premise.  The only remaining physical inputs are upstream: the literal
-- 1/32 Hessian coercivity and the literal stencil/shell row-mass budget.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Empty; yes; no)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact as CT
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasPromotionExact as Promotion
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33CombesThomasSquaredHalfGapExact as Squared
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasSchurExact as PhysicalSchur
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33CombesThomasCoercivitySurvivalExact as Survival

Coordinate : Set
Coordinate = Physical.PhysicalSU2Coordinate4

PhysicalMatrix : Set
PhysicalMatrix = Physical.PhysicalSU2Matrix4

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

------------------------------------------------------------------------
-- Exact finite action/composition algebra.
------------------------------------------------------------------------

physicalMatrixApplyCompositionExact :
  ∀ (left right : PhysicalMatrix) vector row →
  Physical.physicalMatrixApply left
    (Physical.physicalMatrixApply right vector) row
  ≡ Physical.physicalMatrixApply
      (CT.composeMatrix Physical.physicalSU2Coordinates4 left right)
      vector row
physicalMatrixApplyCompositionExact left right vector row =
  let
    expandedRows :
      Sums.sumRational Physical.physicalSU2Coordinates4
        (λ middle →
          left row middle
            * Sums.sumRational Physical.physicalSU2Coordinates4
                (λ column → right middle column * vector column))
      ≡ Sums.sumRational Physical.physicalSU2Coordinates4
          (λ middle →
            Sums.sumRational Physical.physicalSU2Coordinates4
              (λ column →
                left row middle
                  * (right middle column * vector column)))
    expandedRows =
      Sums.sumRationalCong
        Physical.physicalSU2Coordinates4
        (λ middle →
          left row middle
            * Sums.sumRational Physical.physicalSU2Coordinates4
                (λ column → right middle column * vector column))
        (λ middle →
          Sums.sumRational Physical.physicalSU2Coordinates4
            (λ column →
              left row middle
                * (right middle column * vector column)))
        (λ middle →
          sym
            (Sums.sumRationalScale
              (left row middle)
              Physical.physicalSU2Coordinates4
              (λ column → right middle column * vector column)))

    swapped :
      Sums.sumRational Physical.physicalSU2Coordinates4
        (λ middle →
          Sums.sumRational Physical.physicalSU2Coordinates4
            (λ column →
              left row middle
                * (right middle column * vector column)))
      ≡ Sums.sumRational Physical.physicalSU2Coordinates4
          (λ column →
            Sums.sumRational Physical.physicalSU2Coordinates4
              (λ middle →
                left row middle
                  * (right middle column * vector column)))
    swapped =
      Fubini.sumSwap
        Physical.physicalSU2Coordinates4
        Physical.physicalSU2Coordinates4
        (λ middle column →
          left row middle * (right middle column * vector column))

    collectedColumn : ∀ column →
      Sums.sumRational Physical.physicalSU2Coordinates4
        (λ middle →
          left row middle * (right middle column * vector column))
      ≡ CT.composeMatrix Physical.physicalSU2Coordinates4
          left right row column * vector column
    collectedColumn column =
      trans
        (Sums.sumRationalCong
          Physical.physicalSU2Coordinates4
          (λ middle →
            left row middle * (right middle column * vector column))
          (λ middle →
            vector column * (left row middle * right middle column))
          (λ middle → ℚRing.solve []))
        (trans
          (Sums.sumRationalScale
            (vector column)
            Physical.physicalSU2Coordinates4
            (λ middle → left row middle * right middle column))
          (ℚRing.solve-∀
            (CT.composeMatrix Physical.physicalSU2Coordinates4
              left right row column)
            (vector column)))

    collectedColumns :
      Sums.sumRational Physical.physicalSU2Coordinates4
        (λ column →
          Sums.sumRational Physical.physicalSU2Coordinates4
            (λ middle →
              left row middle * (right middle column * vector column)))
      ≡ Sums.sumRational Physical.physicalSU2Coordinates4
          (λ column →
            CT.composeMatrix Physical.physicalSU2Coordinates4
              left right row column * vector column)
    collectedColumns =
      Sums.sumRationalCong
        Physical.physicalSU2Coordinates4
        (λ column →
          Sums.sumRational Physical.physicalSU2Coordinates4
            (λ middle →
              left row middle * (right middle column * vector column)))
        (λ column →
          CT.composeMatrix Physical.physicalSU2Coordinates4
            left right row column * vector column)
        collectedColumn
  in
  trans expandedRows (trans swapped collectedColumns)

identityEntrySymmetric : ∀ left right →
  Calibration.identityEntry left right
  ≡ Calibration.identityEntry right left
identityEntrySymmetric left right
  with Calibration.physicalCoordinateDecidableEquality left right
     | Calibration.physicalCoordinateDecidableEquality right left
... | yes refl | yes refl = refl
... | yes refl | no rightNotLeft =
  emptyElim (rightNotLeft refl)
... | no leftNotRight | yes rightEqualsLeft =
  emptyElim (leftNotRight (sym rightEqualsLeft))
... | no _ | no _ = refl

physicalIdentityApplyExact : ∀ vector row →
  Physical.physicalMatrixApply Calibration.identityEntry vector row
  ≡ vector row
physicalIdentityApplyExact vector row =
  trans
    (Sums.sumRationalCong
      Physical.physicalSU2Coordinates4
      (λ column → Calibration.identityEntry row column * vector column)
      (λ column → vector column * Calibration.identityEntry column row)
      (λ column →
        trans
          (cong
            (_* vector column)
            (identityEntrySymmetric row column))
          (ℚRing.solve [])))
    (Basis.physicalIdentitySelectorExact vector row)

rightInverseActsPointwise :
  ∀ operator inverse →
  CT.RightInverse
    Physical.physicalSU2Coordinates4
    Calibration.identityEntry operator inverse →
  ∀ vector row →
  Physical.physicalMatrixApply operator
    (Physical.physicalMatrixApply inverse vector) row
  ≡ vector row
rightInverseActsPointwise operator inverse rightInverse vector row =
  trans
    (physicalMatrixApplyCompositionExact operator inverse vector row)
    (trans
      (Sums.sumRationalCong
        Physical.physicalSU2Coordinates4
        (λ column →
          CT.composeMatrix Physical.physicalSU2Coordinates4
            operator inverse row column * vector column)
        (λ column → Calibration.identityEntry row column * vector column)
        (λ column →
          cong (_* vector column) (rightInverse row column)))
      (physicalIdentityApplyExact vector row))

rightInverseActsNormExact :
  ∀ operator inverse →
  CT.RightInverse
    Physical.physicalSU2Coordinates4
    Calibration.identityEntry operator inverse →
  ∀ vector →
  Physical.physicalSU2CoordinateNormSq
    (Physical.physicalMatrixApply operator
      (Physical.physicalMatrixApply inverse vector))
  ≡ Physical.physicalSU2CoordinateNormSq vector
rightInverseActsNormExact operator inverse rightInverse vector =
  Sums.sumRationalCong
    Physical.physicalSU2Coordinates4
    (λ row →
      FiniteL2.square
        (Physical.physicalMatrixApply operator
          (Physical.physicalMatrixApply inverse vector) row))
    (λ row → FiniteL2.square (vector row))
    (λ row →
      cong FiniteL2.square
        (rightInverseActsPointwise
          operator inverse rightInverse vector row))

------------------------------------------------------------------------
-- Squared resolvent package: no independently supplied entry bound.
------------------------------------------------------------------------

record PhysicalCombesThomasSquaredResolvent
    (hessian green : PhysicalMatrix) : Set₁ where
  field
    coercivity : PhysicalSchur.PhysicalOriginalSquaredCoercivity hessian

    hessianGreenRightInverse :
      CT.RightInverse
        Physical.physicalSU2Coordinates4
        Calibration.identityEntry hessian green

open PhysicalCombesThomasSquaredResolvent public

squaredGeometry :
  ∀ {hessian green} →
  PhysicalCombesThomasSquaredResolvent hessian green →
  Promotion.PhysicalCombesThomasGeometry hessian
squaredGeometry resolvent =
  PhysicalSchur.geometry
    (PhysicalSchur.schurData (coercivity resolvent))

physicalTiltedGreen :
  ∀ {hessian green} →
  PhysicalCombesThomasSquaredResolvent hessian green → PhysicalMatrix
physicalTiltedGreen {green = green} resolvent =
  CT.diagonalConjugate
    (Promotion.physicalWeight (squaredGeometry resolvent))
    (Promotion.physicalInverseWeight (squaredGeometry resolvent))
    green

physicalTiltedRightInverseFromSquaredData :
  ∀ {hessian green}
    (resolvent : PhysicalCombesThomasSquaredResolvent hessian green) →
  CT.RightInverse
    Physical.physicalSU2Coordinates4
    Calibration.identityEntry
    (PhysicalSchur.physicalTiltedHessian
      (PhysicalSchur.schurData (coercivity resolvent)))
    (physicalTiltedGreen resolvent)
physicalTiltedRightInverseFromSquaredData
    {hessian} {green} resolvent =
  CT.conjugatedRightInverseWithStableIdentity
    Physical.physicalSU2Coordinates4
    Calibration.identityEntry hessian green
    (Promotion.physicalWeight (squaredGeometry resolvent))
    (Promotion.physicalInverseWeight (squaredGeometry resolvent))
    (Promotion.physicalWeightInverseLaw (squaredGeometry resolvent))
    (hessianGreenRightInverse resolvent)
    (Promotion.physicalIdentityStable (squaredGeometry resolvent))

physicalTiltedInverseSquaredOperatorBound :
  ∀ {hessian green}
    (resolvent : PhysicalCombesThomasSquaredResolvent hessian green)
    vector →
  Physical.physicalSU2CoordinateNormSq
    (Physical.physicalMatrixApply
      (physicalTiltedGreen resolvent) vector)
  ≤ Squared.p33SquaredInverseScale
      * Physical.physicalSU2CoordinateNormSq vector
physicalTiltedInverseSquaredOperatorBound resolvent vector =
  let
    tiltedHessian =
      PhysicalSchur.physicalTiltedHessian
        (PhysicalSchur.schurData (coercivity resolvent))

    tiltedGreen = physicalTiltedGreen resolvent

    lower :
      Squared.p33HalfGapSquared
        * Physical.physicalSU2CoordinateNormSq
            (Physical.physicalMatrixApply tiltedGreen vector)
      ≤ Physical.physicalSU2CoordinateNormSq
          (Physical.physicalMatrixApply tiltedHessian
            (Physical.physicalMatrixApply tiltedGreen vector))
    lower =
      PhysicalSchur.physicalTiltedSquaredLower
        (coercivity resolvent)
        (Physical.physicalMatrixApply tiltedGreen vector)

    upperIdentified :
      Squared.p33HalfGapSquared
        * Physical.physicalSU2CoordinateNormSq
            (Physical.physicalMatrixApply tiltedGreen vector)
      ≤ Physical.physicalSU2CoordinateNormSq vector
    upperIdentified =
      subst
        (λ upper →
          Squared.p33HalfGapSquared
            * Physical.physicalSU2CoordinateNormSq
                (Physical.physicalMatrixApply tiltedGreen vector)
          ≤ upper)
        (rightInverseActsNormExact
          tiltedHessian tiltedGreen
          (physicalTiltedRightInverseFromSquaredData resolvent)
          vector)
        lower
  in
  Squared.p33TiltedInverseSquaredBound
    (Physical.physicalSU2CoordinateNormSq
      (Physical.physicalMatrixApply tiltedGreen vector))
    (Physical.physicalSU2CoordinateNormSq vector)
    upperIdentified

physicalTiltedGreenEntryBound :
  ∀ {hessian green}
    (resolvent : PhysicalCombesThomasSquaredResolvent hessian green)
    row column →
  ∣ physicalTiltedGreen resolvent row column ∣
  ≤ Survival.p33InverseScale
physicalTiltedGreenEntryBound resolvent row column =
  subst
    (λ upper → ∣ physicalTiltedGreen resolvent row column ∣ ≤ upper)
    (ℚRing.solve [])
    (Basis.p33PhysicalEntryAbsoluteBoundFromSquaredOperator
      (physicalTiltedGreen resolvent) row column
      (physicalTiltedInverseSquaredOperatorBound resolvent))

physicalCombesThomasResolventFromSquaredData :
  ∀ {hessian green} →
  PhysicalCombesThomasSquaredResolvent hessian green →
  Promotion.PhysicalCombesThomasResolvent hessian green
physicalCombesThomasResolventFromSquaredData resolvent = record
  { geometry = squaredGeometry resolvent
  ; hessianGreenRightInverse = hessianGreenRightInverse resolvent
  ; tiltedGreenEntryBound =
      physicalTiltedGreenEntryBound resolvent
        (Promotion.root (squaredGeometry resolvent))
  }

physicalGreenKernelDecayFromSquaredData :
  ∀ {hessian green}
    (resolvent : PhysicalCombesThomasSquaredResolvent hessian green)
    target →
  ∣ green (Promotion.root (squaredGeometry resolvent)) target ∣
  ≤ Survival.p33InverseScale
      * Promotion.physicalWeight (squaredGeometry resolvent) target
physicalGreenKernelDecayFromSquaredData resolvent target =
  Promotion.physicalGreenKernelDecay
    (physicalCombesThomasResolventFromSquaredData resolvent)
    target

physicalMatrixActionCompositionLevel : ProofLevel
physicalMatrixActionCompositionLevel = machineChecked

physicalRightInverseActionLevel : ProofLevel
physicalRightInverseActionLevel = machineChecked

physicalTiltedInverseSquaredOperatorLevel : ProofLevel
physicalTiltedInverseSquaredOperatorLevel = machineChecked

physicalTiltedEntrySixtyFourLevel : ProofLevel
physicalTiltedEntrySixtyFourLevel = machineChecked

physicalGreenKernelDecayFromSquaredLevel : ProofLevel
physicalGreenKernelDecayFromSquaredLevel = machineChecked
