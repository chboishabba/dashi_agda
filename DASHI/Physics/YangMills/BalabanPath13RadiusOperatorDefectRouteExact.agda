{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13RadiusOperatorDefectRouteExact where

------------------------------------------------------------------------
-- PATH13 NATIVE RADIUS -> STANDARD OPERATOR DEFECT
--
-- The Path13 coercivity lane already owns the native physical small-field
-- carrier
--
--   SelectedInverseLinkRadius13 A
--     = forall b, N(A(b)^-1 - 1) <= 4 rho^2.
--
-- This module reuses that SAME carrier to feed the CMP98 operator-norm
-- telescope.  It therefore removes the detour through an abstract selected
-- variational defect when all that the path argument needs is the physical
-- 1/2048 per-link operator bound.
--
-- The standard rational SU(2) operator representation is owned by R171.  Its
-- identity/product/conjugation laws are source-independent representation
-- facts and are not repaid in this Path13 specialization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; s≤s)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanCMP98SU2OperatorDefectFromPhysicalRadiusRound171Exact as R171
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Op
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as QTelescope
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointNormSquaredExact as AdjointNorm
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanP33RelaxedRadiusQuaternionL1DefectExact as L1
import DASHI.Physics.YangMills.BalabanP33RelaxedRadiusQuaternionL1SharpExact as Sharp
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierErasureBridgeExact as Erasure
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierRound187Exact as R187
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanCMP109QuaternionPathTransportTelescopeExact as RawPath
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Quaternion
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33CMP109MinimalPathStageBudgetExact as PathBudget
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164

ExactRationalSU2OperatorDefectRepresentation : Set₁
ExactRationalSU2OperatorDefectRepresentation =
  R171.RationalSU2OperatorDefectRepresentation

operatorKernel :
  ExactRationalSU2OperatorDefectRepresentation →
  Op.UnitaryOperatorDefectKernel Q.RationalQuaternion
operatorKernel = R171.kernel

path13PositiveLinkNormSqBelowRadius :
  ∀ background → Background.SelectedInverseLinkRadius13 background →
  ∀ axis site →
  Norm.normSq
    (QTelescope._-q_ (Background.link background axis site) Q.oneQ)
  ≤ Relaxed.fourRhoSquare
path13PositiveLinkNormSqBelowRadius background radius axis site =
  let
    inverseBound = Background.inverseLinkDefectBound radius axis site
    sameNorm = AdjointNorm.inverseDifferenceNormSqExact
      (Background.link background axis site)
  in
  subst (λ lower → lower ≤ Relaxed.fourRhoSquare) sameNorm inverseBound

path13PositiveLinkQuaternionL1BelowOne2048 :
  ∀ background → Background.SelectedInverseLinkRadius13 background →
  ∀ axis site →
  L1.quaternionDefectL1
    (QTelescope._-q_ (Background.link background axis site) Q.oneQ)
  ≤ Budget.perLinkDefectMajorant
path13PositiveLinkQuaternionL1BelowOne2048 background radius axis site =
  let
    raw = Sharp.relaxedNormSqImpliesSharpQuaternionL1Budget
      (QTelescope._-q_ (Background.link background axis site) Q.oneQ)
      (path13PositiveLinkNormSqBelowRadius background radius axis site)
    budgetExact : Sharp.sharpL1Budget ≡ Budget.perLinkDefectMajorant
    budgetExact = refl
  in
  subst
    (λ upper →
      L1.quaternionDefectL1
        (QTelescope._-q_ (Background.link background axis site) Q.oneQ)
      ≤ upper)
    budgetExact raw

path13PositiveLinkOperatorDefectBelowOne2048 :
  (representation : ExactRationalSU2OperatorDefectRepresentation) →
  ∀ background → Background.SelectedInverseLinkRadius13 background →
  ∀ axis site →
  Op.defect (operatorKernel representation)
    (Background.link background axis site)
  ≤ Budget.perLinkDefectMajorant
path13PositiveLinkOperatorDefectBelowOne2048 representation background radius axis site =
  ℚP.≤-trans
    (R171.operatorDefectBelowQuaternionL1 representation
      (Background.link background axis site))
    (path13PositiveLinkQuaternionL1BelowOne2048 background radius axis site)

rawOrientedFactorDefectSmallFromRadius :
  (representation : ExactRationalSU2OperatorDefectRepresentation) →
  ∀ background → Background.SelectedInverseLinkRadius13 background →
  ∀ site direction →
  Op.defect (operatorKernel representation)
    (R187.eraseUnitQuaternion
      (Bond.orientedLink
        (R192.path13PhysicalPeriodicRealization background)
        site direction))
  ≤ Budget.perLinkDefectMajorant
rawOrientedFactorDefectSmallFromRadius representation background radius site
    (Carrier.pair axis true) =
  subst
    (λ value → Op.defect (operatorKernel representation) value
      ≤ Budget.perLinkDefectMajorant)
    (sym
      (trans
        (Erasure.eraseOrientedLinkPositive
          (R192.path13PhysicalPeriodicRealization background) site axis)
        (R192.path13RealizationErasesToPhysicalLink background site axis)))
    (path13PositiveLinkOperatorDefectBelowOne2048
      representation background radius axis site)
rawOrientedFactorDefectSmallFromRadius representation background radius site
    (Carrier.pair axis false) =
  let
    predecessor = Bond.negativeStep site axis
    positive = Background.link background axis predecessor

    erasedNegativeIsConjugate :
      R187.eraseUnitQuaternion
        (Bond.orientedLink
          (R192.path13PhysicalPeriodicRealization background)
          site (Carrier.pair axis false))
      ≡ Quaternion.quaternionConjugate positive
    erasedNegativeIsConjugate =
      trans
        (Erasure.eraseOrientedLinkNegative
          (R192.path13PhysicalPeriodicRealization background) site axis)
        (cong Quaternion.quaternionConjugate
          (R192.path13RealizationErasesToPhysicalLink
            background predecessor axis))

    conjugateBound :
      Op.defect (operatorKernel representation)
        (Quaternion.quaternionConjugate positive)
      ≤ Budget.perLinkDefectMajorant
    conjugateBound =
      subst
        (λ lower → lower ≤ Budget.perLinkDefectMajorant)
        (sym (R171.kernelDefectConjugateInvariant representation positive))
        (path13PositiveLinkOperatorDefectBelowOne2048
          representation background radius axis predecessor)
  in
  subst
    (λ value → Op.defect (operatorKernel representation) value
      ≤ Budget.perLinkDefectMajorant)
    (sym erasedNegativeIsConjugate)
    conjugateBound

rawPathDefectBelowLengthBudgetFromRadius :
  (representation : ExactRationalSU2OperatorDefectRepresentation) →
  ∀ background → Background.SelectedInverseLinkRadius13 background →
  ∀ site word bound →
  R164.listLength word ≤ bound →
  Op.defect (operatorKernel representation)
    (RawPath.pathProduct
      (Erasure.rawPathFactors
        (R192.path13PhysicalPeriodicRealization background) site word))
  ≤ Sums.natAsRational bound * Budget.perLinkDefectMajorant
rawPathDefectBelowLengthBudgetFromRadius representation background radius site [] bound lengthBound =
  subst
    (λ selectedValue →
      Op.defect (operatorKernel representation) selectedValue
      ≤ Sums.natAsRational bound * Budget.perLinkDefectMajorant)
    (R171.kernelIdentityIsQuaternionIdentity representation)
    (subst
      (λ lower → lower
        ≤ Sums.natAsRational bound * Budget.perLinkDefectMajorant)
      (sym (Op.identityDefectZero (operatorKernel representation)))
      (PathBudget.productNonnegative
        (Sums.natAsRational bound) Budget.perLinkDefectMajorant
        (PathBudget.natAsRationalNonnegative bound)
        Budget.perLinkDefectMajorantNonnegative))
rawPathDefectBelowLengthBudgetFromRadius representation background radius site (_ ∷ _) zero ()
rawPathDefectBelowLengthBudgetFromRadius representation background radius site
    (direction ∷ directions) (suc bound) (s≤s tailLength) =
  let
    realization = R192.path13PhysicalPeriodicRealization background
    head = R187.eraseUnitQuaternion (Bond.orientedLink realization site direction)
    tail = RawPath.pathProduct
      (Erasure.rawPathFactors realization (Bond.walkStep site direction) directions)

    productBound :
      Op.defect (operatorKernel representation)
        (Op.multiply (operatorKernel representation) head tail)
      ≤ Op.defect (operatorKernel representation) head
        + Op.defect (operatorKernel representation) tail
    productBound =
      Op.productDefectTriangle (operatorKernel representation) head tail

    headTailBound :
      Op.defect (operatorKernel representation) head
        + Op.defect (operatorKernel representation) tail
      ≤ Budget.perLinkDefectMajorant
        + (Sums.natAsRational bound * Budget.perLinkDefectMajorant)
    headTailBound = ℚP.+-mono-≤
      (rawOrientedFactorDefectSmallFromRadius
        representation background radius site direction)
      (rawPathDefectBelowLengthBudgetFromRadius
        representation background radius
        (Bond.walkStep site direction) directions bound tailLength)

    successorBound :
      Op.defect (operatorKernel representation)
        (Op.multiply (operatorKernel representation) head tail)
      ≤ Sums.natAsRational (suc bound) * Budget.perLinkDefectMajorant
    successorBound =
      subst
        (λ upper →
          Op.defect (operatorKernel representation)
            (Op.multiply (operatorKernel representation) head tail)
          ≤ upper)
        (PathBudget.successorBudgetExact bound Budget.perLinkDefectMajorant)
        (ℚP.≤-trans productBound headTailBound)
  in
  subst
    (λ selectedValue →
      Op.defect (operatorKernel representation) selectedValue
      ≤ Sums.natAsRational (suc bound) * Budget.perLinkDefectMajorant)
    (R171.kernelMultiplyIsQuaternionMultiply representation head tail)
    successorBound

path13NativeRadiusToOperatorDefectLevel : ProofLevel
path13NativeRadiusToOperatorDefectLevel = machineChecked

path13NativeRadiusRawPathTelescopeLevel : ProofLevel
path13NativeRadiusRawPathTelescopeLevel = machineChecked

path13ExactRationalSU2OperatorRepresentationLevel : ProofLevel
path13ExactRationalSU2OperatorRepresentationLevel =
  R171.cmp98RationalSU2OperatorRepresentationRound171Level

------------------------------------------------------------------------
-- Direct squared-chord route on the actual unit group.  Unlike the
-- operator-defect representation socket above, this uses only the
-- existing rational quaternion norm theorem and finite path recursion.
------------------------------------------------------------------------

chordRadiusSq : SU2.RationalUnitQuaternion → ℚ
chordRadiusSq q =
  Norm.normSq (QTelescope._-q_ (R187.eraseUnitQuaternion q) Q.oneQ)

chordRadiusSqIsLiteral : ∀ q →
  chordRadiusSq q ≡ SU2.literalChordalDistanceSq q
chordRadiusSqIsLiteral (SU2.rationalUnitQuaternion a x y z _) =
  Ring.solve-∀ a x y z

unitRawNorm : ∀ q → Norm.normSq (R187.eraseUnitQuaternion q) ≡ 1ℚ
unitRawNorm q = SU2.unitNormExact q

unitProductDifference : ∀ u v →
  QTelescope._-q_ (R187.eraseUnitQuaternion (Group.multiplyRationalSU2 u v)) Q.oneQ
  ≡ ((QTelescope._-q_ (R187.eraseUnitQuaternion u) Q.oneQ)
      Q.*q R187.eraseUnitQuaternion v)
      Q.+q QTelescope._-q_ (R187.eraseUnitQuaternion v) Q.oneQ
unitProductDifference (SU2.rationalUnitQuaternion a x y z _)
                      (SU2.rationalUnitQuaternion b p q t _) =
  Q.quaternionExt (Ring.solve-∀ a x y z b p q t)
    (Ring.solve-∀ a x y z b p q t)
    (Ring.solve-∀ a x y z b p q t)
    (Ring.solve-∀ a x y z b p q t)

unitProductChordBound : ∀ u v a b →
  0ℚ ℚ.< a → 0ℚ ℚ.< b →
  chordRadiusSq u ≤ a * a → chordRadiusSq v ≤ b * b →
  chordRadiusSq (Group.multiplyRationalSU2 u v) ≤ (a + b) * (a + b)
unitProductChordBound u v a b ap bp hu hv =
  let du = QTelescope._-q_ (R187.eraseUnitQuaternion u) Q.oneQ
      dv = QTelescope._-q_ (R187.eraseUnitQuaternion v) Q.oneQ
      rightTransport = du Q.*q R187.eraseUnitQuaternion v
      sameNorm : Norm.normSq rightTransport ≡ chordRadiusSq u
      sameNorm rewrite Norm.normSqMultiplyExact du (R187.eraseUnitQuaternion v)
                     | unitRawNorm v = ℚP.*-identityʳ (chordRadiusSq u)
      transportedBound = subst (λ x → x ≤ a * a) (sym sameNorm) hu
  in subst (λ x → Norm.normSq x ≤ (a + b) * (a + b))
       (sym (unitProductDifference u v))
       (Norm.radiusTriangleSquared a b rightTransport dv ap bp transportedBound hv)

chordInverseExact : ∀ q →
  chordRadiusSq (Group.inverseRationalSU2 q) ≡ chordRadiusSq q
chordInverseExact q =
  trans (cong (λ v → Norm.normSq (QTelescope._-q_ v Q.oneQ))
    (Erasure.eraseInverse q))
    (AdjointNorm.inverseDifferenceNormSqExact (R187.eraseUnitQuaternion q))

epsChord : ℚ
epsChord = Budget.perLinkDefectMajorant

epsChordPositive : 0ℚ ℚ.< epsChord
epsChordPositive = ℚP.positive⁻¹ epsChord

linkSqBelowEpsSq : Relaxed.fourRhoSquare ≤ epsChord * epsChord
linkSqBelowEpsSq =
  ℚP.<⇒≤ (ℚP.positive⁻¹ (epsChord * epsChord - Relaxed.fourRhoSquare))

path13OrientedChordSq : ∀ background → Background.SelectedInverseLinkRadius13 background →
  ∀ site direction →
  chordRadiusSq (Bond.orientedLink (R192.path13PhysicalPeriodicRealization background)
    site direction) ≤ epsChord * epsChord
path13OrientedChordSq background radius site (Carrier.pair axis true) =
  subst (λ raw → Norm.normSq (QTelescope._-q_ raw Q.oneQ) ≤ epsChord * epsChord)
    (sym (trans
      (Erasure.eraseOrientedLinkPositive
        (R192.path13PhysicalPeriodicRealization background) site axis)
      (R192.path13RealizationErasesToPhysicalLink background site axis)))
    (ℚP.≤-trans (path13PositiveLinkNormSqBelowRadius background radius axis site)
      linkSqBelowEpsSq)
path13OrientedChordSq background radius site (Carrier.pair axis false) =
  let predecessor = Bond.negativeStep site axis
      erased = trans
        (Erasure.eraseOrientedLinkNegative
          (R192.path13PhysicalPeriodicRealization background) site axis)
        (cong Quaternion.quaternionConjugate
          (R192.path13RealizationErasesToPhysicalLink background predecessor axis))
      invbound = subst (λ d → d ≤ epsChord * epsChord)
        (sym (AdjointNorm.inverseDifferenceNormSqExact (Background.link background axis predecessor)))
        (ℚP.≤-trans (path13PositiveLinkNormSqBelowRadius background radius axis predecessor)
          linkSqBelowEpsSq)
  in subst (λ raw → Norm.normSq (QTelescope._-q_ raw Q.oneQ) ≤ epsChord * epsChord)
       (sym erased) invbound

chordBudget : Nat → ℚ
chordBudget zero = 0ℚ
chordBudget (suc n) = epsChord + chordBudget n

chordBudgetNN : ∀ n → 0ℚ ≤ chordBudget n
chordBudgetNN zero = ℚP.≤-refl
chordBudgetNN (suc n) = ℚP.+-mono-≤
  (ℚP.<⇒≤ epsChordPositive) (chordBudgetNN n)

chordBudgetPositive : ∀ n → 0ℚ ℚ.< chordBudget (suc n)
chordBudgetPositive n =
  ℚP.<-≤-trans epsChordPositive
    (subst (λ left → left ≤ epsChord + chordBudget n)
      (ℚP.+-identityʳ epsChord)
      (ℚP.+-monoʳ-≤ epsChord (chordBudgetNN n)))

chordBudgetIsLengthTimesEps : ∀ n →
  chordBudget n ≡ Sums.natAsRational n * epsChord
chordBudgetIsLengthTimesEps zero = sym (ℚP.*-zeroˡ epsChord)
chordBudgetIsLengthTimesEps (suc n) rewrite chordBudgetIsLengthTimesEps n =
  PathBudget.successorBudgetExact n epsChord

pathChordSqBelowLengthBudget : ∀ background →
  Background.SelectedInverseLinkRadius13 background →
  ∀ site word bound →
  R164.listLength word ≤ bound →
  chordRadiusSq (Bond.pathHolonomy
    (R192.path13PhysicalPeriodicRealization background) site word)
  ≤ chordBudget bound * chordBudget bound
pathChordSqBelowLengthBudget background radius site [] bound le =
  PathBudget.productNonnegative (chordBudget bound) (chordBudget bound)
    (chordBudgetNN bound) (chordBudgetNN bound)
pathChordSqBelowLengthBudget background radius site (_ ∷ _) zero ()
pathChordSqBelowLengthBudget background radius site (d ∷ []) (suc zero) le =
  let u = Bond.orientedLink (R192.path13PhysicalPeriodicRealization background) site d
      fixed = path13OrientedChordSq background radius site d
  in subst (λ q → chordRadiusSq q ≤ chordBudget 1 * chordBudget 1)
       (sym (Group.identityRight u))
       (subst (λ upper → chordRadiusSq u ≤ upper)
         (Ring.solve []) fixed)
pathChordSqBelowLengthBudget background radius site (d ∷ e ∷ es) (suc zero) (s≤s ())
pathChordSqBelowLengthBudget background radius site (d ∷ ds) (suc (suc n)) (s≤s le) =
  let real = R192.path13PhysicalPeriodicRealization background
  in unitProductChordBound (Bond.orientedLink real site d)
       (Bond.pathHolonomy real (Bond.walkStep site d) ds)
       epsChord (chordBudget (suc n))
       epsChordPositive (chordBudgetPositive n)
       (path13OrientedChordSq background radius site d)
       (pathChordSqBelowLengthBudget background radius (Bond.walkStep site d) ds (suc n) le)
