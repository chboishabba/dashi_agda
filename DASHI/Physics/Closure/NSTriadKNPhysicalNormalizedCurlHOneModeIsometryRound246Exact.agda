module DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedCurlHOneModeIsometryRound246Exact where

------------------------------------------------------------------------
-- ROUND246 / LITERAL MODEWISE NORMALIZED-CURL H^1 ISOMETRY
--
-- Backward need from Round243/W1:
--
--   || H u ||_{H^1} = || u ||_{H^1},
--
-- where H = |D|^-1 curl is the helicity-sign action.
--
-- Round142 already proves, on the literal Fourier carrier,
--
--   H u = u^+ - u^-.
--
-- The periodic helical laws prove, for transverse u,
--
--   u = u^+ + u^-
--
-- and <u^+,u^-> = 0.  Hermitian conjugate symmetry gives the reverse
-- cross term <u^-,u^+> = 0.  Expanding the literal Hermitian quadratic form
-- therefore proves
--
--   <u^+ - u^-, u^+ - u^-> = <u^+ + u^-, u^+ + u^->.
--
-- Multiplying both sides by the SAME literal |k|^2 weight closes the
-- modewise homogeneous H^1 energy isometry.  No abstract hsSquaredNorm law is
-- assumed and no analytic Sobolev embedding is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142

reverseHelicalOrthogonality :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.hermitianPairing3
    (Helical.helicalProjectorMinus E I S k value)
    (Helical.helicalProjectorPlus E I S k value)
  ≡ C3.complexZero F
reverseHelicalOrthogonality {F = F} E I S L k value =
  let
    forward = Helical.helicalComponentsStronglyOrthogonal L k value
    symmetry =
      Hermitian.hermitianPairingConjugateSymmetric
        (Helical.helicalProjectorPlus E I S k value)
        (Helical.helicalProjectorMinus E I S k value)
  in
  sym
    (trans
      (cong C3.complexConjugate forward)
      (trans
        (Hermitian.complexConjugateZero F)
        (sym symmetry)))

pairingSumExpansion :
  ∀ {r} {F : C3.RealField r}
    (plus minus : C3.Complex3 F) →
  C3.hermitianPairing3
    (C3.complex3Add plus minus)
    (C3.complex3Add plus minus)
  ≡ C3.complexAdd
      (C3.complexAdd
        (C3.hermitianPairing3 plus plus)
        (C3.hermitianPairing3 plus minus))
      (C3.complexAdd
        (C3.hermitianPairing3 minus plus)
        (C3.hermitianPairing3 minus minus))
pairingSumExpansion plus minus =
  trans
    (Additive.hermitianPairingAddLeft
      plus minus (C3.complex3Add plus minus))
    (cong₂ C3.complexAdd
      (Additive.hermitianPairingAddRight plus plus minus)
      (Additive.hermitianPairingAddRight minus plus minus))

pairingDifferenceExpansion :
  ∀ {r} {F : C3.RealField r}
    (plus minus : C3.Complex3 F) →
  C3.hermitianPairing3
    (C3.complex3Subtract plus minus)
    (C3.complex3Subtract plus minus)
  ≡ C3.complexSubtract
      (C3.complexSubtract
        (C3.hermitianPairing3 plus plus)
        (C3.hermitianPairing3 plus minus))
      (C3.complexSubtract
        (C3.hermitianPairing3 minus plus)
        (C3.hermitianPairing3 minus minus))
pairingDifferenceExpansion plus minus =
  trans
    (Additive.hermitianPairingSubtractLeft
      plus minus (C3.complex3Subtract plus minus))
    (cong₂ C3.complexSubtract
      (Additive.hermitianPairingSubtractRight plus plus minus)
      (Additive.hermitianPairingSubtractRight minus plus minus))

orthogonalSumDifferenceQuadraticEqual :
  ∀ {r} {F : C3.RealField r}
    (plus minus : C3.Complex3 F) →
  C3.hermitianPairing3 plus minus ≡ C3.complexZero F →
  C3.hermitianPairing3 minus plus ≡ C3.complexZero F →
  C3.hermitianPairing3
    (C3.complex3Subtract plus minus)
    (C3.complex3Subtract plus minus)
  ≡ C3.hermitianPairing3
      (C3.complex3Add plus minus)
      (C3.complex3Add plus minus)
orthogonalSumDifferenceQuadraticEqual {F = F}
    plus minus plusMinusZero minusPlusZero =
  let
    pp = C3.hermitianPairing3 plus plus
    mm = C3.hermitianPairing3 minus minus

    differenceReduced :
      C3.complexSubtract
        (C3.complexSubtract pp (C3.complexZero F))
        (C3.complexSubtract (C3.complexZero F) mm)
      ≡ C3.complexAdd pp mm
    differenceReduced =
      R.solve 2
        (λ pp mm →
          ((pp R.⊕ (R.⊝ R.𝟘)) R.⊕
            (R.⊝ (R.𝟘 R.⊕ (R.⊝ mm))))
          R.⊜ pp R.⊕ mm)
        refl pp mm
      where module R = Ring.Solver F

    sumReduced :
      C3.complexAdd
        (C3.complexAdd pp (C3.complexZero F))
        (C3.complexAdd (C3.complexZero F) mm)
      ≡ C3.complexAdd pp mm
    sumReduced =
      R.solve 2
        (λ pp mm →
          ((pp R.⊕ R.𝟘) R.⊕ (R.𝟘 R.⊕ mm))
          R.⊜ pp R.⊕ mm)
        refl pp mm
      where module R = Ring.Solver F
  in
  trans
    (pairingDifferenceExpansion plus minus)
    (trans
      (cong₂ C3.complexSubtract
        (cong₂ C3.complexSubtract refl plusMinusZero)
        (cong₂ C3.complexSubtract minusPlusZero refl))
      (trans
        differenceReduced
        (sym
          (trans
            (cong₂ C3.complexAdd
              (cong₂ C3.complexAdd refl plusMinusZero)
              (cong₂ C3.complexAdd minusPlusZero refl))
            (trans sumReduced (sym (pairingSumExpansion plus minus)))))))

physicalModeHOneEnergy :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  Z3.FourierMode → C3.Complex3 F → C3.Carrier F
physicalModeHOneEnergy {F = F} I k value =
  C3.multiply F
    (C3.normSquared I k)
    (C3.real (C3.hermitianPairing3 value value))

normalizedCurlModeHOneIsometry :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  Helical.Transverse E k value →
  physicalModeHOneEnergy I k (R142.normalizedCurl E S k value)
  ≡ physicalModeHOneEnergy I k value
normalizedCurlModeHOneIsometry {F = F} E I S L H k value transverse =
  let
    plus = Helical.helicalProjectorPlus E I S k value
    minus = Helical.helicalProjectorMinus E I S k value

    diffMeaning :
      C3.complex3Subtract plus minus ≡ R142.normalizedCurl E S k value
    diffMeaning = R142.helicitySignActionIsNormalizedCurl E I S H k value

    sumMeaning : C3.complex3Add plus minus ≡ value
    sumMeaning = Helical.velocityHelicalDecomposition L k value transverse

    plusMinusZero :
      C3.hermitianPairing3 plus minus ≡ C3.complexZero F
    plusMinusZero = Helical.helicalComponentsStronglyOrthogonal L k value

    minusPlusZero :
      C3.hermitianPairing3 minus plus ≡ C3.complexZero F
    minusPlusZero = reverseHelicalOrthogonality E I S L k value

    quadratic :
      C3.hermitianPairing3
        (C3.complex3Subtract plus minus)
        (C3.complex3Subtract plus minus)
      ≡ C3.hermitianPairing3
          (C3.complex3Add plus minus)
          (C3.complex3Add plus minus)
    quadratic =
      orthogonalSumDifferenceQuadraticEqual
        plus minus plusMinusZero minusPlusZero
  in
  trans
    (sym
      (cong (physicalModeHOneEnergy I k) diffMeaning))
    (trans
      (cong
        (λ z → C3.multiply F (C3.normSquared I k) (C3.real z))
        quadratic)
      (cong (physicalModeHOneEnergy I k) sumMeaning))

round246LiteralModewiseNormalizedCurlHOneIsometryClosed : Bool
round246LiteralModewiseNormalizedCurlHOneIsometryClosed = true

round246UsesAbstractHsSquaredNorm : Bool
round246UsesAbstractHsSquaredNorm = false

round246StandardTorusSobolevEmbeddingsInstalled : Bool
round246StandardTorusSobolevEmbeddingsInstalled = false

round246W1PhysicalInterpolationInstalled : Bool
round246W1PhysicalInterpolationInstalled = false

round246PackageAClosed : Bool
round246PackageAClosed = false

round246ClayPromotion : Bool
round246ClayPromotion = false

round246LiteralModewiseNormalizedCurlHOneIsometryClosedIsTrue :
  round246LiteralModewiseNormalizedCurlHOneIsometryClosed ≡ true
round246LiteralModewiseNormalizedCurlHOneIsometryClosedIsTrue = refl

round246UsesAbstractHsSquaredNormIsFalse :
  round246UsesAbstractHsSquaredNorm ≡ false
round246UsesAbstractHsSquaredNormIsFalse = refl

round246PackageAClosedIsFalse : round246PackageAClosed ≡ false
round246PackageAClosedIsFalse = refl

round246ClayPromotionIsFalse : round246ClayPromotion ≡ false
round246ClayPromotionIsFalse = refl
