module DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact where

------------------------------------------------------------------------
-- ROUND142 / HELICITY-SIGN ACTION IS NORMALIZED CURL
--
-- Sources:
--   Zhen Lei; Fang-Hua Lin; Yi Zhou,
--   "Structure of Helicity and Global Solutions of Incompressible
--   Navier-Stokes Equation", ARMA 218 (2015), DOI 10.1007/s00205-015-0884-8.
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--
-- Round140/141 identify the three first Walsh moments with insertion of
--
--     h_j = u_j^+ - u_j^-.
--
-- The periodic helical projector definitions already present in the repository
-- give, purely algebraically,
--
--     P_+ u = h (P u + |D|^-1 curl u),
--     P_- u = h (P u - |D|^-1 curl u).
--
-- If the scalar called `half` is calibrated by h+h=1, subtraction cancels the
-- Leray part exactly and therefore
--
--     P_+ u - P_- u = |D|^-1 curl u.
--
-- No curl-eigenvalue assumption is needed for this identity: it follows from
-- the projector formulas themselves.  This is the exact physical meaning of
-- the helicity-sign difference used by the Walsh reduction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical

record HelicalHalfCalibration
    {r} {F : C3.RealField r}
    (S : Helical.HelicalModeScalars F) : Set r where
  constructor helical-half-calibration
  field
    halfPlusHalfIsOne :
      C3.add F (Helical.half S) (Helical.half S) ≡ C3.one F

open HelicalHalfCalibration public

normalizedCurl :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F) →
  Z3.FourierMode → C3.Complex3 F → C3.Complex3 F
normalizedCurl {F = F} E S k value =
  C3.complex3Scale
    (C3.realEmbed F (Helical.inverseModeNorm S k))
    (Helical.curlSymbol E k value)

helicitySignAction :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F) →
  Z3.FourierMode → C3.Complex3 F → C3.Complex3 F
helicitySignAction E I S k value =
  C3.complex3Subtract
    (Helical.helicalProjectorPlus E I S k value)
    (Helical.helicalProjectorMinus E I S k value)

-- Generic vector identity behind the projector cancellation.
halfDifferenceCancellation :
  ∀ {r} {F : C3.RealField r}
    (h : C3.Carrier F) →
  C3.add F h h ≡ C3.one F →
  (a b : C3.Complex3 F) →
  C3.complex3Subtract
    (C3.complex3Scale (C3.realEmbed F h) (C3.complex3Add a b))
    (C3.complex3Scale (C3.realEmbed F h) (C3.complex3Subtract a b))
  ≡ b
halfDifferenceCancellation {F = F} h calibration
    (C3.complex3 ax ay az) (C3.complex3 bx by bz) =
  Field.complex3Ext
    (coordinate ax bx)
    (coordinate ay by)
    (coordinate az bz)
  where
  hC = C3.realEmbed F h

  twiceHComplex :
    C3.complexAdd hC hC ≡ C3.complexOne F
  twiceHComplex =
    cong (C3.realEmbed F) calibration

  coordinate :
    (a b : C3.Complex F) →
    C3.complexSubtract
      (C3.complexMultiply hC (C3.complexAdd a b))
      (C3.complexMultiply hC (C3.complexSubtract a b))
    ≡ b
  coordinate a b =
    trans
      (R.solve 3
        (λ h a b →
          ((h R.⊗ (a R.⊕ b))
            R.⊕ (R.⊝ (h R.⊗ (a R.⊕ (R.⊝ b)))))
          R.⊜ (h R.⊕ h) R.⊗ b)
        refl hC a b)
      (trans
        (cong (λ scalar → C3.complexMultiply scalar b) twiceHComplex)
        (C3.complexMultiplyOneLeft F b))
    where module R = Ring.Solver F

helicitySignActionIsNormalizedCurl :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (H : HelicalHalfCalibration S)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  helicitySignAction E I S k value
  ≡ normalizedCurl E S k value
helicitySignActionIsNormalizedCurl {F = F} E I S H k value =
  halfDifferenceCancellation
    (Helical.half S)
    (halfPlusHalfIsOne H)
    (C3.lerayProject3 E I k value)
    (normalizedCurl E S k value)

round142HelicitySignActionNormalizedCurlClosed : Bool
round142HelicitySignActionNormalizedCurlClosed = true

round142UsesCurlEigenmodeAssumption : Bool
round142UsesCurlEigenmodeAssumption = false

round142PackageAClosed : Bool
round142PackageAClosed = false

round142HelicitySignActionNormalizedCurlClosedIsTrue :
  round142HelicitySignActionNormalizedCurlClosed ≡ true
round142HelicitySignActionNormalizedCurlClosedIsTrue = refl

round142UsesCurlEigenmodeAssumptionIsFalse :
  round142UsesCurlEigenmodeAssumption ≡ false
round142UsesCurlEigenmodeAssumptionIsFalse = refl

round142PackageAClosedIsFalse : round142PackageAClosed ≡ false
round142PackageAClosedIsFalse = refl
