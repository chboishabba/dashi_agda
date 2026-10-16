module DASHI.Unified.TOEArithmeticCMRealizationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unified.TOESectorRealizationExact
import DASHI.Unified.TOE369C3RealizationGraphExact as C3

record ArithmeticCMPayment : Set where
  field
    eisensteinNormShellPaid : Bool
    dirichletFactorisationPaid : Bool
    jZeroPointGroupActionPaid : Bool
    eisensteinOrderActionPaid : Bool
    inertSamePrimeEulerPaid : Bool
    genericCubicJacobiCompilerPaid : Bool

    canonicalCubeFibreCertificatePaid : Bool
    jacobiToSelectedEisensteinPrimePaid : Bool
    splitPrimeFrobeniusPaid : Bool
    allGoodPrimeAgreementPaid : Bool
    sameCurveHeckeGroessencharacterPaid : Bool
    ellipticHeckeLSeriesAgreementPaid : Bool

    leanAuthority : String

currentArithmeticCMPayment : ArithmeticCMPayment
currentArithmeticCMPayment =
  record
    { eisensteinNormShellPaid = true
    ; dirichletFactorisationPaid = true
    ; jZeroPointGroupActionPaid = true
    ; eisensteinOrderActionPaid = true
    ; inertSamePrimeEulerPaid = true
    ; genericCubicJacobiCompilerPaid = true
    ; canonicalCubeFibreCertificatePaid = false
    ; jacobiToSelectedEisensteinPrimePaid = false
    ; splitPrimeFrobeniusPaid = false
    ; allGoodPrimeAgreementPaid = false
    ; sameCurveHeckeGroessencharacterPaid = false
    ; ellipticHeckeLSeriesAgreementPaid = false
    ; leanAuthority =
        "Lean PR #69: exact same-carrier Z[omega] -> j=0 point-group action and same-prime inert local Euler factor are source-written; generic cubic/Jacobi compiler is paid. Split cube-fibre certificate, selected Eisenstein-prime Jacobi evaluation, split Frobenius and same-curve Hecke/Groessencharacter remain open. This Agda owner imports that source status, not its proof object."
    }

arithmeticCMGrade : ValidationGrade
arithmeticCMGrade = representationIntertwiner

arithmeticCMObligations : List RealizationObligation
arithmeticCMObligations =
  dynamicsEquivariance
  ∷ actionHamiltonianAgreement
  ∷ scaleCalibrationAgreement
  ∷ empiricalSameObjectAttachment
  ∷ []

record ArithmeticCMRealization : Set where
  field
    universalC3ToOmega : C3.C3Edge
    payments : ArithmeticCMPayment
    attainedGrade : ValidationGrade
    unpaid : List RealizationObligation
    spectralPhysicalPromotion : Bool
    spectralPhysicalPromotionIsFalse : spectralPhysicalPromotion ≡ false
    reading : String

canonicalArithmeticCMRealization : ArithmeticCMRealization
canonicalArithmeticCMRealization =
  record
    { universalC3ToOmega = C3.eisensteinUniversalCharacter
    ; payments = currentArithmeticCMPayment
    ; attainedGrade = arithmeticCMGrade
    ; unpaid = arithmeticCMObligations
    ; spectralPhysicalPromotion = false
    ; spectralPhysicalPromotionIsFalse = refl
    ; reading =
        "HAM candidate: Eisenstein omega/j=0 CM is a literal arithmetic/spectral realization of universal C3. The same Z[omega] carrier and inert same-prime local factor make this more than a character coincidence. The decisive higher lift is split-prime Frobenius plus a same-curve Hecke/Groessencharacter and L-series transport; no arithmetic 6*zeta*L(chi_-3) identity is silently relabelled as the elliptic L-function."
    }
