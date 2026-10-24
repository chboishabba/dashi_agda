module DASHI.Unified.TOEArithmeticCMRealizationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unified.TOESectorRealizationExact
import DASHI.Unified.TOE369C3RealizationGraphExact as C3
import DASHI.Unified.TOEConcreteInhabitantsExact as Inhabitants

record ArithmeticCMPayment : Set where
  field
    eisensteinNormShellPaid : Bool
    dirichletFactorisationPaid : Bool
    jZeroPointGroupActionPaid : Bool
    eisensteinOrderActionPaid : Bool
    inertSamePrimeEulerPaid : Bool
    primarySplitNormalizationPaid : Bool
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
    ; primarySplitNormalizationPaid = true
    ; genericCubicJacobiCompilerPaid = true
    ; canonicalCubeFibreCertificatePaid = false
    ; jacobiToSelectedEisensteinPrimePaid = false
    ; splitPrimeFrobeniusPaid = false
    ; allGoodPrimeAgreementPaid = false
    ; sameCurveHeckeGroessencharacterPaid = false
    ; ellipticHeckeLSeriesAgreementPaid = false
    ; leanAuthority =
        "Lean PR #73 strengthens #69 with an actual nonsingular j=0 elliptic point-group endomorphism over Q(omega), full inert-prime Euler family, unique primary split-prime normalization, and exact Frobenius trace/quadratic-character-sum identity. The cubic/Jacobi evaluation, split Frobenius and same-curve Hecke/Groessencharacter remain live. This Agda owner imports those theorem values only as formal-source inhabitants."
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
    cmPointGroupFormalInhabitant : Inhabitants.FormalInhabitantReceipt
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
    ; cmPointGroupFormalInhabitant = Inhabitants.lean73CMInhabitant
    ; payments = currentArithmeticCMPayment
    ; attainedGrade = arithmeticCMGrade
    ; unpaid = arithmeticCMObligations
    ; spectralPhysicalPromotion = false
    ; spectralPhysicalPromotionIsFalse = refl
    ; reading =
        "HAM candidate: Eisenstein omega/j=0 CM is a literal arithmetic/spectral realization of universal C3. The TOE now carries an actual imported formal inhabitant for the order-three elliptic point-group endomorphism, rather than a paid-status Boolean alone. The remaining higher lift is the classical cubic/Jacobi split-prime evaluation, split Frobenius, same-curve Hecke/Groessencharacter and L-series transport; none of those is inferred from the existing point-group inhabitant."
    }
