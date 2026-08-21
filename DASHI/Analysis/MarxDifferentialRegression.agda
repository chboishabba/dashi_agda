module DASHI.Analysis.MarxDifferentialRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxPolynomialDifferential
open import DASHI.Analysis.MarxPowerRuleNormalisation
open import DASHI.Analysis.MarxReciprocalQuotientNormalisation
open import DASHI.Analysis.MarxOrdinaryDerivativeBridge
open import DASHI.Analysis.MarxHigherCalculus
open import DASHI.Analysis.MarxFrechetProduct
open import DASHI.Analysis.MarxExteriorIntegration
open import DASHI.Governance.GeopoliticalDifferentialEvidence

------------------------------------------------------------------------
-- A one-point exact model exercises every constructor without claiming that
-- the terminal carrier is the ordinary real line.  Nondegeneracy remains a
-- separate proof obligation in MarxFastCauchyCompletionCutset.

terminalAlgebra : MarxAlgebra
terminalAlgebra =
  record
    { Carrier = ⊤
    ; zero = tt
    ; one = tt
    ; _+_ = λ _ _ → tt
    ; _-_ = λ _ _ → tt
    ; _*_ = λ _ _ → tt
    ; subSelf = λ _ → refl
    ; mulZeroRight = λ _ → refl
    ; mulOneRight = λ _ → refl
    ; mulAssoc = λ _ _ _ → refl
    ; addDifferenceFactor = λ _ _ → refl
    ; productDifferenceFactor = λ _ _ → refl
    }

terminalConstantReceipt :
  MarxFactorisation terminalAlgebra (constantFunction tt)
terminalConstantReceipt = constantFactorisation tt

terminalIdentityReceipt :
  MarxFactorisation terminalAlgebra identityFunction
terminalIdentityReceipt = identityFactorisation

terminalSumReceipt :
  MarxFactorisation terminalAlgebra
    (addFunctions identityFunction (constantFunction tt))
terminalSumReceipt =
  addFactorisations terminalIdentityReceipt terminalConstantReceipt

terminalProductReceipt :
  MarxFactorisation terminalAlgebra
    (multiplyFunctions identityFunction identityFunction)
terminalProductReceipt =
  productFactorisations terminalIdentityReceipt terminalIdentityReceipt

terminalChainReceipt :
  MarxFactorisation terminalAlgebra
    (compose identityFunction identityFunction)
terminalChainReceipt =
  chainFactorisation terminalIdentityReceipt terminalIdentityReceipt

terminalPowerTwoReceipt :
  MarxFactorisation terminalAlgebra (powerFunction (suc (suc zero)))
terminalPowerTwoReceipt = powerFactorisation (suc (suc zero))

------------------------------------------------------------------------
-- Power normalisation constructed from algebra laws.

terminalPowerAlgebraLaws : MarxPowerAlgebraLaws terminalAlgebra
terminalPowerAlgebraLaws =
  record
    { addZeroLeftLaw = λ _ → refl
    ; addZeroRightLaw = λ _ → refl
    ; addAssocLaw = λ _ _ _ → refl
    ; mulCommLaw = λ _ _ → refl
    ; distribRightLaw = λ _ _ _ → refl
    }

terminalPowerNormalisation :
  PowerRuleNormalisation terminalAlgebra
terminalPowerNormalisation =
  powerRuleNormalisationFromLaws terminalPowerAlgebraLaws

terminalPowerRule :
  marxDerivative terminalPowerTwoReceipt tt ≡ tt
terminalPowerRule =
  powerDerivativeNatScale terminalPowerAlgebraLaws (suc zero) tt

terminalPolynomial : Polynomial terminalAlgebra
terminalPolynomial =
  (varTerm *P varTerm) +P constant tt

terminalPolynomialReceipt :
  MarxFactorisation terminalAlgebra (interpret terminalPolynomial)
terminalPolynomialReceipt = polynomialFactorisation terminalPolynomial

terminalPolynomialDerivativeCommutes :
  polynomialDerivative terminalPolynomial tt
  ≡ interpret (formalPolynomialDerivative terminalPolynomial) tt
terminalPolynomialDerivativeCommutes =
  polynomialDerivativeInterpretationCommutes terminalPolynomial tt

terminalRawDiagonalImpossible :
  RawDiagonalQuotient terminalAlgebra identityFunction tt →
  ⊥
terminalRawDiagonalImpossible = rawDiagonalQuotientImpossible

------------------------------------------------------------------------
-- Reciprocal and quotient regression.

terminalReciprocalLaws : MarxReciprocalLaws terminalAlgebra
terminalReciprocalLaws =
  record
    { Nonzero = λ _ → ⊤
    ; neg = λ _ → tt
    ; reciprocal = λ _ → tt
    ; reciprocalNonzero = λ _ → tt
    ; mulReciprocalLeft = λ _ _ → refl
    ; mulReciprocalRight = λ _ _ → refl
    ; reciprocalDifferenceIdentity = λ _ _ _ _ → refl
    ; reciprocalDifferenceFactor = λ _ _ _ → refl
    ; reciprocalDiagonalNormalisation = λ _ _ _ → refl
    }

terminalEverywhereNonzero :
  (x : ⊤) → Nonzero terminalReciprocalLaws x
terminalEverywhereNonzero x = tt

terminalReciprocalReceipt :
  MarxFactorisation terminalAlgebra
    (reciprocalFunction terminalReciprocalLaws identityFunction)
terminalReciprocalReceipt =
  reciprocalMarxFactorisation
    terminalReciprocalLaws
    terminalIdentityReceipt
    terminalEverywhereNonzero

terminalQuotientNormalisation :
  QuotientDenominatorSquareNormalisation terminalReciprocalLaws
terminalQuotientNormalisation =
  record { quotientNumeratorNormalisation = λ _ _ _ _ _ _ → refl }

terminalQuotientRule :
  marxDerivative
    (quotientFactorisationCanonical
      terminalReciprocalLaws
      terminalIdentityReceipt
      terminalIdentityReceipt
      terminalEverywhereNonzero)
    tt
  ≡ tt
terminalQuotientRule =
  quotientRule
    terminalReciprocalLaws
    terminalQuotientNormalisation
    terminalIdentityReceipt
    terminalIdentityReceipt
    terminalEverywhereNonzero
    tt

------------------------------------------------------------------------
-- Little-o compatibility regression.

terminalRemainderStructure : RemainderDerivativeStructure terminalAlgebra
terminalRemainderStructure =
  record
    { Nonzero = λ _ → ⊤
    ; normaliseRemainder = λ _ _ → tt
    ; TendsToZeroPunctured = λ _ → ⊤
    ; puncturedCongruence = λ _ _ → tt
    ; normalizedProductCancellation = λ _ _ _ → refl
    ; zeroTendsToZero = tt
    }

terminalRemainderExpansion : MarxRemainderExpansionLaws terminalAlgebra
terminalRemainderExpansion =
  record { factorisationToRemainderExpansion = λ _ _ _ → refl }

terminalDerivativeUniqueness :
  OrdinaryDerivativeUniqueness terminalRemainderStructure
terminalDerivativeUniqueness =
  record { uniqueLinearCoefficient = λ _ _ → refl }

terminalDiagonalContinuous :
  PreliminaryContinuousAtDiagonal
    terminalRemainderStructure
    terminalIdentityReceipt
    tt
terminalDiagonalContinuous = tt

terminalOrdinaryIdentityDerivative :
  OrdinaryDerivativeAt
    terminalRemainderStructure
    identityFunction
    tt
terminalOrdinaryIdentityDerivative =
  marxFactorisationAndDiagonalContinuityGiveOrdinaryDerivative
    terminalRemainderStructure
    terminalRemainderExpansion
    terminalIdentityReceipt
    tt
    terminalDiagonalContinuous

terminalMarxEqualsOrdinary :
  marxDerivative terminalIdentityReceipt tt
  ≡ linearCoefficient terminalOrdinaryIdentityDerivative
terminalMarxEqualsOrdinary =
  marxDerivativeEqualsOrdinaryDerivative
    terminalRemainderExpansion
    terminalDerivativeUniqueness
    terminalIdentityReceipt
    tt
    terminalDiagonalContinuous
    terminalOrdinaryIdentityDerivative

------------------------------------------------------------------------
-- Genuine module/linear/Frechet regression.

terminalModule : Module terminalAlgebra
terminalModule =
  record
    { Vector = ⊤
    ; zeroV = tt
    ; _+V_ = λ _ _ → tt
    ; _•_ = λ _ _ → tt
    ; addZeroLeftV = λ _ → refl
    ; addZeroRightV = λ _ → refl
    ; addAssocV = λ _ _ _ → refl
    ; scaleZeroV = λ _ → refl
    ; scaleOneV = λ _ → refl
    ; scaleDistributesAddV = λ _ _ _ → refl
    }

terminalVectorLittleO :
  VectorLittleOStructure terminalAlgebra terminalModule terminalModule
terminalVectorLittleO =
  record
    { LittleO = λ _ → ⊤
    ; zeroLittleO = tt
    ; addLittleO = λ _ _ → tt
    }

terminalFrechetIdentity :
  FrechetDerivativeAt terminalVectorLittleO (λ x → x) tt
terminalFrechetIdentity =
  frechetIdentity terminalVectorLittleO tt

terminalDirectionalIdentity :
  DirectionalDerivativeAt terminalFrechetIdentity tt ≡ tt
terminalDirectionalIdentity = refl

terminalBilinearProduct :
  BilinearProduct terminalAlgebra terminalModule
terminalBilinearProduct =
  record
    { product = λ _ _ → tt
    ; productZeroLeft = λ _ → refl
    ; productZeroRight = λ _ → refl
    ; productAddLeft = λ _ _ _ → refl
    ; productAddRight = λ _ _ _ → refl
    ; productScaleLeft = λ _ _ _ → refl
    ; productScaleRight = λ _ _ _ → refl
    }

terminalFrechetProductConstruction :
  FrechetProductConstruction
    terminalVectorLittleO
    terminalBilinearProduct
    terminalFrechetIdentity
    terminalFrechetIdentity
terminalFrechetProductConstruction =
  record
    { productLinear = linearIdentity terminalModule
    ; productLinearPointwise = λ _ → refl
    ; productRemainder = λ _ → tt
    ; productExpansion = λ _ → refl
    ; productRemainderLittleO = tt
    }

terminalFrechetProduct :
  FrechetDerivativeAt
    terminalVectorLittleO
    (multiplyVectorFunctions terminalBilinearProduct (λ x → x) (λ x → x))
    tt
terminalFrechetProduct =
  frechetProduct
    terminalBilinearProduct
    terminalFrechetIdentity
    terminalFrechetIdentity
    terminalFrechetProductConstruction

------------------------------------------------------------------------
-- Genuine d²=0 target and finite integration regression.

terminalForms : GradedDifferentialForms terminalAlgebra terminalModule
terminalForms =
  record
    { Form = λ _ → ⊤
    ; zeroForm = λ _ → tt
    ; asAlternatingMap = λ _ →
        record
          { evaluate = λ _ → tt
          ; acceptedArity = λ _ → ⊤
          ; multilinearAdd = λ _ _ _ _ _ → refl
          ; multilinearScale = λ _ _ _ _ _ → refl
          ; alternatingAdjacent = λ _ _ _ _ → refl
          }
    }

terminalExteriorDerivative : ExteriorDerivative terminalForms
terminalExteriorDerivative = zeroExteriorDerivative terminalForms

terminalDSquaredZero :
  ExteriorDerivative.d terminalExteriorDerivative
    (ExteriorDerivative.d terminalExteriorDerivative tt)
  ≡ GradedDifferentialForms.zeroForm terminalForms (suc (suc zero))
terminalDSquaredZero =
  exteriorDerivativeSquaredZero terminalExteriorDerivative tt

terminalIntegral : RiemannIntegralStructure terminalAlgebra
terminalIntegral =
  record
    { _≤I_ = λ _ _ → ⊤
    ; IntegrableOn = λ _ _ → ⊤
    ; integral = λ _ _ → tt
    ; integralConstant = λ _ _ → refl
    ; integralAdd = λ _ _ _ _ _ → refl
    ; integralScale = λ _ _ _ _ → refl
    ; integralOrder = λ _ _ _ _ _ _ → tt
    ; intervalAdditivity = λ _ _ _ _ _ _ _ → refl
    }

------------------------------------------------------------------------
-- Legal-status non-collapse regression.

terminalNoFinalMeritsFromProvisional :
  FinalMeritsStatus provisionalMeasures → ⊥
terminalNoFinalMeritsFromProvisional =
  provisionalOrderDoesNotEntailFinalMeritsJudgment
