module DASHI.Analysis.RiemannG21OddTaylorQuantitativeFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SupportMomentDominationExact as Support
import DASHI.Analysis.RiemannG21ActualTaperOddMomentSupportExact as ActualMoments
import DASHI.Analysis.RiemannG21OddMomentRatioGapExact as RatioGap
import DASHI.Analysis.RiemannG21MathlibSineTaylorReceiptBoundary as SineReceipt
import DASHI.Analysis.RiemannG21OddTaylorDeterminantExact as Taylor
import DASHI.Analysis.RiemannG21OddTaylorRemainderDeterminantExact as Remainder
import DASHI.Analysis.RiemannG21OddTaylorOrderBudgetExact as Order
import DASHI.Analysis.RiemannG21OddTaylorSourceBudgetBoundary as Source
import DASHI.Analysis.RiemannG21OddTaylorDeterminantConstantExact as Constant
import DASHI.Analysis.RiemannG21OddTaylorNormalizedRadiusGateExact as Normalized
import DASHI.Analysis.RiemannG21DeterminantMarginTransferExact as Margin

data OddTaylorQuantitativeArrow : Set where
  compactSupportAndPositivity : OddTaylorQuantitativeArrow
  actualOddMomentSupportSpecialization : OddTaylorQuantitativeArrow
  supportMomentDomination : OddTaylorQuantitativeArrow
  mathlibSineTaylorInfrastructure : OddTaylorQuantitativeArrow
  fifthOrderSineRemainder : OddTaylorQuantitativeArrow
  integratedOddR5Remainder : OddTaylorQuantitativeArrow
  strictNormalizedRatioGap : OddTaylorQuantitativeArrow
  doubleRadiusCubicSignal : OddTaylorQuantitativeArrow
  exactSixTermDeterminantError : OddTaylorQuantitativeArrow
  radiusDegreeGapTwo : OddTaylorQuantitativeArrow
  explicitDeterminantErrorCoefficient : OddTaylorQuantitativeArrow
  massNormalizedErrorPolynomial : OddTaylorQuantitativeArrow
  supportOnlyErrorPolynomial : OddTaylorQuantitativeArrow
  determinantR6Inequality : OddTaylorQuantitativeArrow
  divisionFreeSmallRadiusGate : OddTaylorQuantitativeArrow
  finiteOddMinorSign : OddTaylorQuantitativeArrow

data QuantitativeStatus : Set where
  sourceAudited structurallyDerived analyticOpen : QuantitativeStatus

record QuantitativeEntry : Set where
  constructor quantitativeEntry
  field
    arrow : OddTaylorQuantitativeArrow
    status : QuantitativeStatus
    reading : String

supportEntry : QuantitativeEntry
supportEntry = quantitativeEntry
  compactSupportAndPositivity sourceAudited
  "The companion taper owners prove 0<=phi<=1, supp(phi) subset [-L/2,L/2], compact support, integrability and integral phi<=L."

actualMomentSpecializationEntry : QuantitativeEntry
actualMomentSpecializationEntry = quantitativeEntry
  actualOddMomentSupportSpecialization structurallyDerived
  "RiemannG21ActualTaperOddMomentSupportExact now states the actual N1/N3/N5 specialization at support radius R=L/2 and keeps positivity plus ordered-integral domination as explicit producers."

supportMomentEntry : QuantitativeEntry
supportMomentEntry = quantitativeEntry
  supportMomentDomination analyticOpen
  "Use the positive common odd weight on 0<=u<=R=L/2 to prove N3(y)<=R^2 N1(y) and N5(y)<=R^4 N1(y). The generic theorem shape and actual-taper specialization are now both explicit."

sineInfrastructureEntry : QuantitativeEntry
sineInfrastructureEntry = quantitativeEntry
  mathlibSineTaylorInfrastructure sourceAudited
  "Mathlib owns Real.hasSum_sin / Real.sin_eq_tsum and general Lagrange/Taylor remainder machinery. This locates a machine-checked proof route but does not count the specialized fifth-order inequality as transported."

sineRemainderEntry : QuantitativeEntry
sineRemainderEntry = quantitativeEntry
  fifthOrderSineRemainder analyticOpen
  "Specialize the source-audited Taylor machinery to |sin x - x + x^3/6| <= |x|^5/120. The specialized proof term is still absent from this branch."

integratedRemainderEntry : QuantitativeEntry
integratedRemainderEntry = quantitativeEntry
  integratedOddR5Remainder analyticOpen
  "Integrate the pointwise sine remainder against the positive compactly supported taper to obtain the six-scaled bound |E_y(r)| <= |r|^5 N5(y)/20."

ratioGapEntry : QuantitativeEntry
ratioGapEntry = quantitativeEntry
  strictNormalizedRatioGap analyticOpen
  "Convert the strict cross-multiplied TP2 moment sign to qp>qa using N1(a),N1(p)>0. The rational mass factorization is derived, while ordered-field division/cancellation remains explicit."

doubleRadiusEntry : QuantitativeEntry
doubleRadiusEntry = quantitativeEntry
  doubleRadiusCubicSignal structurallyDerived
  "For r1=r and r2=2r, rational ring normalization gives the cubic odd determinant exactly as -36 r^4 Delta_odd."

sixTermEntry : QuantitativeEntry
sixTermEntry = quantitativeEntry
  exactSixTermDeterminantError structurallyDerived
  "The actual determinant minus the cubic determinant is exactly the six-term bilinear truncation/remainder expression owned by RiemannG21OddTaylorRemainderDeterminantExact."

degreeGapEntry : QuantitativeEntry
degreeGapEntry = quantitativeEntry
  radiusDegreeGapTwo structurallyDerived
  "Signal radius degree is 4 while the first determinant remainder terms have degree at least 6; hence the relative error starts two powers of the sample-radius scale later."

coefficientEntry : QuantitativeEntry
coefficientEntry = quantitativeEntry
  explicitDeterminantErrorCoefficient structurallyDerived
  "RiemannG21OddTaylorDeterminantConstantExact constructs a concrete rational C_det coefficient from the r and 2r truncation constants and the two fifth-order remainder coefficients."

normalizedEntry : QuantitativeEntry
normalizedEntry = quantitativeEntry
  massNormalizedErrorPolynomial structurallyDerived
  "Both Delta_odd and C_det factor through N1(a)N1(p); rational ring normalization constructs the mass-free error polynomial P(qa,qp,ca,cp) and the ratio gap qp-qa."

supportPolynomialEntry : QuantitativeEntry
supportPolynomialEntry = quantitativeEntry
  supportOnlyErrorPolynomial structurallyDerived
  "After the target bounds qa,qp<=R^2 and ca,cp<=R^4/20, the support-only polynomial is 25P <= 510R^4+100R^6+4R^8. The polynomial is constructed; the ordered-real majorization remains open."

r6InequalityEntry : QuantitativeEntry
r6InequalityEntry = quantitativeEntry
  determinantR6Inequality analyticOpen
  "Prove the six exact determinant-error terms are bounded by the constructed C_det r^6 using the actual taper support-moment and fifth-order remainder bounds for 0<r<=1."

smallRadiusEntry : QuantitativeEntry
smallRadiusEntry = quantitativeEntry
  divisionFreeSmallRadiusGate analyticOpen
  "A support-only sufficient gate is (510R^4+100R^6+4R^8) r^2 < 900(qp-qa), with R=L/2. This is mass-free and division-free once qp-qa>0 is supplied."

finiteSignEntry : QuantitativeEntry
finiteSignEntry = quantitativeEntry
  finiteOddMinorSign analyticOpen
  "Combine the strict normalized ratio gap, exact -36r^4 signal, and determinant R6 bound to obtain the actual finite-radius odd minor with preserved strict sign."

canonicalOddTaylorQuantitativeFrontier : List QuantitativeEntry
canonicalOddTaylorQuantitativeFrontier =
  supportEntry ∷ actualMomentSpecializationEntry ∷ supportMomentEntry
  ∷ sineInfrastructureEntry ∷ sineRemainderEntry ∷ integratedRemainderEntry
  ∷ ratioGapEntry ∷ doubleRadiusEntry ∷ sixTermEntry ∷ degreeGapEntry
  ∷ coefficientEntry ∷ normalizedEntry ∷ supportPolynomialEntry
  ∷ r6InequalityEntry ∷ smallRadiusEntry ∷ finiteSignEntry ∷ []

supportBoundary : Support.SupportMomentDominationBoundary
supportBoundary = Support.canonicalSupportMomentDominationBoundary

actualMomentBoundary : ActualMoments.ActualTaperOddMomentBoundary
actualMomentBoundary = ActualMoments.canonicalActualTaperOddMomentBoundary

ratioGapBoundary : RatioGap.OddRatioGapBoundary
ratioGapBoundary = RatioGap.canonicalOddRatioGapBoundary

sineReceiptBoundary : SineReceipt.MathlibSineTaylorBoundary
sineReceiptBoundary = SineReceipt.canonicalMathlibSineTaylorBoundary

sourceBoundary : Source.OddTaylorSourceBudgetBoundary
sourceBoundary = Source.canonicalOddTaylorSourceBudgetBoundary

taylorBoundary : Taylor.OddTaylorDeterminantBoundary
taylorBoundary = Taylor.canonicalOddTaylorDeterminantBoundary

remainderBoundary : Remainder.OddTaylorRemainderBoundary
remainderBoundary = Remainder.canonicalOddTaylorRemainderBoundary

orderBudget : Order.OddTaylorOrderBudget
orderBudget = Order.canonicalOddTaylorOrderBudget

constantBoundary : Constant.OddDeterminantConstantBoundary
constantBoundary = Constant.canonicalOddDeterminantConstantBoundary

normalizedBoundary : Normalized.NormalizedRadiusGateBoundary
normalizedBoundary = Normalized.canonicalNormalizedRadiusGateBoundary

marginBoundary : Margin.DeterminantMarginBoundary
marginBoundary = Margin.canonicalDeterminantMarginBoundary

record OddTaylorQuantitativeBoundary : Set where
  constructor oddTaylorQuantitativeBoundary
  field
    taperSupportFactsAvailable : Bool
    taperSupportFactsAvailableIsTrue : taperSupportFactsAvailable ≡ true
    actualOddMomentSpecializationConstructed : Bool
    actualOddMomentSpecializationConstructedIsTrue : actualOddMomentSpecializationConstructed ≡ true
    mathlibSineTaylorInfrastructureLocated : Bool
    mathlibSineTaylorInfrastructureLocatedIsTrue : mathlibSineTaylorInfrastructureLocated ≡ true
    doubleRadiusCoefficient36Derived : Bool
    doubleRadiusCoefficient36DerivedIsTrue : doubleRadiusCoefficient36Derived ≡ true
    exactSixTermErrorDerived : Bool
    exactSixTermErrorDerivedIsTrue : exactSixTermErrorDerived ≡ true
    relativeErrorDegreeGapTwoDerived : Bool
    relativeErrorDegreeGapTwoDerivedIsTrue : relativeErrorDegreeGapTwoDerived ≡ true
    explicitDeterminantErrorCoefficientConstructed : Bool
    explicitDeterminantErrorCoefficientConstructedIsTrue : explicitDeterminantErrorCoefficientConstructed ≡ true
    massNormalizedErrorPolynomialDerived : Bool
    massNormalizedErrorPolynomialDerivedIsTrue : massNormalizedErrorPolynomialDerived ≡ true
    supportOnlyPolynomialConstructed : Bool
    supportOnlyPolynomialConstructedIsTrue : supportOnlyPolynomialConstructed ≡ true
    actualSupportMomentDominationDerived : Bool
    actualSupportMomentDominationDerivedIsFalse : actualSupportMomentDominationDerived ≡ false
    specializedFifthOrderSineRemainderDerived : Bool
    specializedFifthOrderSineRemainderDerivedIsFalse : specializedFifthOrderSineRemainderDerived ≡ false
    actualPositiveRatioGapDerived : Bool
    actualPositiveRatioGapDerivedIsFalse : actualPositiveRatioGapDerived ≡ false
    determinantR6InequalityDerived : Bool
    determinantR6InequalityDerivedIsFalse : determinantR6InequalityDerived ≡ false
    explicitSmallRadiusGateDerived : Bool
    explicitSmallRadiusGateDerivedIsFalse : explicitSmallRadiusGateDerived ≡ false
    finiteOddMinorSignDerived : Bool
    finiteOddMinorSignDerivedIsFalse : finiteOddMinorSignDerived ≡ false

canonicalOddTaylorQuantitativeBoundary : OddTaylorQuantitativeBoundary
canonicalOddTaylorQuantitativeBoundary =
  oddTaylorQuantitativeBoundary
    true refl true refl true refl
    true refl true refl true refl true refl true refl true refl
    false refl false refl false refl false refl false refl false refl
