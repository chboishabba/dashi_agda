module DASHI.Analysis.RiemannG21OddTaylorQuantitativeFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG21OddTaylorDeterminantExact as Taylor
import DASHI.Analysis.RiemannG21OddTaylorRemainderDeterminantExact as Remainder
import DASHI.Analysis.RiemannG21OddTaylorOrderBudgetExact as Order
import DASHI.Analysis.RiemannG21OddTaylorSourceBudgetBoundary as Source
import DASHI.Analysis.RiemannG21OddTaylorDeterminantConstantExact as Constant
import DASHI.Analysis.RiemannG21DeterminantMarginTransferExact as Margin

data OddTaylorQuantitativeArrow : Set where
  compactSupportAndPositivity : OddTaylorQuantitativeArrow
  fifthOrderSineRemainder : OddTaylorQuantitativeArrow
  integratedOddR5Remainder : OddTaylorQuantitativeArrow
  doubleRadiusCubicSignal : OddTaylorQuantitativeArrow
  exactSixTermDeterminantError : OddTaylorQuantitativeArrow
  radiusDegreeGapTwo : OddTaylorQuantitativeArrow
  explicitDeterminantErrorCoefficient : OddTaylorQuantitativeArrow
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

sineRemainderEntry : QuantitativeEntry
sineRemainderEntry = quantitativeEntry
  fifthOrderSineRemainder analyticOpen
  "Discharge |sin x - x + x^3/6| <= |x|^5/120, preferably from an existing Mathlib power-series/Taylor theorem or a tiny approved companion proof."

integratedRemainderEntry : QuantitativeEntry
integratedRemainderEntry = quantitativeEntry
  integratedOddR5Remainder analyticOpen
  "Integrate the pointwise sine remainder against the positive compactly supported taper to obtain the six-scaled bound |E_y(r)| <= |r|^5 N5(y)/20."

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

r6InequalityEntry : QuantitativeEntry
r6InequalityEntry = quantitativeEntry
  determinantR6Inequality analyticOpen
  "Prove the six exact determinant-error terms are bounded in magnitude by the constructed C_det r^6 using the actual taper N5 bounds and 0<r<=1."

smallRadiusEntry : QuantitativeEntry
smallRadiusEntry = quantitativeEntry
  divisionFreeSmallRadiusGate analyticOpen
  "Choose r>0 satisfying C_det r^2 < 36 Delta_odd. This is the exact division-free sign-preservation condition after canceling the common r^4 scale."

finiteSignEntry : QuantitativeEntry
finiteSignEntry = quantitativeEntry
  finiteOddMinorSign analyticOpen
  "Combine the strict continuum odd margin, exact -36r^4 signal, and C_det r^6 determinant remainder bound to obtain the actual finite-radius odd minor with preserved strict sign."

canonicalOddTaylorQuantitativeFrontier : List QuantitativeEntry
canonicalOddTaylorQuantitativeFrontier =
  supportEntry ∷ sineRemainderEntry ∷ integratedRemainderEntry
  ∷ doubleRadiusEntry ∷ sixTermEntry ∷ degreeGapEntry
  ∷ coefficientEntry ∷ r6InequalityEntry
  ∷ smallRadiusEntry ∷ finiteSignEntry ∷ []

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

marginBoundary : Margin.DeterminantMarginBoundary
marginBoundary = Margin.canonicalDeterminantMarginBoundary

record OddTaylorQuantitativeBoundary : Set where
  constructor oddTaylorQuantitativeBoundary
  field
    taperSupportFactsAvailable : Bool
    taperSupportFactsAvailableIsTrue : taperSupportFactsAvailable ≡ true
    doubleRadiusCoefficient36Derived : Bool
    doubleRadiusCoefficient36DerivedIsTrue : doubleRadiusCoefficient36Derived ≡ true
    exactSixTermErrorDerived : Bool
    exactSixTermErrorDerivedIsTrue : exactSixTermErrorDerived ≡ true
    relativeErrorDegreeGapTwoDerived : Bool
    relativeErrorDegreeGapTwoDerivedIsTrue : relativeErrorDegreeGapTwoDerived ≡ true
    explicitDeterminantErrorCoefficientConstructed : Bool
    explicitDeterminantErrorCoefficientConstructedIsTrue :
      explicitDeterminantErrorCoefficientConstructed ≡ true
    fifthOrderSineRemainderDerived : Bool
    fifthOrderSineRemainderDerivedIsFalse : fifthOrderSineRemainderDerived ≡ false
    determinantR6InequalityDerived : Bool
    determinantR6InequalityDerivedIsFalse : determinantR6InequalityDerived ≡ false
    explicitSmallRadiusGateDerived : Bool
    explicitSmallRadiusGateDerivedIsFalse : explicitSmallRadiusGateDerived ≡ false
    finiteOddMinorSignDerived : Bool
    finiteOddMinorSignDerivedIsFalse : finiteOddMinorSignDerived ≡ false

canonicalOddTaylorQuantitativeBoundary : OddTaylorQuantitativeBoundary
canonicalOddTaylorQuantitativeBoundary =
  oddTaylorQuantitativeBoundary
    true refl true refl true refl true refl true refl
    false refl false refl false refl false refl
