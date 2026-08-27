module DASHI.Analysis.RiemannG21OddTaylorQuantitativeFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG21OddTaylorDeterminantExact as Taylor
import DASHI.Analysis.RiemannG21OddTaylorRemainderDeterminantExact as Remainder
import DASHI.Analysis.RiemannG21OddTaylorOrderBudgetExact as Order
import DASHI.Analysis.RiemannG21OddTaylorSourceBudgetBoundary as Source
import DASHI.Analysis.RiemannG21DeterminantMarginTransferExact as Margin

data OddTaylorQuantitativeArrow : Set where
  compactSupportAndPositivity : OddTaylorQuantitativeArrow
  fifthOrderSineRemainder : OddTaylorQuantitativeArrow
  integratedOddR5Remainder : OddTaylorQuantitativeArrow
  doubleRadiusCubicSignal : OddTaylorQuantitativeArrow
  exactSixTermDeterminantError : OddTaylorQuantitativeArrow
  radiusDegreeGapTwo : OddTaylorQuantitativeArrow
  determinantR6Constant : OddTaylorQuantitativeArrow
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

r6ConstantEntry : QuantitativeEntry
r6ConstantEntry = quantitativeEntry
  determinantR6Constant analyticOpen
  "Use the compact-support N5 bound and explicit truncation magnitudes at r and 2r to produce C_det(a,p,L) with |det A-det T| <= C_det r^6."

smallRadiusEntry : QuantitativeEntry
smallRadiusEntry = quantitativeEntry
  divisionFreeSmallRadiusGate analyticOpen
  "Choose r>0 satisfying C_det r^2 < 36 Delta_odd. This is the exact division-free sign-preservation condition after canceling the common r^4 scale."

finiteSignEntry : QuantitativeEntry
finiteSignEntry = quantitativeEntry
  finiteOddMinorSign analyticOpen
  "Combine the strict continuum odd margin, exact -36r^4 signal, and direct determinant remainder bound to obtain the actual finite-radius odd minor with preserved strict sign."

canonicalOddTaylorQuantitativeFrontier : List QuantitativeEntry
canonicalOddTaylorQuantitativeFrontier =
  supportEntry ∷ sineRemainderEntry ∷ integratedRemainderEntry
  ∷ doubleRadiusEntry ∷ sixTermEntry ∷ degreeGapEntry
  ∷ r6ConstantEntry ∷ smallRadiusEntry ∷ finiteSignEntry ∷ []

sourceBoundary : Source.OddTaylorSourceBudgetBoundary
sourceBoundary = Source.canonicalOddTaylorSourceBudgetBoundary

taylorBoundary : Taylor.OddTaylorDeterminantBoundary
taylorBoundary = Taylor.canonicalOddTaylorDeterminantBoundary

remainderBoundary : Remainder.OddTaylorRemainderBoundary
remainderBoundary = Remainder.canonicalOddTaylorRemainderBoundary

orderBudget : Order.OddTaylorOrderBudget
orderBudget = Order.canonicalOddTaylorOrderBudget

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
    fifthOrderSineRemainderDerived : Bool
    fifthOrderSineRemainderDerivedIsFalse : fifthOrderSineRemainderDerived ≡ false
    determinantR6ConstantDerived : Bool
    determinantR6ConstantDerivedIsFalse : determinantR6ConstantDerived ≡ false
    explicitSmallRadiusGateDerived : Bool
    explicitSmallRadiusGateDerivedIsFalse : explicitSmallRadiusGateDerived ≡ false
    finiteOddMinorSignDerived : Bool
    finiteOddMinorSignDerivedIsFalse : finiteOddMinorSignDerived ≡ false

canonicalOddTaylorQuantitativeBoundary : OddTaylorQuantitativeBoundary
canonicalOddTaylorQuantitativeBoundary =
  oddTaylorQuantitativeBoundary
    true refl true refl true refl true refl
    false refl false refl false refl false refl
