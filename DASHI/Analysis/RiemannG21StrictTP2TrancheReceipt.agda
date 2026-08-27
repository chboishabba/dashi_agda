module DASHI.Analysis.RiemannG21StrictTP2TrancheReceipt where

open import DASHI.Core.Prelude

import DASHI.Analysis.StrictKernelMomentRatioExact as TP2
import DASHI.Analysis.RiemannG21OddSinhTP2Exact as Odd
import DASHI.Analysis.RiemannG21OddTaylorDeterminantExact as OddTaylor
import DASHI.Analysis.RiemannG21OddTaylorRemainderDeterminantExact as OddRemainder
import DASHI.Analysis.RiemannG21DeterminantMarginTransferExact as Margin
import DASHI.Analysis.RiemannG21ParityMinorAnalyticFrontierExact as Frontier
import DASHI.Analysis.RiemannG22ReflectionHermitianDeskTestExact as G22

record StrictTP2TrancheReceipt : Set where
  constructor strictTP2TrancheReceipt
  field
    genericTP2OwnerConstructed : Bool
    genericTP2OwnerConstructedIsTrue : genericTP2OwnerConstructed ≡ true
    oddStrictSignTargetNamed : Bool
    oddStrictSignTargetNamedIsTrue : oddStrictSignTargetNamed ≡ true
    oddCubicTaylorFactorizationDerived : Bool
    oddCubicTaylorFactorizationDerivedIsTrue : oddCubicTaylorFactorizationDerived ≡ true
    exactOddDeterminantRemainderDecompositionDerived : Bool
    exactOddDeterminantRemainderDecompositionDerivedIsTrue :
      exactOddDeterminantRemainderDecompositionDerived ≡ true
    determinantMarginInterfaceConstructed : Bool
    determinantMarginInterfaceConstructedIsTrue : determinantMarginInterfaceConstructed ≡ true
    actualSinhTP2Derived : Bool
    actualSinhTP2DerivedIsFalse : actualSinhTP2Derived ≡ false
    actualOddContinuumSignDerived : Bool
    actualOddContinuumSignDerivedIsFalse : actualOddContinuumSignDerived ≡ false
    actualStructuredRemainderBoundDerived : Bool
    actualStructuredRemainderBoundDerivedIsFalse : actualStructuredRemainderBoundDerived ≡ false
    actualFiniteRadiusSignDerived : Bool
    actualFiniteRadiusSignDerivedIsFalse : actualFiniteRadiusSignDerived ≡ false
    g22SuccessorSocketConstructed : Bool
    g22SuccessorSocketConstructedIsTrue : g22SuccessorSocketConstructed ≡ true
    g22LiteralPrimeIdentityDerived : Bool
    g22LiteralPrimeIdentityDerivedIsFalse : g22LiteralPrimeIdentityDerived ≡ false
    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse : riemannHypothesisDerived ≡ false

canonicalStrictTP2TrancheReceipt : StrictTP2TrancheReceipt
canonicalStrictTP2TrancheReceipt =
  strictTP2TrancheReceipt
    true refl true refl
    true refl true refl true refl
    false refl false refl false refl false refl
    true refl false refl false refl
