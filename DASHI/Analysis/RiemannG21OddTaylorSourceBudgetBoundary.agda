module DASHI.Analysis.RiemannG21OddTaylorSourceBudgetBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record TaperSupportSourceReceipt : Set where
  constructor taperSupportSourceReceipt
  field
    companionRepository : String
    basicSourcePath : String
    stripSourcePath : String
    phiNonnegativeTheorem : String
    phiLeOneTheorem : String
    phiSupportSubsetTheorem : String
    phiCompactSupportTheorem : String
    phiIntegrableTheorem : String
    integralPhiLeTheorem : String
    supportRadiusReading : String

canonicalTaperSupportSourceReceipt : TaperSupportSourceReceipt
canonicalTaperSupportSourceReceipt =
  taperSupportSourceReceipt
    "anthropics/zeta-23-lean"
    "Zeta23/Taper/Basic.lean"
    "Zeta23/Taper/Strip.lean"
    "Zeta23.Taper.phi_nonneg"
    "Zeta23.Taper.phi_le_one"
    "Zeta23.Taper.phi_support_subset"
    "Zeta23.Taper.phi_hasCompactSupport"
    "Zeta23.Taper.phi_integrable"
    "Zeta23.Taper.integral_phi_le"
    "The companion proves supp(phi) subset [-L/2,L/2], 0 <= phi <= 1, phi integrable, and integral phi <= L."

record FifthOrderSineRemainder : Set₁ where
  field
    Real : Set
    zero : Real
    add subtract multiply divide : Real → Real → Real
    abs sin : Real → Real
    StrictPositive : Real → Set
    LessOrEqual : Real → Real → Set
    x : Real
    oneTwenty : Real
    pointwiseFifthOrderBound : Set
    reading : String

record IntegratedOddRemainderBound : Set₁ where
  field
    Height Radius Scalar : Set
    height : Height
    radius : Radius
    n5 : Height → Scalar
    sixScaledRemainder : Height → Radius → Scalar
    abs : Scalar → Scalar
    radiusFifth : Radius → Scalar
    multiply : Scalar → Scalar → Scalar
    divideByTwenty : Scalar → Scalar
    LessOrEqual : Scalar → Scalar → Set
    sixScaledRemainderBound :
      LessOrEqual
        (abs (sixScaledRemainder height radius))
        (divideByTwenty (multiply (radiusFifth radius) (n5 height)))
    reading : String

record CompactSupportN5Bound : Set₁ where
  field
    Height Length Scalar : Set
    height : Height
    length : Length
    n5AtHeight : Scalar
    crudeUpperBound : Scalar
    LessOrEqual : Scalar → Scalar → Set
    n5Bound : LessOrEqual n5AtHeight crudeUpperBound
    boundReading : String

record DoubleRadiusOddSignGate : Set₁ where
  field
    Scalar : Set
    radiusSquared determinantErrorConstant oddMomentMargin : Scalar
    multiply : Scalar → Scalar → Scalar
    thirtySixTimes : Scalar → Scalar
    StrictBelow : Scalar → Scalar → Set
    StrictPositive : Scalar → Set
    oddMomentMarginPositive : StrictPositive oddMomentMargin
    smallRadiusGate :
      StrictBelow
        (multiply determinantErrorConstant radiusSquared)
        (thirtySixTimes oddMomentMargin)
    finiteOddDeterminantSignPreserved : Set
    reading : String

record OddTaylorSourceBudgetBoundary : Set where
  constructor oddTaylorSourceBudgetBoundary
  field
    taperSupportFactsSourceAudited : Bool
    taperSupportFactsSourceAuditedIsTrue : taperSupportFactsSourceAudited ≡ true
    fifthOrderSineRemainderLocatedOrDerived : Bool
    fifthOrderSineRemainderLocatedOrDerivedIsFalse :
      fifthOrderSineRemainderLocatedOrDerived ≡ false
    integratedR5RemainderBoundDerived : Bool
    integratedR5RemainderBoundDerivedIsFalse :
      integratedR5RemainderBoundDerived ≡ false
    compactSupportN5BoundDerived : Bool
    compactSupportN5BoundDerivedIsFalse : compactSupportN5BoundDerived ≡ false
    determinantR6ConstantDerived : Bool
    determinantR6ConstantDerivedIsFalse : determinantR6ConstantDerived ≡ false
    explicitSmallRadiusGateDerived : Bool
    explicitSmallRadiusGateDerivedIsFalse : explicitSmallRadiusGateDerived ≡ false

canonicalOddTaylorSourceBudgetBoundary : OddTaylorSourceBudgetBoundary
canonicalOddTaylorSourceBudgetBoundary =
  oddTaylorSourceBudgetBoundary
    true refl false refl false refl false refl false refl false refl
