module DASHI.Analysis.RiemannG21OddTaylorSourceBudgetBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-bounded analytic producer for the odd determinant remainder.
--
-- Companion source ownership (anthropics/zeta-23-lean):
--
--   Zeta23/Taper/Basic.lean
--     Taper.phi_nonneg
--     Taper.phi_le_one
--     Taper.phi_support_subset
--     Taper.phi_hasCompactSupport
--     Taper.phi_integrable
--
--   Zeta23/Taper/Strip.lean
--     Taper.phiC_support
--     Taper.integral_phi_le
--
-- These prove 0 <= phi <= 1, support inside [-L/2,L/2], compact support,
-- integrability, and integral phi <= L.  They do NOT by themselves prove the
-- fifth-order sine Taylor remainder used below.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Atomic pointwise Taylor remainder target.
------------------------------------------------------------------------

record FifthOrderSineRemainder : Set₁ where
  field
    Real : Set
    zero : Real
    add subtract multiply divide abs sin : Real → Real → Real
    -- Operations stay opaque at this weak cross-prover interface.
    StrictPositive : Real → Set
    LessOrEqual : Real → Real → Set

    x : Real
    oneTwenty : Real

    pointwiseFifthOrderBound : Set

    reading : String

------------------------------------------------------------------------
-- Integrated odd-response remainder target.
--
-- For the unscaled odd response remainder R_y(r), the desired bound is
--
--   |R_y(r)| <= |r|^5 N5(y) / 120.
--
-- For the six-scaled response E_y(r)=6 R_y(r):
--
--   |E_y(r)| <= |r|^5 N5(y) / 20.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Compact-support moment producer.
--
-- A crude source-compatible target is
--
--   N5(y) <= L (L/2)^5 sinh(y L/2)
--
-- for 0<y<=1/2, using 0<=phi<=1, supp phi subset [-L/2,L/2], and integral
-- phi<=L.  The exact constant may be improved; G21 needs an explicit valid
-- upper bound, not an optimal one.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Determinant-level small-radius gate for r2=2r.
--
-- The exact cubic signal has magnitude 36 r^4 Delta_odd.  If the structured
-- six-term determinant remainder is bounded by C_det r^6, sign preservation
-- reduces division-free to
--
--   C_det r^2 < 36 Delta_odd.
------------------------------------------------------------------------

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
