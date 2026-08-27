module DASHI.Analysis.RiemannG21OddTaylorDeterminantConstantExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Explicit coefficient budget for the six-term determinant remainder at
-- radii r and 2r.
--
-- Assume for 0<r<=1:
--
--   |T_y(r)|  <= A_y1 r,
--   |T_y(2r)| <= A_y2 r,
--   |E_y(r)|  <= C_y r^5,
--   |E_y(2r)| <= 32 C_y r^5.
--
-- The six exact determinant-error terms are then bounded by C_det r^6, where
--
--   C_det =
--       32 A_a1 C_p
--     + C_a A_p2
--     + A_a2 C_p
--     + 32 C_a A_p1
--     + 64 C_a C_p.
--
-- The final 64 C_a C_p includes the two remainder*remainder terms after
-- using r^10 <= r^6 for 0<r<=1.
------------------------------------------------------------------------

record DoubleRadiusComponentConstants : Set₁ where
  field
    Scalar : Set
    truncA1 truncA2 truncP1 truncP2 : Scalar
    remainderA remainderP : Scalar
    add multiply : Scalar → Scalar → Scalar
    times32 times64 : Scalar → Scalar

open DoubleRadiusComponentConstants public

record DeterminantErrorConstant
    (components : DoubleRadiusComponentConstants) : Set₁ where
  field
    value : Scalar components

    coefficientFormula : Set

    reading : String

------------------------------------------------------------------------
-- Moment-generated truncation constants.
--
-- From T_y(r)=-6rN1(y)+r^3N3(y) and r<=1, natural candidates are
--
--   A_y1 = 6 N1(y) + N3(y),
--   A_y2 = 12 N1(y) + 8 N3(y).
--
-- If the six-scaled fifth-order response remainder obeys
--
--   |E_y(r)| <= (N5(y)/20) r^5,
--
-- then C_y=N5(y)/20.
------------------------------------------------------------------------

record MomentGeneratedErrorConstants : Set₁ where
  field
    Scalar : Set
    n1A n3A n5A n1P n3P n5P : Scalar
    add multiply : Scalar → Scalar → Scalar
    times6 times8 times12 : Scalar → Scalar
    divideBy20 : Scalar → Scalar

    truncA1 truncA2 truncP1 truncP2 remainderA remainderP : Scalar

    truncA1Formula : Set
    truncA2Formula : Set
    truncP1Formula : Set
    truncP2Formula : Set
    remainderAFormula : Set
    remainderPFormula : Set

    reading : String

------------------------------------------------------------------------
-- Final division-free radius gate.
------------------------------------------------------------------------

record ExplicitOddRadiusGate : Set₁ where
  field
    Scalar : Set
    determinantErrorConstant radiusSquared oddMomentMargin : Scalar
    multiply : Scalar → Scalar → Scalar
    times36 : Scalar → Scalar
    StrictBelow : Scalar → Scalar → Set

    gate :
      StrictBelow
        (multiply determinantErrorConstant radiusSquared)
        (times36 oddMomentMargin)

    reading : String

record OddDeterminantConstantBoundary : Set where
  constructor oddDeterminantConstantBoundary
  field
    explicitCoefficientShapeConstructed : Bool
    explicitCoefficientShapeConstructedIsTrue :
      explicitCoefficientShapeConstructed ≡ true
    momentGeneratedTruncationConstantsIdentified : Bool
    momentGeneratedTruncationConstantsIdentifiedIsTrue :
      momentGeneratedTruncationConstantsIdentified ≡ true
    fifthOrderRemainderCoefficientIdentified : Bool
    fifthOrderRemainderCoefficientIdentifiedIsTrue :
      fifthOrderRemainderCoefficientIdentified ≡ true
    actualSixTermInequalityDerived : Bool
    actualSixTermInequalityDerivedIsFalse : actualSixTermInequalityDerived ≡ false
    actualRadiusGateInhabited : Bool
    actualRadiusGateInhabitedIsFalse : actualRadiusGateInhabited ≡ false

canonicalOddDeterminantConstantBoundary : OddDeterminantConstantBoundary
canonicalOddDeterminantConstantBoundary =
  oddDeterminantConstantBoundary
    true refl true refl true refl false refl false refl
