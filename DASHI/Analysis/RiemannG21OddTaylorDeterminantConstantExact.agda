module DASHI.Analysis.RiemannG21OddTaylorDeterminantConstantExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; _+_; _*_)

------------------------------------------------------------------------
-- Explicit coefficient budget for the six-term determinant remainder at
-- radii r and 2r.
------------------------------------------------------------------------

trunc1Q : ℚ → ℚ → ℚ
trunc1Q n1 n3 = 6 * n1 + n3

trunc2Q : ℚ → ℚ → ℚ
trunc2Q n1 n3 = 12 * n1 + 8 * n3

determinantErrorConstantQ :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
determinantErrorConstantQ aa1 aa2 ap1 ap2 ca cp =
    32 * aa1 * cp
  + ca * ap2
  + aa2 * cp
  + 32 * ca * ap1
  + 64 * ca * cp

determinantErrorConstantFromMomentsQ :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
determinantErrorConstantFromMomentsQ n1a n3a n1p n3p ca cp =
  determinantErrorConstantQ
    (trunc1Q n1a n3a)
    (trunc2Q n1a n3a)
    (trunc1Q n1p n3p)
    (trunc2Q n1p n3p)
    ca cp

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
    explicitRationalCoefficientConstructed : Bool
    explicitRationalCoefficientConstructedIsTrue :
      explicitRationalCoefficientConstructed ≡ true
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
    true refl true refl true refl true refl false refl false refl
