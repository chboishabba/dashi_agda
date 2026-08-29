module DASHI.Analysis.RiemannG21OddMomentRatioGapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG21OddSinhTP2Exact as Odd
import DASHI.Analysis.RiemannG21OddTaylorNormalizedRadiusGateExact as Radius

------------------------------------------------------------------------
-- Normalize the strict odd moment determinant to the ratio-gap quantity used
-- by the support-only radius gate.
--
-- For positive N1(a),N1(p), define
--
--   qa = N3(a)/N1(a),
--   qp = N3(p)/N1(p).
--
-- The strict TP2 moment theorem gives
--
--   N1(a)N3(p) > N3(a)N1(p),
--
-- hence
--
--   qp > qa.
--
-- The current weak Agda real interface does not yet own division/cancellation
-- strongly enough to derive this specialization.  We therefore expose the
-- exact cross-multiplied producer and the normalized positive-gap consumer as
-- separate obligations, while reusing the rational mass factorization already
-- proved in RiemannG21OddTaylorNormalizedRadiusGateExact.
------------------------------------------------------------------------

record CrossMultipliedOddGap : Set₁ where
  field
    Scalar : Set
    n1A n3A n1P n3P : Scalar
    multiply : Scalar → Scalar → Scalar
    StrictGreater : Scalar → Scalar → Set

    strictCrossProduct :
      StrictGreater
        (multiply n1A n3P)
        (multiply n3A n1P)

    reading : String

record NormalizedOddRatioGap : Set₁ where
  field
    Scalar : Set
    qa qp ratioGap : Scalar
    subtract : Scalar → Scalar → Scalar
    StrictPositive : Scalar → Set
    StrictGreater : Scalar → Scalar → Set

    ratioGapFormula : ratioGap ≡ subtract qp qa
    qpStrictlyAboveQa : StrictGreater qp qa
    ratioGapPositive : StrictPositive ratioGap

    reading : String

record CrossProductToRatioGapBridge : Set₁ where
  field
    Scalar : Set
    n1A n3A n1P n3P qa qp : Scalar
    multiply divide subtract : Scalar → Scalar → Scalar
    StrictPositive : Scalar → Set
    StrictGreater : Scalar → Scalar → Set

    n1APositive : StrictPositive n1A
    n1PPositive : StrictPositive n1P

    qaDefinition : qa ≡ divide n3A n1A
    qpDefinition : qp ≡ divide n3P n1P

    strictCrossProduct :
      StrictGreater
        (multiply n1A n3P)
        (multiply n3A n1P)

    normalizedStrictGap : StrictGreater qp qa

    bridgeReading : String

------------------------------------------------------------------------
-- Existing exact rational factorization remains the algebraic regression for
-- this bridge:
--
-- Delta = N1(a)N1(p)(qp-qa).
------------------------------------------------------------------------

record OddRatioGapBoundary : Set where
  constructor oddRatioGapBoundary
  field
    crossMultipliedGapInterfaceConstructed : Bool
    crossMultipliedGapInterfaceConstructedIsTrue :
      crossMultipliedGapInterfaceConstructed ≡ true
    normalizedRatioGapInterfaceConstructed : Bool
    normalizedRatioGapInterfaceConstructedIsTrue :
      normalizedRatioGapInterfaceConstructed ≡ true
    rationalMassFactorizationAvailable : Bool
    rationalMassFactorizationAvailableIsTrue :
      rationalMassFactorizationAvailable ≡ true
    actualCrossProductStrictSignDerived : Bool
    actualCrossProductStrictSignDerivedIsFalse :
      actualCrossProductStrictSignDerived ≡ false
    positiveMassCancellationDerivedInAgda : Bool
    positiveMassCancellationDerivedInAgdaIsFalse :
      positiveMassCancellationDerivedInAgda ≡ false
    actualPositiveRatioGapDerived : Bool
    actualPositiveRatioGapDerivedIsFalse :
      actualPositiveRatioGapDerived ≡ false

canonicalOddRatioGapBoundary : OddRatioGapBoundary
canonicalOddRatioGapBoundary =
  oddRatioGapBoundary
    true refl true refl true refl false refl false refl false refl

oddTP2Boundary : Odd.OddSinhTP2Boundary
oddTP2Boundary = Odd.canonicalOddSinhTP2Boundary

normalizedRadiusBoundary : Radius.NormalizedRadiusGateBoundary
normalizedRadiusBoundary = Radius.canonicalNormalizedRadiusGateBoundary
