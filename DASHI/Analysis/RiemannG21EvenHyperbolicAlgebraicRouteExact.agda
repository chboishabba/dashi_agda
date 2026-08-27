module DASHI.Analysis.RiemannG21EvenHyperbolicAlgebraicRouteExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Alternative route for the EVEN/cosh relative-weight inequality.
--
-- For 0 < a < p and 0 < u < v, the target is
--
--   cosh(p v) cosh(a u) > cosh(p u) cosh(a v).
--
-- Unlike the odd/sinh sector, this can be reduced without logarithmic
-- derivatives.  Product-to-sum gives two cosh comparisons.  Their argument
-- ordering follows from
--
--   p v + a u > p u + a v
--
-- because (p-a)(v-u)>0, and
--
--   (p v - a u)^2 - (p u - a v)^2
--     = (p^2-a^2)(v^2-u^2) > 0.
--
-- Since p v - a u > 0, the second identity implies
--
--   p v - a u > |p u - a v|.
--
-- Evenness and strict increase of cosh on the positive axis then yield the
-- second product-to-sum comparison.  Thus the even sector can use elementary
-- order/algebra plus standard cosh monotonicity and does not depend on the
-- x*tanh(x) route.  The actual ordered-real instantiation remains analytic.
------------------------------------------------------------------------

record PositiveRectangle : Set₁ where
  field
    Scalar : Set
    a p u v : Scalar
    StrictlyPositive : Scalar → Set
    StrictlyBelow : Scalar → Scalar → Set

    aPositive : StrictlyPositive a
    pPositive : StrictlyPositive p
    uPositive : StrictlyPositive u
    vPositive : StrictlyPositive v
    aBelowP : StrictlyBelow a p
    uBelowV : StrictlyBelow u v

open PositiveRectangle public

record EvenProductToSumOrderProducer (rect : PositiveRectangle) : Set₁ where
  field
    add subtract multiply square abs : Scalar rect → Scalar rect → Scalar rect
    -- abs is intentionally binary at this weak interface only as an opaque
    -- carrier operation slot; literal real instantiation may repackage it.
    StrictlyPositive : Scalar rect → Set
    StrictlyBelow : Scalar rect → Scalar rect → Set

    sumArgumentSeparated : Set
    squareDifferenceFactorization : Set
    positiveDifferenceArgument : Set
    absoluteDifferenceArgumentSeparated : Set

    producerReading : String

------------------------------------------------------------------------
-- Division-free algebraic certificate shape.  The proof owner that eventually
-- instantiates ordered reals may use ring normalization for the factorization
-- and ordinary positive-product order for the strict signs.
------------------------------------------------------------------------

record EvenHyperbolicAlgebraicCertificate : Set₁ where
  field
    Scalar : Set
    a p u v : Scalar
    add subtract multiply square : Scalar → Scalar → Scalar
    StrictGreater : Scalar → Scalar → Set

    sumArgumentStrict :
      StrictGreater
        (add (multiply p v) (multiply a u))
        (add (multiply p u) (multiply a v))

    differenceSquaresStrict :
      StrictGreater
        (square (subtract (multiply p v) (multiply a u))
                (subtract (multiply p v) (multiply a u)))
        (square (subtract (multiply p u) (multiply a v))
                (subtract (multiply p u) (multiply a v)))

    factorizationReading : String

record EvenHyperbolicAlgebraicBoundary : Set where
  constructor evenHyperbolicAlgebraicBoundary
  field
    sumArgumentFactorizationIdentified : Bool
    sumArgumentFactorizationIdentifiedIsTrue :
      sumArgumentFactorizationIdentified ≡ true
    squareDifferenceFactorizationIdentified : Bool
    squareDifferenceFactorizationIdentifiedIsTrue :
      squareDifferenceFactorizationIdentified ≡ true
    evenSectorIndependentOfXTanhRoute : Bool
    evenSectorIndependentOfXTanhRouteIsTrue :
      evenSectorIndependentOfXTanhRoute ≡ true
    orderedRealCoshMinorDerivedInAgda : Bool
    orderedRealCoshMinorDerivedInAgdaIsFalse :
      orderedRealCoshMinorDerivedInAgda ≡ false

canonicalEvenHyperbolicAlgebraicBoundary : EvenHyperbolicAlgebraicBoundary
canonicalEvenHyperbolicAlgebraicBoundary =
  evenHyperbolicAlgebraicBoundary
    true refl true refl true refl false refl
