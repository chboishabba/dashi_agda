module DASHI.Analysis.MarxConstructiveRealAdapter where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.MarxDifferentialCore

------------------------------------------------------------------------
-- Exact adapter from the repository's constructed-real carrier.
--
-- ConstructedOrderedCompleteReal already owns the carrier, arithmetic,
-- associativity, distributivity, subtraction-self law, sequences, Cauchy
-- convergence, and limits.  It does not yet expose the two finite-difference
-- normalisation lemmas needed by MarxFactorisation closure.  Those missing
-- lemmas are isolated here rather than duplicated or assumed globally.

record ConstructiveRealMarxNormalisation
  (R : ConstructedOrderedCompleteReal)
  : Set₁ where
  field
    _≢_ : Real R → Real R → Set
    mulZeroRight :
      ∀ x → _*_ R x (zero R) ≡ zero R

    addDifferenceFactor :
      ∀ {x x₁ a a₁ b b₁ A B} →
      _-_ R a₁ a ≡ _*_ R (_-_ R x₁ x) A →
      _-_ R b₁ b ≡ _*_ R (_-_ R x₁ x) B →
      _-_ R (_+_ R a₁ b₁) (_+_ R a b)
      ≡ _*_ R (_-_ R x₁ x) (_+_ R A B)

    productDifferenceFactor :
      ∀ {x x₁ a a₁ b b₁ A B} →
      _-_ R a₁ a ≡ _*_ R (_-_ R x₁ x) A →
      _-_ R b₁ b ≡ _*_ R (_-_ R x₁ x) B →
      _-_ R (_*_ R a₁ b₁) (_*_ R a b)
      ≡ _*_ R
          (_-_ R x₁ x)
          (_+_ R (_*_ R A b₁) (_*_ R a B))

open ConstructiveRealMarxNormalisation public

constructedRealToMarxAlgebra :
  (R : ConstructedOrderedCompleteReal) →
  ConstructiveRealMarxNormalisation R →
  MarxAlgebra
constructedRealToMarxAlgebra R N =
  record
    { Carrier = Real R
    ; zero = zero R
    ; one = one R
    ; _+_ = _+_ R
    ; _-_ = _-_ R
    ; _*_ = _*_ R
    ; _≢_ = _≢_ N
    ; subSelf = subSelf R
    ; mulZeroRight = mulZeroRight N
    ; mulOneRight = mulOneRight R
    ; mulCommutative = mulComm R
    ; mulAssoc = mulAssoc R
    ; addDifferenceFactor = addDifferenceFactor N
    ; productDifferenceFactor = productDifferenceFactor N
    }

record ConstructiveRealMarxDifferentialPackage : Set₁ where
  field
    constructedReal : ConstructedOrderedCompleteReal
    finiteDifferenceNormalisation :
      ConstructiveRealMarxNormalisation constructedReal

    marxAlgebra : MarxAlgebra
    marxAlgebraIsSelectedAdapter :
      marxAlgebra
      ≡ constructedRealToMarxAlgebra
          constructedReal
          finiteDifferenceNormalisation

-- This adapter proves that the remaining gap is not completion, series, exp,
-- or log.  It is the small ring-normalisation and topology seam needed to turn
-- the existing constructive real into a nondegenerate differential carrier.
