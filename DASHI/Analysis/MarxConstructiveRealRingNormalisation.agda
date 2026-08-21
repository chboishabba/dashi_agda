module DASHI.Analysis.MarxConstructiveRealRingNormalisation where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.FastCauchyReals
  hiding (zero; one; add; sub; mul; neg; abs; le; lt)
open import DASHI.Analysis.FastCauchyQuotient
  hiding (zero; one; add; sub; mul; neg; abs; le; lt)
open import DASHI.Analysis.MarxDifferentialCore
  hiding (zero; one; _+_; _-_; _*_; _≢_)
open import DASHI.Analysis.MarxConstructiveRealAdapter

------------------------------------------------------------------------
-- The exact ring laws missing from ConstructedOrderedCompleteReal.
--
-- The existing constructed-real spine already exports associativity,
-- commutativity, distributivity, identities and subtraction-self.  This record
-- adds only the normal forms needed to transport the Marx finite-difference
-- identities through the selected quotient carrier.

record ConstructedRealRingNormalisationLaws
  (R : ConstructedOrderedCompleteReal)
  : Set₁ where
  field
    mulZeroRightLaw :
      ∀ x → _*_ R x (zero R) ≡ zero R

    subAsAddNeg :
      ∀ x y → _-_ R x y ≡ _+_ R x (neg R y)

    negAdd :
      ∀ x y → neg R (_+_ R x y) ≡ _+_ R (neg R x) (neg R y)

    differenceOfSums :
      ∀ a a₁ b b₁ →
      _-_ R (_+_ R a₁ b₁) (_+_ R a b)
      ≡ _+_ R (_-_ R a₁ a) (_-_ R b₁ b)

    differenceOfProducts :
      ∀ a a₁ b b₁ →
      _-_ R (_*_ R a₁ b₁) (_*_ R a b)
      ≡ _+_ R
          (_*_ R (_-_ R a₁ a) b₁)
          (_*_ R a (_-_ R b₁ b))

    zeroNotOne : zero R ≡ one R → ⊥
    twoNonzero : _+_ R (one R) (one R) ≡ zero R → ⊥

open ConstructedRealRingNormalisationLaws public

------------------------------------------------------------------------
-- The requested finite-difference factor laws are derived, not stored twice.

constructedRealAddDifferenceFactor :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (L : ConstructedRealRingNormalisationLaws R) →
  ∀ {x x₁ a a₁ b b₁ A B} →
  _-_ R a₁ a ≡ _*_ R (_-_ R x₁ x) A →
  _-_ R b₁ b ≡ _*_ R (_-_ R x₁ x) B →
  _-_ R (_+_ R a₁ b₁) (_+_ R a b)
  ≡ _*_ R (_-_ R x₁ x) (_+_ R A B)
constructedRealAddDifferenceFactor {R} L {x} {x₁} {a} {a₁} {b} {b₁} {A} {B}
  leftFactor rightFactor =
  trans
    (differenceOfSums L a a₁ b b₁)
    (trans
      (cong₂ (_+_ R) leftFactor rightFactor)
      (sym (distribLeft R (_-_ R x₁ x) A B)))

constructedRealProductDifferenceFactor :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (L : ConstructedRealRingNormalisationLaws R) →
  ∀ {x x₁ a a₁ b b₁ A B} →
  _-_ R a₁ a ≡ _*_ R (_-_ R x₁ x) A →
  _-_ R b₁ b ≡ _*_ R (_-_ R x₁ x) B →
  _-_ R (_*_ R a₁ b₁) (_*_ R a b)
  ≡ _*_ R
      (_-_ R x₁ x)
      (_+_ R (_*_ R A b₁) (_*_ R a B))
constructedRealProductDifferenceFactor
  {R} L {x} {x₁} {a} {a₁} {b} {b₁} {A} {B}
  leftFactor rightFactor =
  trans
    (differenceOfProducts L a a₁ b b₁)
    (trans
      (cong₂
        (_+_ R)
        (trans
          (cong (λ t → _*_ R t b₁) leftFactor)
          (mulAssoc R (_-_ R x₁ x) A b₁))
        (trans
          (cong (λ t → _*_ R a t) rightFactor)
          (trans
            (sym (mulAssoc R a (_-_ R x₁ x) B))
            (trans
              (cong (λ t → _*_ R t B) (mulComm R a (_-_ R x₁ x)))
              (mulAssoc R (_-_ R x₁ x) a B)))))
      (sym
        (distribLeft R
          (_-_ R x₁ x)
          (_*_ R A b₁)
          (_*_ R a B))))

constructedRealRingNormalisation :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ConstructedRealRingNormalisationLaws R →
  ConstructiveRealMarxNormalisation R
constructedRealRingNormalisation {R} L =
  record
    { _≢_ = λ x y → x ≡ y → ⊥
    ; mulZeroRight = mulZeroRightLaw L
    ; addDifferenceFactor = constructedRealAddDifferenceFactor L
    ; productDifferenceFactor = constructedRealProductDifferenceFactor L
    }

ordinaryConstructiveRealMarxAlgebra :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ConstructedRealRingNormalisationLaws R →
  MarxAlgebra
ordinaryConstructiveRealMarxAlgebra {R} L =
  constructedRealToMarxAlgebra R (constructedRealRingNormalisation L)

ordinaryConstructiveRealMarxPackage :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (L : ConstructedRealRingNormalisationLaws R) →
  ConstructiveRealMarxDifferentialPackage
ordinaryConstructiveRealMarxPackage {R} L =
  record
    { constructedReal = R
    ; finiteDifferenceNormalisation = constructedRealRingNormalisation L
    ; marxAlgebra = ordinaryConstructiveRealMarxAlgebra L
    ; marxAlgebraIsSelectedAdapter = refl
    }

ordinaryMarxCarrierNonterminal :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (L : ConstructedRealRingNormalisationLaws R) →
  zero R ≡ one R → ⊥
ordinaryMarxCarrierNonterminal L = zeroNotOne L

------------------------------------------------------------------------
-- Existing representative-respect lemmas, re-exported under the completion
-- cutset names.  These are already proved in FastCauchyArithmetic/Quotient.

addRespectsFastCauchyEquality :
  ∀ {A : RationalMetricAuthority}
    (O : FastCauchyOperations A)
    {a a′ b b′ : FastCauchyReal A} →
  a ≈R a′ → b ≈R b′ → addR O a b ≈R addR O a′ b′
addRespectsFastCauchyEquality O = addRespect O

subRespectsFastCauchyEquality :
  ∀ {A : RationalMetricAuthority}
    (O : FastCauchyOperations A)
    {a a′ b b′ : FastCauchyReal A} →
  a ≈R a′ → b ≈R b′ → subR O a b ≈R subR O a′ b′
subRespectsFastCauchyEquality O = subRespect O

mulRespectsFastCauchyEquality :
  ∀ {A : RationalMetricAuthority}
    (O : FastCauchyOperations A)
    {a a′ b b′ : FastCauchyReal A} →
  a ≈R a′ → b ≈R b′ → mulR O a b ≈R mulR O a′ b′
mulRespectsFastCauchyEquality O = mulRespect O

negRespectsFastCauchyEquality :
  ∀ {A : RationalMetricAuthority}
    {O : FastCauchyOperations A}
    {Q : SetQuotientBackend (FastCauchyReal A) _≈R_} →
  (F : FastCauchyQuotientOperations A O Q) →
  ∀ {a a′ : FastCauchyReal A} →
  a ≈R a′ → negR O a ≈R negR O a′
negRespectsFastCauchyEquality F = negRespectRepresentative F
