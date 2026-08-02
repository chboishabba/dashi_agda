module DASHI.Analysis.SetoidConstructiveRealSpine where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Martín Hötzel Escardó; Fredrik
-- Nordvall Forsberg; Chuangjie Xu; Zachary Murray; Viktor Csimma; DASHI
-- repository contributors.
-- Title: "Constructive Analysis"; "The Inconsistency of a Brouwerian
-- Continuity Principle with the Curry--Howard Interpretation"; "Formalising
-- Real Numbers in Homotopy Type Theory"; "Constructive Analysis in the Agda
-- Proof Assistant"; and "Setoid constructive-real spine for DASHI".
-- Venue/year: Springer, 1985; Typed Lambda Calculi and Applications, 2015;
-- CPP 2017; Dalhousie University/arXiv, 2022; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.1007/978-3-319-19797-5_20;
-- 10.1145/3018610.3018614; 10.48550/arXiv.2205.08354; the repository
-- capability surface has no DOI.
-- Uses: the standard constructive practice of retaining Cauchy reals as a
-- carrier equipped with extensional equality rather than identifying
-- extensional equality with Agda propositional equality.
-- Relationship: this is the nondegenerate backend boundary used when a
-- literal quotient would require representative choice for arbitrary
-- quotient-valued sequences.  It records exactly the algebra, order and
-- Cauchy-completeness laws used by the output-relocation programme.  Square
-- order reflection is kept as a sibling capability because it is not part of
-- the minimal ordered-complete-real interface.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)

record SetoidOrderedCompleteReal : Set₁ where
  infix 4 _≈_ _≤_ _<_
  infixl 20 _+_ _-_
  infixl 30 _*_

  field
    Carrier : Set
    _≈_ : Carrier → Carrier → Set
    ≈-refl : ∀ {x} → x ≈ x
    ≈-sym : ∀ {x y} → x ≈ y → y ≈ x
    ≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

    zero one : Carrier
    _+_ _-_ _*_ : Carrier → Carrier → Carrier
    neg abs : Carrier → Carrier

    addCong : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a + b) ≈ (a′ + b′)
    subCong : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a - b) ≈ (a′ - b′)
    mulCong : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a * b) ≈ (a′ * b′)
    negCong : ∀ {a b} → a ≈ b → neg a ≈ neg b
    absCong : ∀ {a b} → a ≈ b → abs a ≈ abs b

    addAssoc : ∀ a b c → ((a + b) + c) ≈ (a + (b + c))
    addComm : ∀ a b → (a + b) ≈ (b + a)
    addZeroLeft : ∀ a → (zero + a) ≈ a
    addZeroRight : ∀ a → (a + zero) ≈ a
    addInverseRight : ∀ a → (a + neg a) ≈ zero

    mulAssoc : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
    mulComm : ∀ a b → (a * b) ≈ (b * a)
    mulOneLeft : ∀ a → (one * a) ≈ a
    mulOneRight : ∀ a → (a * one) ≈ a
    mulZeroLeft : ∀ a → (zero * a) ≈ zero
    mulZeroRight : ∀ a → (a * zero) ≈ zero
    distribLeft : ∀ a b c → (a * (b + c)) ≈ ((a * b) + (a * c))
    distribRight : ∀ a b c → ((a + b) * c) ≈ ((a * c) + (b * c))
    subSelf : ∀ a → (a - a) ≈ zero

    _≤_ _<_ : Carrier → Carrier → Set
    leRefl : ∀ x → x ≤ x
    leTrans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    ltTrans : ∀ {a b c} → a < b → b < c → a < c
    ltToLe : ∀ {a b} → a < b → a ≤ b
    leRespectsLeft : ∀ {a a′ b} → a ≈ a′ → a ≤ b → a′ ≤ b
    leRespectsRight : ∀ {a b b′} → b ≈ b′ → a ≤ b → a ≤ b′
    ltRespectsLeft : ∀ {a a′ b} → a ≈ a′ → a < b → a′ < b
    ltRespectsRight : ∀ {a b b′} → b ≈ b′ → a < b → a < b′

    addMonotone : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
    addStrictMonotone : ∀ {a b c d} → a < b → c < d → (a + c) < (b + d)
    negateAntitone : ∀ {a b} → a ≤ b → neg b ≤ neg a
    negateStrictAntitone : ∀ {a b} → a < b → neg b < neg a
    multiplyMonotoneNonnegative : ∀ {a b c d} →
      zero ≤ a → a ≤ b → zero ≤ c → c ≤ d → (a * c) ≤ (b * d)

    valueBelowAbsolute : ∀ value → value ≤ abs value
    negativeAbsoluteBelowValue : ∀ value → neg (abs value) ≤ value
    absoluteNonnegative : ∀ value → zero ≤ abs value

    Sequence : Set
    sequenceAt : Sequence → Nat → Carrier
    IsCauchy : Sequence → Set
    ConvergesTo : Sequence → Carrier → Set
    cauchyLimit : (sequence : Sequence) →
      IsCauchy sequence → Σ Carrier (λ limit → ConvergesTo sequence limit)

open SetoidOrderedCompleteReal public

record SetoidNonnegativeSquareOrder
    (R : SetoidOrderedCompleteReal) : Set₁ where
  field
    squareReflectsOrderOnNonnegative : ∀ {left right} →
      _≤_ R (zero R) left → _≤_ R (zero R) right →
      _≤_ R (_*_ R left left) (_*_ R right right) →
      _≤_ R left right

open SetoidNonnegativeSquareOrder public

record SetoidRealExponential
    (R : SetoidOrderedCompleteReal) : Set₁ where
  field
    exp : Carrier R → Carrier R
    expCong : ∀ {x y} → _≈_ R x y → _≈_ R (exp x) (exp y)
    expZero : _≈_ R (exp (zero R)) (one R)
    expAdd : ∀ x y →
      _≈_ R (exp (_+_ R x y)) (_*_ R (exp x) (exp y))
    expNonnegative : ∀ x → _≤_ R (zero R) (exp x)
    expStrictlyPositive : ∀ x → _<_ R (zero R) (exp x)
    expMonotone : ∀ {x y} → _≤_ R x y → _≤_ R (exp x) (exp y)
    expStrictMonotone : ∀ {x y} → _<_ R x y → _<_ R (exp x) (exp y)

open SetoidRealExponential public

record SetoidRealLogarithm
    (R : SetoidOrderedCompleteReal)
    (E : SetoidRealExponential R) : Set₁ where
  field
    log : Carrier R → Carrier R
    logCong : ∀ {x y} → _≈_ R x y → _≈_ R (log x) (log y)
    expLogOnPositive : ∀ y → _<_ R (zero R) y →
      _≈_ R (exp E (log y)) y
    logOne : _≈_ R (log (one R)) (zero R)
    logMultiplyPositive : ∀ x y →
      _<_ R (zero R) x → _<_ R (zero R) y →
      _≈_ R (log (_*_ R x y)) (_+_ R (log x) (log y))

open SetoidRealLogarithm public
