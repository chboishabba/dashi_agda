module DASHI.Analysis.ConstructedRealBackendSpineExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as Legacy
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Setoid-aware constructive-real backend contract.
--
-- The existing ConstructedOrderedCompleteReal record uses propositional
-- equality because it was designed to sit behind a quotient realization.
-- This sibling record is the direct contract for quotient-free real models
-- such as DASHI FastCauchyReals and viktorcsimma/bishop.
------------------------------------------------------------------------

record SetoidOrderedCompleteReal : Set₁ where
  infix 12 _≈_
  infixl 20 _+_ _-_
  infixl 30 _*_
  infix 15 _≤_ _<_
  field
    Carrier : Set
    _≈_ : Carrier → Carrier → Set

    ≈-refl : ∀ {x} → x ≈ x
    ≈-sym : ∀ {x y} → x ≈ y → y ≈ x
    ≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

    zero one : Carrier
    _+_ _-_ _*_ : Carrier → Carrier → Carrier
    neg abs : Carrier → Carrier
    _≤_ _<_ : Carrier → Carrier → Set

    addCong : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a + b) ≈ (a′ + b′)
    subCong : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a - b) ≈ (a′ - b′)
    mulCong : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a * b) ≈ (a′ * b′)
    negCong : ∀ {a b} → a ≈ b → neg a ≈ neg b
    absCong : ∀ {a b} → a ≈ b → abs a ≈ abs b

    leResp : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → a ≤ b → a′ ≤ b′
    ltResp : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → a < b → a′ < b′

    orderedFieldLaws : Set

    Sequence : Set
    sequenceAt : Sequence → Nat → Carrier
    IsCauchy : Sequence → Set
    ConvergesTo : Sequence → Carrier → Set
    cauchyLimit : (s : Sequence) → IsCauchy s → Σ Carrier (λ x → ConvergesTo s x)
    limitUnique : ∀ {s x y} → ConvergesTo s x → ConvergesTo s y → x ≈ y

open SetoidOrderedCompleteReal public

record FunctionSequenceRealization
    (R : SetoidOrderedCompleteReal) : Set₁ where
  field
    fromFunction : (Nat → Carrier R) → Sequence R
    sequenceAtFromFunction : ∀ f n → _≈_ R (sequenceAt R (fromFunction f) n) (f n)

open FunctionSequenceRealization public

------------------------------------------------------------------------
-- Structure-preserving maps and equivalences.
------------------------------------------------------------------------

record SetoidRealMorphism
    (Source Target : SetoidOrderedCompleteReal) : Set₁ where
  field
    map : Carrier Source → Carrier Target
    respectsEquality : ∀ {x y} → _≈_ Source x y → _≈_ Target (map x) (map y)
    preservesZero : _≈_ Target (map (zero Source)) (zero Target)
    preservesOne : _≈_ Target (map (one Source)) (one Target)
    preservesAdd : ∀ x y → _≈_ Target (map (_+_ Source x y)) (_+_ Target (map x) (map y))
    preservesSub : ∀ x y → _≈_ Target (map (_-_ Source x y)) (_-_ Target (map x) (map y))
    preservesMul : ∀ x y → _≈_ Target (map (_*_ Source x y)) (_*_ Target (map x) (map y))
    preservesNeg : ∀ x → _≈_ Target (map (neg Source x)) (neg Target (map x))
    preservesAbs : ∀ x → _≈_ Target (map (abs Source x)) (abs Target (map x))
    preservesLe : ∀ {x y} → _≤_ Source x y → _≤_ Target (map x) (map y)
    preservesLt : ∀ {x y} → _<_ Source x y → _<_ Target (map x) (map y)

open SetoidRealMorphism public

record SetoidRealEquivalence
    (Left Right : SetoidOrderedCompleteReal) : Set₁ where
  field
    toRight : SetoidRealMorphism Left Right
    toLeft : SetoidRealMorphism Right Left
    leftRoundTrip : ∀ x → _≈_ Left (map toLeft (map toRight x)) x
    rightRoundTrip : ∀ y → _≈_ Right (map toRight (map toLeft y)) y
    reflectsLe : ∀ {x y} → _≤_ Right (map toRight x) (map toRight y) → _≤_ Left x y
    reflectsLt : ∀ {x y} → _<_ Right (map toRight x) (map toRight y) → _<_ Left x y

open SetoidRealEquivalence public

------------------------------------------------------------------------
-- Explicit quotient seam into the older propositional-equality contract.
------------------------------------------------------------------------

record PropositionalQuotientRealization
    (R : SetoidOrderedCompleteReal) : Set₁ where
  field
    Quotient : Set
    quotient : Carrier R → Quotient
    quotientSound : ∀ {x y} → _≈_ R x y → quotient x ≡ quotient y
    quotientComplete : ∀ value → Σ (Carrier R) (λ x → quotient x ≡ value)

    zeroQ oneQ : Quotient
    addQ subQ mulQ : Quotient → Quotient → Quotient
    negQ absQ : Quotient → Quotient
    leQ ltQ : Quotient → Quotient → Set

    operationsAgree : Set
    orderedFieldLawsQ : Set

    SequenceQ : Set
    sequenceAtQ : SequenceQ → Nat → Quotient
    IsCauchyQ : SequenceQ → Set
    ConvergesToQ : SequenceQ → Quotient → Set
    cauchyLimitQ : (s : SequenceQ) → IsCauchyQ s → Σ Quotient (λ x → ConvergesToQ s x)

    addAssocQ : ∀ a b c → addQ (addQ a b) c ≡ addQ a (addQ b c)
    addCommQ : ∀ a b → addQ a b ≡ addQ b a
    addZeroLeftQ : ∀ a → addQ zeroQ a ≡ a
    addZeroRightQ : ∀ a → addQ a zeroQ ≡ a
    mulAssocQ : ∀ a b c → mulQ (mulQ a b) c ≡ mulQ a (mulQ b c)
    mulCommQ : ∀ a b → mulQ a b ≡ mulQ b a
    mulOneLeftQ : ∀ a → mulQ oneQ a ≡ a
    mulOneRightQ : ∀ a → mulQ a oneQ ≡ a
    distribLeftQ : ∀ a b c → mulQ a (addQ b c) ≡ addQ (mulQ a b) (mulQ a c)
    distribRightQ : ∀ a b c → mulQ (addQ a b) c ≡ addQ (mulQ a c) (mulQ b c)
    subSelfQ : ∀ a → subQ a a ≡ zeroQ

open PropositionalQuotientRealization public

asLegacyConstructedReal :
  ∀ {R} → PropositionalQuotientRealization R → Legacy.ConstructedOrderedCompleteReal
asLegacyConstructedReal quotientData = record
  { Real = Quotient quotientData
  ; zero = zeroQ quotientData
  ; one = oneQ quotientData
  ; _+_ = addQ quotientData
  ; _-_ = subQ quotientData
  ; _*_ = mulQ quotientData
  ; neg = negQ quotientData
  ; abs = absQ quotientData
  ; _≤_ = leQ quotientData
  ; _<_ = ltQ quotientData
  ; addAssoc = addAssocQ quotientData
  ; addComm = addCommQ quotientData
  ; addZeroLeft = addZeroLeftQ quotientData
  ; addZeroRight = addZeroRightQ quotientData
  ; mulAssoc = mulAssocQ quotientData
  ; mulComm = mulCommQ quotientData
  ; mulOneLeft = mulOneLeftQ quotientData
  ; mulOneRight = mulOneRightQ quotientData
  ; distribLeft = distribLeftQ quotientData
  ; distribRight = distribRightQ quotientData
  ; subSelf = subSelfQ quotientData
  ; Sequence = SequenceQ quotientData
  ; sequenceAt = sequenceAtQ quotientData
  ; IsCauchy = IsCauchyQ quotientData
  ; ConvergesTo = ConvergesToQ quotientData
  ; cauchyLimit = cauchyLimitQ quotientData
  }

record ConstructiveRealBackend : Set₁ where
  field
    backendName : String
    real : SetoidOrderedCompleteReal
    functionSequences : FunctionSequenceRealization real
    quotientOptional : Set

open ConstructiveRealBackend public

setoidBackendSpineLevel : ProofLevel
setoidBackendSpineLevel = machineChecked

legacyQuotientAdapterLevel : ProofLevel
legacyQuotientAdapterLevel = machineChecked
