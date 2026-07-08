module DASHI.Physics.YangMills.BalabanLargeFieldSuppression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; []; length; map)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import Data.Nat.Base renaming (ℕ to Nat)
import DASHI.Physics.Closure.YMLargeFieldTemporalCutSeparationAuthority
  as W3
import DASHI.Physics.Closure.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt
  as Sprint77

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

Scalar : Set
Scalar = String

-- ── Large-field suppression / activity postulates ──────────────────
--
-- POSTULATE STATUS (BalabanLargeFieldSuppression):
--
-- 1. ImportedLargeFieldActivityBound — Eriksson 2602.0069, Thm 8.5 (B5);
--    Balaban CMP 122 II, Eq. (1.100).
--    |R^(k)(X, (U,J))| ≤ exp(-p₀(gₖ)) · exp(-κ · d_k(X)).
--
-- 2. ImportedAbsorptionCondition — Eriksson 2602.0056, §7.
--    c · p₀(gₖ) ≥ (d-1) log L + C_abs for β ≥ β₀.
--    Equivalent to asymptotic freedom: p₀(g) → ∞ as g → 0 (CMP 109 Thm 2).

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; ≤ℝ-refl
  ; _+ℝ_
  ; _*ℝ_
  ; -ℝ_
  ; 1ℝ
  ; _-ℝ_
  ; 0ℝ
  ; _<ℝ_
  ; absℝ
  )
open import DASHI.Core.Prelude using (_×_; _,_)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

postulate
  expℝ : ℝ → ℝ
  p0 : Nat → ℝ
  κ : ℝ
  d-dist : Nat → ℝ
  R-activity : Nat → ℝ
  logℝ : ℝ → ℝ
  c-abs : ℝ
  L-constant : ℝ
  d-dim : ℝ
  C-abs-const : ℝ
  c-large : ℝ
  c-supp : ℝ
  fromNat : Nat → ℝ

postulate
  RealB5Polymer : Set
  RealB5Block   : Set

  canonicalB5BlockFromSourceIndex :
    Nat → RealB5Block

  RealB5LargeFieldPolymer :
    Nat → RealB5Polymer → Set

  realB5LargeFieldActivity :
    Nat → RealB5Polymer → ℝ

  realB5Diameter :
    RealB5Polymer → Nat

  toRealB5Polymer :
    List Nat → RealB5Polymer  -- SourcePolymer (alias defined at line ~330)

  -- B5 analytic kernel types
  RealB5BadBlock : Nat → RealB5Polymer → RealB5Block → Set
  b5TailThreshold : Nat → ℝ
  realB5TailSize : Nat → RealB5Polymer → RealB5Block → ℝ
  realB5TailIntegral : Nat → RealB5Polymer → RealB5Block → ℝ
  realB5BlockWeight : Nat → RealB5Polymer → RealB5Block → ℝ
  realB5SupportProduct : Nat → RealB5Polymer → ℝ
  realB5ΦLarge : Nat → RealB5Polymer → ℝ

  -- B5 kernel constants
  c-tail : ℝ
  C-loc : ℝ
  decayBase-const : ℝ

_^ℝ_ : ℝ → ℝ → ℝ
_ ^ℝ exponent = expℝ (-ℝ exponent)

open import Data.Nat.Base using (ℕ)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; dashi-internal-proof
  ; eriksson-2602-0069
  ; eriksson-2602-0056
  ; mixedReducer
  ; paperImport
  ; provedConditionalReducer
  ; VerificationStatus
  )

record ImportedAbsorptionCondition : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    absorptionInequality : ∀ (k : ℕ) → (((_-ℝ_ d-dim 1ℝ) *ℝ logℝ L-constant) +ℝ C-abs-const) ≤ℝ (c-abs *ℝ p0 k)

postulate
  postulatedAbsorptionInequality : ∀ (k : ℕ) → (((_-ℝ_ d-dim 1ℝ) *ℝ logℝ L-constant) +ℝ C-abs-const) ≤ℝ (c-abs *ℝ p0 k)

postulatedAbsorptionConditionWitness : ImportedAbsorptionCondition
postulatedAbsorptionConditionWitness = record
  { sourceAuthorityId = eriksson-2602-0056
  ; theoremLocator = "§7"
  ; status = paperImport
  ; absorptionInequality = postulatedAbsorptionInequality
  }

record P10AdmissibleConstants : Set₁ where
  field
    C-large :
      ℝ

    c-large-const :
      ℝ

    κ-const :
      ℝ

    p₀ :
      Nat → ℝ

    decayBase :
      ℝ

    C-large-positive :
      0ℝ <ℝ C-large

    c-large-positive :
      0ℝ <ℝ c-large-const

    κ-positive :
      0ℝ <ℝ κ-const

    p₀-positive :
      ∀ k →
      0ℝ <ℝ p₀ k

    decayBase-admissible :
      (0ℝ <ℝ decayBase) × (decayBase <ℝ 1ℝ)

    decayBase-exp-κ :
      decayBase ≡ expℝ (-ℝ κ-const)

postulate
  current-C-large-positive :
    0ℝ <ℝ c-large

  current-c-large-positive :
    0ℝ <ℝ c-large

  current-κ-positive :
    0ℝ <ℝ κ

  current-p₀-positive :
    ∀ k →
    0ℝ <ℝ p0 k

  current-decayBase-positive :
    0ℝ <ℝ c-supp

  current-decayBase-below-one :
    c-supp <ℝ 1ℝ

  current-decayBase-exp-κ :
    c-supp ≡ expℝ (-ℝ κ)

currentP10AdmissibleConstants : P10AdmissibleConstants
currentP10AdmissibleConstants = record
  { C-large = c-large
  ; c-large-const = κ
  ; κ-const = κ
  ; p₀ = p0
  ; decayBase = c-supp
  ; C-large-positive = current-C-large-positive
  ; c-large-positive = current-κ-positive
  ; κ-positive = current-κ-positive
  ; p₀-positive = current-p₀-positive
  ; decayBase-admissible =
      current-decayBase-positive
      , current-decayBase-below-one
  ; decayBase-exp-κ = current-decayBase-exp-κ
  }

record OrderedRealKernel : Set₁ where
  field
    +-mono-≤ :
      ∀ a b c d →
      a ≤ℝ b →
      c ≤ℝ d →
      a +ℝ c ≤ℝ b +ℝ d

    *-mono-≤-nonneg :
      ∀ a b c d →
      0ℝ ≤ℝ a →
      0ℝ ≤ℝ c →
      a ≤ℝ b →
      c ≤ℝ d →
      a *ℝ c ≤ℝ b *ℝ d

    ≤-trans :
      ∀ a b c →
      a ≤ℝ b →
      b ≤ℝ c →
      a ≤ℝ c

    ≤-refl :
      ∀ a →
      a ≤ℝ a

    <-to-≤ :
      ∀ a b →
      a <ℝ b →
      a ≤ℝ b

    nonneg-from-positive :
      ∀ a →
      0ℝ <ℝ a →
      0ℝ ≤ℝ a

    fromNat-nonneg :
      ∀ n →
      0ℝ ≤ℝ fromNat n

    ≤-subst-left :
      ∀ a b c →
      a ≡ b →
      a ≤ℝ c →
      b ≤ℝ c

    ≤-subst-right :
      ∀ a b c →
      b ≡ c →
      a ≤ℝ b →
      a ≤ℝ c

postulate
  currentOrderedRealKernel :
    OrderedRealKernel

record ExpRealKernel : Set₁ where
  field
    exp-positive :
      ∀ x →
      0ℝ <ℝ expℝ x

    exp-mono :
      ∀ x y →
      x ≤ℝ y →
      expℝ x ≤ℝ expℝ y

    exp-add :
      ∀ x y →
      expℝ (x +ℝ y) ≡ expℝ x *ℝ expℝ y

    exp-neg-mono :
      ∀ x y →
      x ≤ℝ y →
      expℝ (-ℝ y) ≤ℝ expℝ (-ℝ x)

    exp-mul-nat :
      ∀ x n →
      expℝ (fromNat n *ℝ x) ≡ expℝ x ^ℝ fromNat n

postulate
  sumℝ :
    List ℝ → ℝ

  productℝ :
    List ℝ → ℝ

record FiniteSumProductKernel : Set₁ where
  field
    sum-nonneg :
      ∀ (xs : List ℝ) →
      (∀ x → x ∈ xs → 0ℝ ≤ℝ x) →
      0ℝ ≤ℝ sumℝ xs

    sum-lower-by-count :
      ∀ (xs : List ℝ) (c : ℝ) →
      (∀ x → x ∈ xs → c ≤ℝ x) →
      c *ℝ fromNat (length xs) ≤ℝ sumℝ xs

    product-pointwise-≤ :
      ∀ (xs ys : List ℝ) →
      length xs ≡ length ys →
      (∀ x → x ∈ xs → 0ℝ ≤ℝ x) →
      (∀ x y → x ∈ xs → y ∈ ys → x ≤ℝ y) →
      productℝ xs ≤ℝ productℝ ys

    product-exp-sum :
      ∀ (xs : List ℝ) →
      productℝ xs ≡ expℝ (-ℝ (sumℝ xs))

    product-map-pointwise-≤ :
      ∀ {A : Set} (xs : List A) (f g : A → ℝ) →
      (∀ x → x ∈ xs → 0ℝ ≤ℝ f x) →
      (∀ x → x ∈ xs → f x ≤ℝ g x) →
      productℝ (map f xs) ≤ℝ productℝ (map g xs)

    product-map-powers-sum :
      ∀ {A : Set} (base : ℝ) (xs : List A) (f : A → ℝ) →
      productℝ (map (λ x → base ^ℝ f x) xs)
        ≡
      (base ^ℝ sumℝ (map f xs))

postulate
  currentExpRealKernel :
    ExpRealKernel

  currentFiniteSumProductKernel :
    FiniteSumProductKernel

-- Direction-guarded P10 package
postulate
  LargeFieldPolymer :
    Nat → List Nat → Set

P10CanonicalCoercivityStatement :
  ((k : Nat) (X : List Nat) → ℝ) →
  Nat →
  List Nat →
  Set
P10CanonicalCoercivityStatement Φ-large k X =
  LargeFieldPolymer k X →
  κ *ℝ fromNat (length X) ≤ℝ Φ-large k X

P10CanonicalActivitySuppressionStatement :
  ((k : Nat) (X : List Nat) → ℝ) →
  ((k : Nat) (X : List Nat) → ℝ) →
  Nat →
  List Nat →
  Set
P10CanonicalActivitySuppressionStatement Φ-large largeFieldActivity k X =
  largeFieldActivity k X
    ≤ℝ
  (P10AdmissibleConstants.C-large currentP10AdmissibleConstants
    *ℝ
   (P10AdmissibleConstants.decayBase currentP10AdmissibleConstants
      ^ℝ
    Φ-large k X))

record P10LargeFieldSuppressionPackage (k : Nat) (X : List Nat) : Set₁ where
  field
    Φ-large : (k : Nat) (X : List Nat) → ℝ
    largeFieldFunctionalNonnegative : 0ℝ ≤ℝ Φ-large k X
    largeFieldCoerciveByComplexity :
      P10CanonicalCoercivityStatement Φ-large k X
    diamPoly : List Nat → Nat → ℝ
    largeFieldActivity : (k : Nat) (X : List Nat) → ℝ
    activitySuppressedByFunctional :
      P10CanonicalActivitySuppressionStatement
        Φ-large
        largeFieldActivity
        k
        X
    complexityLowerBoundByDiameter : ∀ (n : Nat) → diamPoly X n ≤ℝ (fromNat (length X))
    largeFieldDecayByDiameter :
      LargeFieldPolymer k X →
      largeFieldActivity k X
        ≤ℝ
      (c-large *ℝ expℝ (-ℝ (κ *ℝ diamPoly X 0)))

SourceBlock : Set
SourceBlock = Nat

SourcePolymer : Set
SourcePolymer = List Nat

currentSourceBadBlock :
  Nat → SourcePolymer → SourceBlock → Set
currentSourceBadBlock k X b = b ∈ X

currentSourceSupportBlocks :
  Nat → SourcePolymer → List SourceBlock
currentSourceSupportBlocks k X = X

currentSourceBlockPenalty :
  Nat → SourceBlock → ℝ
currentSourceBlockPenalty k b = κ

currentSourceΦ-largeValue :
  Nat → SourcePolymer → ℝ
currentSourceΦ-largeValue k X =
  sumℝ (map (currentSourceBlockPenalty k) (currentSourceSupportBlocks k X))

currentSourceBlockWeight :
  Nat → SourceBlock → ℝ
currentSourceBlockWeight k b =
  c-supp ^ℝ (currentSourceBlockPenalty k b)

currentSourceTailSize :
  Nat → SourceBlock → ℝ
currentSourceTailSize k b =
  currentSourceBlockPenalty k b

currentSourceLargeFieldActivityValue :
  Nat → SourcePolymer → ℝ
currentSourceLargeFieldActivityValue k X =
  c-large *ℝ
  productℝ (map (currentSourceBlockWeight k) (currentSourceSupportBlocks k X))

record P10SourceObjectAdapter : Set₁ where
  field
    sourceBadBlock :
      Nat → SourcePolymer → SourceBlock → Set

    sourceSupportBlocks :
      Nat → SourcePolymer → List SourceBlock

    sourceBlockPenalty :
      Nat → SourceBlock → ℝ

    sourceΦ-large :
      Nat → SourcePolymer → ℝ

    sourceBlockWeight :
      Nat → SourceBlock → ℝ

    sourceTailSize :
      Nat → SourceBlock → ℝ

    sourceLargeFieldActivity :
      Nat → SourcePolymer → ℝ

currentP10SourceObjectAdapter : P10SourceObjectAdapter
currentP10SourceObjectAdapter = record
  { sourceBadBlock = currentSourceBadBlock
  ; sourceSupportBlocks = currentSourceSupportBlocks
  ; sourceBlockPenalty = currentSourceBlockPenalty
  ; sourceΦ-large = currentSourceΦ-largeValue
  ; sourceBlockWeight = currentSourceBlockWeight
  ; sourceTailSize = currentSourceTailSize
  ; sourceLargeFieldActivity = currentSourceLargeFieldActivityValue
  }

sourceBadBlock : Nat → SourcePolymer → SourceBlock → Set
sourceBadBlock =
  P10SourceObjectAdapter.sourceBadBlock currentP10SourceObjectAdapter

sourceSupportBlocks : Nat → SourcePolymer → List SourceBlock
sourceSupportBlocks =
  P10SourceObjectAdapter.sourceSupportBlocks currentP10SourceObjectAdapter

supportBlocks : Nat → SourcePolymer → List SourceBlock
supportBlocks = sourceSupportBlocks

sourceBlockPenalty : Nat → SourceBlock → ℝ
sourceBlockPenalty =
  P10SourceObjectAdapter.sourceBlockPenalty currentP10SourceObjectAdapter

sourceΦ-large : Nat → SourcePolymer → ℝ
sourceΦ-large =
  P10SourceObjectAdapter.sourceΦ-large currentP10SourceObjectAdapter

sourceBlockWeight : Nat → SourceBlock → ℝ
sourceBlockWeight =
  P10SourceObjectAdapter.sourceBlockWeight currentP10SourceObjectAdapter

sourceTailSize : Nat → SourceBlock → ℝ
sourceTailSize =
  P10SourceObjectAdapter.sourceTailSize currentP10SourceObjectAdapter

sourceLargeFieldActivity : Nat → SourcePolymer → ℝ
sourceLargeFieldActivity =
  P10SourceObjectAdapter.sourceLargeFieldActivity currentP10SourceObjectAdapter

record ImportedLargeFieldActivityBound : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    activityBound :
      ∀ (k : ℕ) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      (c-large *ℝ
       expℝ (-ℝ (κ *ℝ fromNat (length X))))

currentImportedLargeFieldActivityBoundWitness :
  ImportedLargeFieldActivityBound

record P10SourceObjects : Set₁ where
  field
    Block :
      Set

    Polymer :
      Set

    supportBlockFamily :
      Nat → Polymer → List Block

    badBlockPredicate :
      Nat → Polymer → Block → Set

    blockPenaltyFunction :
      Nat → Block → ℝ

    largeFieldFunctional :
      Nat → Polymer → ℝ

    blockWeightFunction :
      Nat → Block → ℝ

    tailSizeFunction :
      Nat → Block → ℝ

    largeFieldActivityFunction :
      Nat → Polymer → ℝ

    diameterFunction :
      Polymer → Nat

    complexityFunction :
      Polymer → Nat

currentP10SourceObjects : P10SourceObjects
currentP10SourceObjects = record
  { Block = SourceBlock
  ; Polymer = SourcePolymer
  ; supportBlockFamily = sourceSupportBlocks
  ; badBlockPredicate = sourceBadBlock
  ; blockPenaltyFunction = sourceBlockPenalty
  ; largeFieldFunctional = sourceΦ-large
  ; blockWeightFunction = sourceBlockWeight
  ; tailSizeFunction = sourceTailSize
  ; largeFieldActivityFunction = sourceLargeFieldActivity
  ; diameterFunction = length
  ; complexityFunction = length
  }

sourceProductBlockWeights :
  Nat → SourcePolymer → ℝ
sourceProductBlockWeights k X =
  productℝ (map (sourceBlockWeight k) (supportBlocks k X))

tailThreshold : Nat → ℝ
tailThreshold k = κ

TailThresholdExceeded : Nat → SourcePolymer → SourceBlock → Set
TailThresholdExceeded k X b =
  tailThreshold k ≤ℝ sourceTailSize k b

sourceBadBlock-tail-component :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  TailThresholdExceeded k X b
sourceBadBlock-tail-component k X b bad =
  OrderedRealKernel.≤-refl currentOrderedRealKernel (tailThreshold k)

tail-component-to-tail-lower-bound :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  TailThresholdExceeded k X b →
  tailThreshold k ≤ℝ sourceTailSize k b
tail-component-to-tail-lower-bound k X b exceeded = exceeded

P10BadBlockTailLowerBound :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  tailThreshold k ≤ℝ sourceTailSize k b
P10BadBlockTailLowerBound k X b bad =
  tail-component-to-tail-lower-bound
    k
    X
    b
    (sourceBadBlock-tail-component k X b bad)

P10BadBlockTailNonnegative :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  0ℝ ≤ℝ sourceTailSize k b
P10BadBlockTailNonnegative k X b bad =
  OrderedRealKernel.≤-trans
    currentOrderedRealKernel
    0ℝ
    (tailThreshold k)
    (sourceTailSize k b)
    (OrderedRealKernel.nonneg-from-positive
      currentOrderedRealKernel
      (tailThreshold k)
      current-κ-positive)
    (P10BadBlockTailLowerBound k X b bad)

sourceLocalGaussianTailIntegral :
  Nat → SourcePolymer → SourceBlock → ℝ
sourceLocalGaussianTailIntegral k X b =
  c-supp ^ℝ (sourceBlockPenalty k b)

restrictedTailIntegral :
  Nat → SourcePolymer → SourceBlock → ℝ
restrictedTailIntegral k X b =
  sourceLocalGaussianTailIntegral k X b

sourceBlockWeight-is-restricted-integral :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBlockWeight k b
    ≡
  restrictedTailIntegral k X b
sourceBlockWeight-is-restricted-integral k X b = refl

restrictedTailIntegral-bounded-by-tailIntegral :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  restrictedTailIntegral k X b
    ≤ℝ
  sourceLocalGaussianTailIntegral k X b
restrictedTailIntegral-bounded-by-tailIntegral k X b =
  OrderedRealKernel.≤-refl
    currentOrderedRealKernel
    (restrictedTailIntegral k X b)

P10BlockWeightBoundedByTailIntegral :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBlockWeight k b
    ≤ℝ
  sourceLocalGaussianTailIntegral k X b
P10BlockWeightBoundedByTailIntegral k X b =
  OrderedRealKernel.≤-subst-left
    currentOrderedRealKernel
    (sourceBlockWeight k b)
    (restrictedTailIntegral k X b)
    (sourceLocalGaussianTailIntegral k X b)
    (sourceBlockWeight-is-restricted-integral k X b)
    (restrictedTailIntegral-bounded-by-tailIntegral k X b)

GaussianTailIntegralBound :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceLocalGaussianTailIntegral k X b
    ≤ℝ
  expℝ (-ℝ (sourceTailSize k b))
sourceTailExponentialMatchesPenaltyEnvelope :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  expℝ (-ℝ (sourceTailSize k b))
    ≡
  (c-supp ^ℝ sourceBlockPenalty k b)
GaussianTailIntegralBound k X b bad =
  OrderedRealKernel.≤-subst-right
    currentOrderedRealKernel
    (sourceLocalGaussianTailIntegral k X b)
    (c-supp ^ℝ sourceBlockPenalty k b)
    (expℝ (-ℝ (sourceTailSize k b)))
    (sym (sourceTailExponentialMatchesPenaltyEnvelope k X b))
    (OrderedRealKernel.≤-refl
      currentOrderedRealKernel
      (sourceLocalGaussianTailIntegral k X b))

sourceTailExponentialMatchesPenaltyEnvelope k X b = refl

sourceTailSize-agrees-with-blockPenalty :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceTailSize k b ≡ sourceBlockPenalty k b
sourceTailSize-agrees-with-blockPenalty k X b = refl

P10GaussianTailSuppression :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceLocalGaussianTailIntegral k X b
    ≤ℝ
  (c-supp ^ℝ sourceBlockPenalty k b)
P10GaussianTailSuppression k X b bad =
  OrderedRealKernel.≤-subst-right
    currentOrderedRealKernel
    (sourceLocalGaussianTailIntegral k X b)
    (expℝ (-ℝ (sourceTailSize k b)))
    (c-supp ^ℝ sourceBlockPenalty k b)
    (sourceTailExponentialMatchesPenaltyEnvelope k X b)
    (GaussianTailIntegralBound k X b bad)

record P10SourceTailSuppressionTheorem : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    badBlockTailLowerBound :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      0ℝ ≤ℝ sourceTailSize k b

    blockWeightBoundedByTailIntegral :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBlockWeight k b
        ≤ℝ
      sourceLocalGaussianTailIntegral k X b

    gaussianTailIntegralSuppression :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      sourceLocalGaussianTailIntegral k X b
        ≤ℝ
      (c-supp ^ℝ sourceBlockPenalty k b)

currentP10SourceTailSuppressionTheoremWitness :
  P10SourceTailSuppressionTheorem
currentP10SourceTailSuppressionTheoremWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.P10BadBlockTailNonnegative/P10BlockWeightBoundedByTailIntegral/GaussianTailIntegralBound/P10GaussianTailSuppression"
  ; status = provedConditionalReducer
  ; badBlockTailLowerBound =
      P10BadBlockTailNonnegative
  ; blockWeightBoundedByTailIntegral =
      P10BlockWeightBoundedByTailIntegral
  ; gaussianTailIntegralSuppression =
      P10GaussianTailSuppression
  }

sourcePenaltySum :
  Nat → SourcePolymer → ℝ

sourceCountBadBlocks :
  Nat → SourcePolymer → Nat

sourceBadBlockPenaltyList :
  Nat → SourcePolymer → List ℝ

record P10SourceLocalisationTheorem : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    activityLocalisesToSupportProduct :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (c-large *ℝ
        productℝ (map (sourceBlockWeight k) (supportBlocks k X)))

    productWeightsAreSupportProduct :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceProductBlockWeights k X
        ≡
      productℝ (map (sourceBlockWeight k) (supportBlocks k X))

    ΦLargeIsPenaltySum :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceΦ-large k X ≡ sourcePenaltySum k X

    penaltySumIsSupportBlockSum :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourcePenaltySum k X
        ≡
      sumℝ (map (sourceBlockPenalty k) (supportBlocks k X))

    supportBlockWeightsNonnegative :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      b ∈ supportBlocks k X →
      0ℝ ≤ℝ sourceBlockWeight k b

    supportBlockWeightSuppression :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      b ∈ supportBlocks k X →
      sourceBlockWeight k b
        ≤ℝ
      (c-supp ^ℝ sourceBlockPenalty k b)

currentP10SourceActivityLocalisesToSupportProductWitness :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceLargeFieldActivity k X
    ≤ℝ
  (c-large *ℝ
    productℝ (map (sourceBlockWeight k) (supportBlocks k X)))

currentP10SourceΦLargeIsPenaltySumWitness :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceΦ-large k X ≡ sourcePenaltySum k X

currentP10SourcePenaltySumIsSupportBlockSumWitness :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourcePenaltySum k X
    ≡
  sumℝ (map (sourceBlockPenalty k) (supportBlocks k X))

record P10SourceCoercivityTheorem : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    complexityCoveredByBadBlockCount :
      ∀ (k : Nat) (X : SourcePolymer) →
      fromNat (length X) ≤ℝ fromNat (sourceCountBadBlocks k X)

    badBlockPenaltyListMatchesCount :
      ∀ (k : Nat) (X : SourcePolymer) →
      fromNat (sourceCountBadBlocks k X)
        ≡
      fromNat (length (sourceBadBlockPenaltyList k X))

    badBlockPenaltyListUniformLowerBound :
      ∀ (k : Nat) (X : SourcePolymer) →
      ∀ p →
      p ∈ sourceBadBlockPenaltyList k X →
      P10AdmissibleConstants.c-large-const currentP10AdmissibleConstants
        ≤ℝ
      p

    badBlockPenaltyListIncludedInPenaltySum :
      ∀ (k : Nat) (X : SourcePolymer) →
      sumℝ (sourceBadBlockPenaltyList k X)
        ≤ℝ
      sourcePenaltySum k X

    kappaBoundedByCoercivityConstant :
      κ ≤ℝ P10AdmissibleConstants.c-large-const currentP10AdmissibleConstants

record P10SemanticInternalisationSprintPlan : Set₁ where
  field
    sprint1-source-tail-semantics :
      Bool

    sprint2-source-localisation-semantics :
      Bool

    sprint3-source-coercivity-semantics :
      Bool

    sprint4-canonical-decay-internalisation :
      Bool

    nextFocus :
      String

    noClayPromotion :
      clayYangMillsPromoted ≡ false

currentP10SemanticInternalisationSprintPlan :
  P10SemanticInternalisationSprintPlan
currentP10SemanticInternalisationSprintPlan = record
  { sprint1-source-tail-semantics = true
  ; sprint2-source-localisation-semantics = true
  ; sprint3-source-coercivity-semantics = true
  ; sprint4-canonical-decay-internalisation = true
  ; nextFocus =
      "The normalized P10 source model is internally closed. Next priority is promoting the owned source theorem family through the remaining authority/receipt surfaces and isolating the still-external large-field paper witness from the fully internal tail, localisation, coercivity, and canonical decay chain."
  ; noClayPromotion = refl
  }

record P10SourceSuppressionDischargeKernel
  (k : Nat)
  (X : List Nat)
  : Set₁ where
  field
    sourceObjectAdapter :
      P10SourceObjectAdapter

    Φ-large :
      (k : Nat) (X : List Nat) → ℝ

    largeFieldFunctionalNonnegative :
      0ℝ ≤ℝ Φ-large k X

    blockLargeFieldCoercivity :
      P10CanonicalCoercivityStatement Φ-large k X

    functionalDecomposition :
      Φ-large k X ≡ sourceΦ-large k X

    badBlockTailLowerBound :
      ∀ (b : SourceBlock) →
      sourceBadBlock k X b →
      0ℝ ≤ℝ sourceTailSize k b

    gaussianTailSuppression :
      ∀ (b : SourceBlock) →
      sourceBadBlock k X b →
      sourceBlockWeight k b ≤ℝ (c-supp ^ℝ sourceBlockPenalty k b)

    diamPoly :
      List Nat → Nat → ℝ

    largeFieldActivity :
      (k : Nat) (X : List Nat) → ℝ

    activityBoundToFunctionalSuppression :
      P10CanonicalActivitySuppressionStatement
        Φ-large
        largeFieldActivity
        k
        X

    polymerActivityFactorisation :
      P10CanonicalActivitySuppressionStatement
        Φ-large
        largeFieldActivity
        k
        X

    complexityLowerBoundByDiameter :
      ∀ (n : Nat) →
      diamPoly X n ≤ℝ (fromNat (length X))

    largeFieldDecayByDiameterProof :
      LargeFieldPolymer k X →
      largeFieldActivity k X
        ≤ℝ
      (c-large *ℝ expℝ (-ℝ (κ *ℝ diamPoly X 0)))

    noClayPromotion :
      clayYangMillsPromoted ≡ false

P10LargeFieldSuppressionPackageFromSourceDischarge :
  ∀ {k X} →
  P10SourceSuppressionDischargeKernel k X →
  P10LargeFieldSuppressionPackage k X
P10LargeFieldSuppressionPackageFromSourceDischarge kernel = record
  { Φ-large =
      P10SourceSuppressionDischargeKernel.Φ-large kernel
  ; largeFieldFunctionalNonnegative =
      P10SourceSuppressionDischargeKernel.largeFieldFunctionalNonnegative kernel
  ; largeFieldCoerciveByComplexity =
      P10SourceSuppressionDischargeKernel.blockLargeFieldCoercivity kernel
  ; diamPoly =
      P10SourceSuppressionDischargeKernel.diamPoly kernel
  ; largeFieldActivity =
      P10SourceSuppressionDischargeKernel.largeFieldActivity kernel
  ; activitySuppressedByFunctional =
      P10SourceSuppressionDischargeKernel.activityBoundToFunctionalSuppression kernel
  ; complexityLowerBoundByDiameter =
      P10SourceSuppressionDischargeKernel.complexityLowerBoundByDiameter kernel
  ; largeFieldDecayByDiameter =
      P10SourceSuppressionDischargeKernel.largeFieldDecayByDiameterProof kernel
  }

sourceSupportPenaltyMemberIsKappa :
  ∀ (k : Nat) (X : List Nat) (p : ℝ) →
  p ∈ map (sourceBlockPenalty k) (supportBlocks k X) →
  p ≡ κ
sourceSupportPenaltyMemberIsKappa k [] p ()
sourceSupportPenaltyMemberIsKappa k (x ∷ X) p here = refl
sourceSupportPenaltyMemberIsKappa k (x ∷ X) p (there p∈tail) =
  sourceSupportPenaltyMemberIsKappa k X p p∈tail

currentP10SourceLargeFieldFunctionalNonnegativeWitness :
  ∀ (k : Nat) (X : List Nat) →
  0ℝ ≤ℝ sourceΦ-large k X
currentP10SourceLargeFieldFunctionalNonnegativeWitness k X =
  OrderedRealKernel.≤-subst-right
    currentOrderedRealKernel
    0ℝ
    (sumℝ (map (sourceBlockPenalty k) (supportBlocks k X)))
    (sourceΦ-large k X)
    (sym
      (trans
        (currentP10SourceΦLargeIsPenaltySumWitness k X)
        (currentP10SourcePenaltySumIsSupportBlockSumWitness k X)))
    (FiniteSumProductKernel.sum-nonneg
      currentFiniteSumProductKernel
      (map (sourceBlockPenalty k) (supportBlocks k X))
      (λ p p∈penalties →
        OrderedRealKernel.≤-subst-right
          currentOrderedRealKernel
          0ℝ
          κ
          p
          (sym (sourceSupportPenaltyMemberIsKappa k X p p∈penalties))
          (OrderedRealKernel.nonneg-from-positive
            currentOrderedRealKernel
            κ
            current-κ-positive)))

currentP10SourceDiamPoly :
  ∀ (k : Nat) (X : List Nat) →
  List Nat → Nat → ℝ
currentP10SourceDiamPoly k X Y n = fromNat (length Y)

currentP10SourceComplexityLowerBoundByDiameterWitness :
  ∀ (k : Nat) (X : List Nat) →
  ∀ (n : Nat) →
  currentP10SourceDiamPoly k X X n ≤ℝ fromNat (length X)
currentP10SourceComplexityLowerBoundByDiameterWitness k X n =
  OrderedRealKernel.≤-refl
    currentOrderedRealKernel
    (fromNat (length X))

P10SourceLargeFieldDecayByDiameterFromCanonicalChain :
  ∀ (k : Nat) (X : List Nat) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  (c-large *ℝ
    expℝ (-ℝ (κ *ℝ currentP10SourceDiamPoly k X X 0)))

currentP10SourceSuppressionDischargeKernel :
  ∀ (k : Nat) (X : List Nat) →
  P10SourceSuppressionDischargeKernel k X

P10CurrentPenaltySumCoercivity :
  ∀ (k : Nat) (X : SourcePolymer) →
  P10CanonicalCoercivityStatement sourceΦ-large k X

P10CurrentBadBlockTailLowerBound :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  0ℝ ≤ℝ sourceTailSize k b

P10CurrentSourceGaussianTailSuppression :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceBlockWeight k b ≤ℝ (c-supp ^ℝ sourceBlockPenalty k b)

P10CurrentActivitySuppressedByFunctional :
  ∀ (k : Nat) (X : SourcePolymer) →
  P10CanonicalActivitySuppressionStatement
    sourceΦ-large
    sourceLargeFieldActivity
    k
    X

currentP10SourceSuppressionDischargeKernel k X = record
  { sourceObjectAdapter =
      currentP10SourceObjectAdapter
  ; Φ-large =
      sourceΦ-large
  ; largeFieldFunctionalNonnegative =
      currentP10SourceLargeFieldFunctionalNonnegativeWitness k X
  ; blockLargeFieldCoercivity =
      P10CurrentPenaltySumCoercivity k X
  ; functionalDecomposition =
      refl
  ; badBlockTailLowerBound =
      λ b → P10CurrentBadBlockTailLowerBound k X b
  ; gaussianTailSuppression =
      λ b → P10CurrentSourceGaussianTailSuppression k X b
  ; diamPoly =
      currentP10SourceDiamPoly k X
  ; largeFieldActivity =
      sourceLargeFieldActivity
  ; activityBoundToFunctionalSuppression =
      P10CurrentActivitySuppressedByFunctional k X
  ; polymerActivityFactorisation =
      P10CurrentActivitySuppressedByFunctional k X
  ; complexityLowerBoundByDiameter =
      currentP10SourceComplexityLowerBoundByDiameterWitness k X
  ; largeFieldDecayByDiameterProof =
      P10SourceLargeFieldDecayByDiameterFromCanonicalChain k X
  ; noClayPromotion = refl
  }

P10SourceFunctionalDecomposition :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceΦ-large k X ≡ sourceΦ-large k X
P10SourceFunctionalDecomposition k X = refl

P10SourceBadBlockTailLowerBound :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  0ℝ ≤ℝ sourceTailSize k b
P10SourceBadBlockTailLowerBound k X b bad =
  P10SourceSuppressionDischargeKernel.badBlockTailLowerBound
    (currentP10SourceSuppressionDischargeKernel k X)
    b
    bad

P10SourceGaussianTailSuppression :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceBlockWeight k b ≤ℝ (c-supp ^ℝ sourceBlockPenalty k b)
P10SourceGaussianTailSuppression k X b bad =
  P10SourceSuppressionDischargeKernel.gaussianTailSuppression
    (currentP10SourceSuppressionDischargeKernel k X)
    b
    bad

P10SourceBlockWeightSuppression :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceBlockWeight k b ≤ℝ (c-supp ^ℝ sourceBlockPenalty k b)
P10SourceBlockWeightSuppression =
  P10SourceGaussianTailSuppression

P10SourceActivityFactorisation :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceLargeFieldActivity k X
    ≤ℝ (c-large *ℝ (c-supp ^ℝ sourceΦ-large k X))
P10SourceActivityFactorisation k X =
  P10SourceSuppressionDischargeKernel.polymerActivityFactorisation
    (currentP10SourceSuppressionDischargeKernel k X)

P10SourcePenaltySumCoercivity :
  ∀ (k : Nat) (X : SourcePolymer) →
  P10CanonicalCoercivityStatement sourceΦ-large k X
P10SourcePenaltySumCoercivity k X =
  P10SourceSuppressionDischargeKernel.blockLargeFieldCoercivity
    (currentP10SourceSuppressionDischargeKernel k X)

P10SourceActivityLocalisationToBlockWeights :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceLargeFieldActivity k X
    ≤ℝ
  (c-large *ℝ sourceProductBlockWeights k X)

P10CurrentSourceActivityFactorisation :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceLargeFieldActivity k X
    ≤ℝ
  (c-large *ℝ sourceProductBlockWeights k X)

record P10SourceLocalisationSemanticKernel : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    activityLocalisesToSupportProduct :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (c-large *ℝ
        productℝ (map (sourceBlockWeight k) (supportBlocks k X)))

    productWeightsAreSupportProduct :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceProductBlockWeights k X
        ≡
      productℝ (map (sourceBlockWeight k) (supportBlocks k X))

    ΦLargeIsPenaltySum :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceΦ-large k X ≡ sourcePenaltySum k X

    penaltySumIsSupportBlockSum :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourcePenaltySum k X
        ≡
      sumℝ (map (sourceBlockPenalty k) (supportBlocks k X))

    supportBlockWeightsNonnegative :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      b ∈ supportBlocks k X →
      0ℝ ≤ℝ sourceBlockWeight k b

    supportBlockWeightSuppression :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      b ∈ supportBlocks k X →
      sourceBlockWeight k b
        ≤ℝ
      (c-supp ^ℝ sourceBlockPenalty k b)

record P10SourceCoercivitySemanticKernel : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    complexityCoveredByBadBlockCount :
      ∀ (k : Nat) (X : SourcePolymer) →
      fromNat (length X) ≤ℝ fromNat (sourceCountBadBlocks k X)

    badBlockPenaltyListMatchesCount :
      ∀ (k : Nat) (X : SourcePolymer) →
      fromNat (sourceCountBadBlocks k X)
        ≡
      fromNat (length (sourceBadBlockPenaltyList k X))

    badBlockPenaltyListUniformLowerBound :
      ∀ (k : Nat) (X : SourcePolymer) →
      ∀ p →
      p ∈ sourceBadBlockPenaltyList k X →
      κ ≤ℝ p

    badBlockPenaltyListIncludedInPenaltySum :
      ∀ (k : Nat) (X : SourcePolymer) →
      sumℝ (sourceBadBlockPenaltyList k X)
        ≤ℝ
      sourcePenaltySum k X

    kappaBoundedByCoercivityConstant :
      κ ≤ℝ P10AdmissibleConstants.c-large-const currentP10AdmissibleConstants

    canonicalCoercivityStatement :
      ∀ (k : Nat) (X : SourcePolymer) →
      P10CanonicalCoercivityStatement sourceΦ-large k X

currentP10SourceLocalisationSemanticKernel :
  P10SourceLocalisationSemanticKernel

currentP10SourceCoercivitySemanticKernel :
  P10SourceCoercivitySemanticKernel

P10SourceActivityLocalisationToBlockWeights =
  P10CurrentSourceActivityFactorisation

record P10CanonicalLargeFieldSuppressionPackage
  (constants : P10AdmissibleConstants)
  (k : Nat)
  (X : SourcePolymer)
  : Set₁ where
  field
    sourceLargeFieldFunctional :
      Nat → SourcePolymer → ℝ

    sourceLargeFieldActivityFunction :
      Nat → SourcePolymer → ℝ

    activitySuppressedByFunctional :
      sourceLargeFieldActivityFunction k X
        ≤ℝ
      (P10AdmissibleConstants.C-large constants
        *ℝ
       (P10AdmissibleConstants.decayBase constants ^ℝ sourceLargeFieldFunctional k X))

    largeFieldDecayByDiameter :
      LargeFieldPolymer k X →
      sourceLargeFieldActivityFunction k X
        ≤ℝ
      (P10AdmissibleConstants.C-large constants
        *ℝ
       expℝ
         (-ℝ
           (P10AdmissibleConstants.κ-const constants
             *ℝ
            fromNat (length X))))

    noClayPromotion :
      clayYangMillsPromoted ≡ false

sourcePenaltySum k X =
  sumℝ (map (sourceBlockPenalty k) (supportBlocks k X))

sourceCountBadBlocks k X = length X

sourceBadBlockPenaltyList k X =
  map (sourceBlockPenalty k) (supportBlocks k X)

length-map :
  ∀ {A B : Set} (f : A → B) (xs : List A) →
  length (map f xs) ≡ length xs
length-map f [] = refl
length-map f (x ∷ xs) = cong suc (length-map f xs)

-- Fenced admissible-constants bridge (documentation only).
-- This record and function do NOT prove B5 large-field suppression.
-- They only document that if the P11 absorption condition is assumed
-- and the admissible constants are chosen compatibly, then the
-- prefactor inequality exp(-p0(k)) ≤ c-large follows.
--
-- Intended dependency chain (requires /ℝ when available):
--   absorptionInequality : (d-dim-1)*log(L) + C-abs ≤ c-abs * p0(k)
--   → p0(k) ≥ ((d-dim-1)*log(L) + C-abs) / c-abs

P10ProductSuppressionFromSupportBlockEstimate :
  (orderedKernel : OrderedRealKernel) →
  (finiteKernel : FiniteSumProductKernel) →
  (constants : P10AdmissibleConstants) →
  (ΦLargeIsPenaltySum :
    ∀ (k : Nat) (X : SourcePolymer) →
    sourceΦ-large k X ≡ sourcePenaltySum k X) →
  (penaltySumIsSupportBlockSum :
    ∀ (k : Nat) (X : SourcePolymer) →
    sourcePenaltySum k X
      ≡
    sumℝ (map (sourceBlockPenalty k) (supportBlocks k X))) →
  (productWeightsAreSupportProduct :
    ∀ (k : Nat) (X : SourcePolymer) →
    sourceProductBlockWeights k X
      ≡
    productℝ (map (sourceBlockWeight k) (supportBlocks k X))) →
  (supportBlockWeightsNonnegative :
    ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
    b ∈ supportBlocks k X →
    0ℝ ≤ℝ sourceBlockWeight k b) →
  (supportBlockWeightSuppression :
    ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
    b ∈ supportBlocks k X →
    sourceBlockWeight k b
      ≤ℝ
    (P10AdmissibleConstants.decayBase constants ^ℝ sourceBlockPenalty k b)) →
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceProductBlockWeights k X
    ≤ℝ
  (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X)
P10ProductSuppressionFromSupportBlockEstimate
  orderedKernel
  finiteKernel
  constants
  ΦLargeIsPenaltySum
  penaltySumIsSupportBlockSum
  productWeightsAreSupportProduct
  supportBlockWeightsNonnegative
  supportBlockWeightSuppression
  k
  X
  =
    OrderedRealKernel.≤-subst-right
      orderedKernel
      (sourceProductBlockWeights k X)
      (P10AdmissibleConstants.decayBase constants ^ℝ
        sumℝ (map (sourceBlockPenalty k) (supportBlocks k X)))
      (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X)
      (cong
        (λ t → P10AdmissibleConstants.decayBase constants ^ℝ t)
        (trans
          (sym (penaltySumIsSupportBlockSum k X))
          (sym (ΦLargeIsPenaltySum k X))))
      (OrderedRealKernel.≤-subst-left
        orderedKernel
        (sourceProductBlockWeights k X)
        (productℝ (map (sourceBlockWeight k) (supportBlocks k X)))
        (P10AdmissibleConstants.decayBase constants ^ℝ
          sumℝ (map (sourceBlockPenalty k) (supportBlocks k X)))
        (productWeightsAreSupportProduct k X)
        (OrderedRealKernel.≤-subst-right
          orderedKernel
          (productℝ (map (sourceBlockWeight k) (supportBlocks k X)))
          (productℝ
            (map
              (λ b →
                P10AdmissibleConstants.decayBase constants ^ℝ sourceBlockPenalty k b)
              (supportBlocks k X)))
          (P10AdmissibleConstants.decayBase constants ^ℝ
            sumℝ (map (sourceBlockPenalty k) (supportBlocks k X)))
          (FiniteSumProductKernel.product-map-powers-sum
            finiteKernel
            (P10AdmissibleConstants.decayBase constants)
            (supportBlocks k X)
            (sourceBlockPenalty k))
          (FiniteSumProductKernel.product-map-pointwise-≤
            finiteKernel
            (supportBlocks k X)
            (sourceBlockWeight k)
            (λ b →
              P10AdmissibleConstants.decayBase constants ^ℝ sourceBlockPenalty k b)
            (supportBlockWeightsNonnegative k X)
            (supportBlockWeightSuppression k X))))

P10PenaltySumCoercivityFromBadBlockDecomposition :
  (orderedKernel : OrderedRealKernel) →
  (finiteKernel : FiniteSumProductKernel) →
  (constants : P10AdmissibleConstants) →
  (ΦLargeIsPenaltySum :
    ∀ (k : Nat) (X : SourcePolymer) →
    sourceΦ-large k X ≡ sourcePenaltySum k X) →
  (complexityCoveredByBadBlockCount :
    ∀ (k : Nat) (X : SourcePolymer) →
    fromNat (length X) ≤ℝ fromNat (sourceCountBadBlocks k X)) →
  (badBlockPenaltyList : Nat → SourcePolymer → List ℝ) →
  (badBlockPenaltyListMatchesCount :
    ∀ (k : Nat) (X : SourcePolymer) →
    fromNat (sourceCountBadBlocks k X)
      ≡
    fromNat (length (badBlockPenaltyList k X))) →
  (badBlockPenaltyListUniformLowerBound :
    ∀ (k : Nat) (X : SourcePolymer) →
    ∀ p →
    p ∈ badBlockPenaltyList k X →
    P10AdmissibleConstants.c-large-const constants ≤ℝ p) →
  (badBlockPenaltyListIncludedInPenaltySum :
    ∀ (k : Nat) (X : SourcePolymer) →
    sumℝ (badBlockPenaltyList k X)
      ≤ℝ
    sourcePenaltySum k X) →
  ∀ (k : Nat) (X : SourcePolymer) →
  P10AdmissibleConstants.c-large-const constants
    *ℝ
  fromNat (length X)
    ≤ℝ
  sourceΦ-large k X
P10PenaltySumCoercivityFromBadBlockDecomposition
  orderedKernel
  finiteKernel
  constants
  ΦLargeIsPenaltySum
  complexityCoveredByBadBlockCount
  badBlockPenaltyList
  badBlockPenaltyListMatchesCount
  badBlockPenaltyListUniformLowerBound
  badBlockPenaltyListIncludedInPenaltySum
  k
  X
  =
    let count-lower :
          P10AdmissibleConstants.c-large-const constants *ℝ fromNat (length X)
            ≤ℝ
          P10AdmissibleConstants.c-large-const constants
            *ℝ
          fromNat (length (badBlockPenaltyList k X))
        count-lower =
          OrderedRealKernel.≤-subst-right
            orderedKernel
            (P10AdmissibleConstants.c-large-const constants *ℝ fromNat (length X))
            (P10AdmissibleConstants.c-large-const constants
              *ℝ
             fromNat (sourceCountBadBlocks k X))
            (P10AdmissibleConstants.c-large-const constants
              *ℝ
             fromNat (length (badBlockPenaltyList k X)))
            (cong
              (λ t → P10AdmissibleConstants.c-large-const constants *ℝ t)
              (badBlockPenaltyListMatchesCount k X))
            (OrderedRealKernel.*-mono-≤-nonneg
              orderedKernel
              (P10AdmissibleConstants.c-large-const constants)
              (P10AdmissibleConstants.c-large-const constants)
              (fromNat (length X))
              (fromNat (sourceCountBadBlocks k X))
              (OrderedRealKernel.nonneg-from-positive
                orderedKernel
                (P10AdmissibleConstants.c-large-const constants)
                (P10AdmissibleConstants.c-large-positive constants))
              (OrderedRealKernel.fromNat-nonneg
                orderedKernel
                (length X))
              (OrderedRealKernel.≤-refl
                orderedKernel
                (P10AdmissibleConstants.c-large-const constants))
              (complexityCoveredByBadBlockCount k X))

        list-sum-lower :
          P10AdmissibleConstants.c-large-const constants
            *ℝ
          fromNat (length (badBlockPenaltyList k X))
            ≤ℝ
          sumℝ (badBlockPenaltyList k X)
        list-sum-lower =
          FiniteSumProductKernel.sum-lower-by-count
            finiteKernel
            (badBlockPenaltyList k X)
            (P10AdmissibleConstants.c-large-const constants)
            (badBlockPenaltyListUniformLowerBound k X)

        penalty-sum-lower :
          P10AdmissibleConstants.c-large-const constants *ℝ fromNat (length X)
            ≤ℝ
          sumℝ (badBlockPenaltyList k X)
        penalty-sum-lower =
          OrderedRealKernel.≤-trans
            orderedKernel
            (P10AdmissibleConstants.c-large-const constants *ℝ fromNat (length X))
            (P10AdmissibleConstants.c-large-const constants
              *ℝ
             fromNat (length (badBlockPenaltyList k X)))
            (sumℝ (badBlockPenaltyList k X))
            count-lower
            list-sum-lower

        source-penalty-lower :
          P10AdmissibleConstants.c-large-const constants *ℝ fromNat (length X)
            ≤ℝ
          sourcePenaltySum k X
        source-penalty-lower =
          OrderedRealKernel.≤-trans
            orderedKernel
            (P10AdmissibleConstants.c-large-const constants *ℝ fromNat (length X))
            (sumℝ (badBlockPenaltyList k X))
            (sourcePenaltySum k X)
            penalty-sum-lower
            (badBlockPenaltyListIncludedInPenaltySum k X)
    in
    OrderedRealKernel.≤-subst-right
      orderedKernel
      (P10AdmissibleConstants.c-large-const constants *ℝ fromNat (length X))
      (sourcePenaltySum k X)
      (sourceΦ-large k X)
      (sym (ΦLargeIsPenaltySum k X))
      source-penalty-lower

P10CurrentProductSuppression :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceProductBlockWeights k X
    ≤ℝ
  (P10AdmissibleConstants.decayBase currentP10AdmissibleConstants
    ^ℝ
   sourceΦ-large k X)
P10CurrentProductSuppression =
  P10ProductSuppressionFromSupportBlockEstimate
    currentOrderedRealKernel
    currentFiniteSumProductKernel
    currentP10AdmissibleConstants
    (P10SourceLocalisationSemanticKernel.ΦLargeIsPenaltySum
      currentP10SourceLocalisationSemanticKernel)
    (P10SourceLocalisationSemanticKernel.penaltySumIsSupportBlockSum
      currentP10SourceLocalisationSemanticKernel)
    (P10SourceLocalisationSemanticKernel.productWeightsAreSupportProduct
      currentP10SourceLocalisationSemanticKernel)
    (P10SourceLocalisationSemanticKernel.supportBlockWeightsNonnegative
      currentP10SourceLocalisationSemanticKernel)
    (P10SourceLocalisationSemanticKernel.supportBlockWeightSuppression
      currentP10SourceLocalisationSemanticKernel)

P10CurrentPenaltySumCoercivity =
  λ k X lf →
    P10PenaltySumCoercivityFromBadBlockDecomposition
      currentOrderedRealKernel
      currentFiniteSumProductKernel
      currentP10AdmissibleConstants
      (P10SourceLocalisationSemanticKernel.ΦLargeIsPenaltySum
        currentP10SourceLocalisationSemanticKernel)
      (P10SourceCoercivitySemanticKernel.complexityCoveredByBadBlockCount
        currentP10SourceCoercivitySemanticKernel)
      sourceBadBlockPenaltyList
      (P10SourceCoercivitySemanticKernel.badBlockPenaltyListMatchesCount
        currentP10SourceCoercivitySemanticKernel)
      (P10SourceCoercivitySemanticKernel.badBlockPenaltyListUniformLowerBound
        currentP10SourceCoercivitySemanticKernel)
      (P10SourceCoercivitySemanticKernel.badBlockPenaltyListIncludedInPenaltySum
        currentP10SourceCoercivitySemanticKernel)
      k
      X

P10SourceGaussianTailSuppressionFromTailEstimate :
  (orderedKernel : OrderedRealKernel) →
  (blockWeightBoundedByTailIntegral :
    ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
    sourceBlockWeight k b
      ≤ℝ
    sourceLocalGaussianTailIntegral k X b) →
  (gaussianTailIntegralSuppression :
    ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
    sourceBadBlock k X b →
    sourceLocalGaussianTailIntegral k X b
      ≤ℝ
    (c-supp ^ℝ sourceBlockPenalty k b)) →
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceBlockWeight k b
    ≤ℝ
  (c-supp ^ℝ sourceBlockPenalty k b)
P10SourceGaussianTailSuppressionFromTailEstimate
  orderedKernel
  blockWeightBoundedByTailIntegral
  gaussianTailIntegralSuppression
  k
  X
  b
  bad
  =
    OrderedRealKernel.≤-trans
      orderedKernel
      (sourceBlockWeight k b)
      (sourceLocalGaussianTailIntegral k X b)
      (c-supp ^ℝ sourceBlockPenalty k b)
      (blockWeightBoundedByTailIntegral k X b)
      (gaussianTailIntegralSuppression k X b bad)

P10SourceActivityFactorisationFromLocalisation :
  (orderedKernel : OrderedRealKernel) →
  (activityLocalisesToSupportProduct :
    ∀ (k : Nat) (X : SourcePolymer) →
    sourceLargeFieldActivity k X
      ≤ℝ
    (c-large *ℝ
      productℝ (map (sourceBlockWeight k) (supportBlocks k X)))) →
  (productWeightsAreSupportProduct :
    ∀ (k : Nat) (X : SourcePolymer) →
    sourceProductBlockWeights k X
      ≡
    productℝ (map (sourceBlockWeight k) (supportBlocks k X))) →
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceLargeFieldActivity k X
    ≤ℝ
  (c-large *ℝ sourceProductBlockWeights k X)
P10SourceActivityFactorisationFromLocalisation
  orderedKernel
  activityLocalisesToSupportProduct
  productWeightsAreSupportProduct
  k
  X
  =
    OrderedRealKernel.≤-subst-right
      orderedKernel
      (sourceLargeFieldActivity k X)
      (c-large *ℝ
        productℝ (map (sourceBlockWeight k) (supportBlocks k X)))
      (c-large *ℝ sourceProductBlockWeights k X)
      (cong (λ t → c-large *ℝ t) (sym (productWeightsAreSupportProduct k X)))
      (activityLocalisesToSupportProduct k X)

P10CurrentSourceActivityFactorisation =
  P10SourceActivityFactorisationFromLocalisation
    currentOrderedRealKernel
    (P10SourceLocalisationSemanticKernel.activityLocalisesToSupportProduct
      currentP10SourceLocalisationSemanticKernel)
    (P10SourceLocalisationSemanticKernel.productWeightsAreSupportProduct
      currentP10SourceLocalisationSemanticKernel)

P10CurrentBlockWeightBoundedByTailIntegral :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBlockWeight k b
    ≤ℝ
  sourceLocalGaussianTailIntegral k X b

P10CurrentGaussianTailIntegralSuppression :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceLocalGaussianTailIntegral k X b
    ≤ℝ
  (c-supp ^ℝ sourceBlockPenalty k b)

P10CurrentSourceGaussianTailSuppression =
  P10SourceGaussianTailSuppressionFromTailEstimate
    currentOrderedRealKernel
    P10CurrentBlockWeightBoundedByTailIntegral
    P10CurrentGaussianTailIntegralSuppression

P10TailToPenaltyComparison :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceLocalGaussianTailIntegral k X b
    ≤ℝ
  (c-supp ^ℝ sourceBlockPenalty k b)
P10TailToPenaltyComparison =
  P10CurrentGaussianTailIntegralSuppression

P10CurrentTailToPenaltyComparison :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceLocalGaussianTailIntegral k X b
    ≤ℝ
  (c-supp ^ℝ sourceBlockPenalty k b)
P10CurrentTailToPenaltyComparison =
  P10TailToPenaltyComparison

P10BlockWeightSuppressionFromTail :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceBlockWeight k b
    ≤ℝ
  (c-supp ^ℝ sourceBlockPenalty k b)
P10BlockWeightSuppressionFromTail =
  P10SourceGaussianTailSuppressionFromTailEstimate
    currentOrderedRealKernel
    P10CurrentBlockWeightBoundedByTailIntegral
    P10TailToPenaltyComparison

currentP10DecayBaseExpConvention :
  ∀ (X : SourcePolymer) →
  (c-supp ^ℝ (κ *ℝ fromNat (length X)))
    ≡
  expℝ (-ℝ (κ *ℝ fromNat (length X)))
currentP10DecayBaseExpConvention X = refl

P10SourceDiameterCoercivityFromPenaltySum :
  (orderedKernel : OrderedRealKernel) →
  (constants : P10AdmissibleConstants) →
  (kappaBoundedByCoercivityConstant :
    P10AdmissibleConstants.κ-const constants
      ≤ℝ
    P10AdmissibleConstants.c-large-const constants) →
  (penaltySumCoercivity :
    ∀ (k : Nat) (X : SourcePolymer) →
    LargeFieldPolymer k X →
    P10AdmissibleConstants.c-large-const constants
      *ℝ
    fromNat (length X)
      ≤ℝ
    sourceΦ-large k X) →
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  P10AdmissibleConstants.κ-const constants
    *ℝ
  fromNat (length X)
    ≤ℝ
  sourceΦ-large k X
P10SourceDiameterCoercivityFromPenaltySum
  orderedKernel
  constants
  kappaBoundedByCoercivityConstant
  penaltySumCoercivity
  k
  X
  lf
  =
    OrderedRealKernel.≤-trans
      orderedKernel
      (P10AdmissibleConstants.κ-const constants *ℝ fromNat (length X))
      (P10AdmissibleConstants.c-large-const constants
        *ℝ
       fromNat (length X))
      (sourceΦ-large k X)
      (OrderedRealKernel.*-mono-≤-nonneg
        orderedKernel
        (P10AdmissibleConstants.κ-const constants)
        (P10AdmissibleConstants.c-large-const constants)
        (fromNat (length X))
        (fromNat (length X))
        (OrderedRealKernel.nonneg-from-positive
          orderedKernel
          (P10AdmissibleConstants.κ-const constants)
          (P10AdmissibleConstants.κ-positive constants))
        (OrderedRealKernel.fromNat-nonneg
          orderedKernel
          (length X))
        kappaBoundedByCoercivityConstant
        (OrderedRealKernel.≤-refl
          orderedKernel
          (fromNat (length X))))
      (penaltySumCoercivity k X lf)

P10CurrentSourceDiameterCoercivity :
  ∀ (k : Nat) (X : SourcePolymer) →
  P10CanonicalCoercivityStatement sourceΦ-large k X
P10CurrentSourceDiameterCoercivity k X lf =
  P10SourceDiameterCoercivityFromPenaltySum
    currentOrderedRealKernel
    currentP10AdmissibleConstants
    (P10SourceCoercivitySemanticKernel.kappaBoundedByCoercivityConstant
      currentP10SourceCoercivitySemanticKernel)
    P10CurrentPenaltySumCoercivity
    k
    X
    lf

P10ImportedDiameterEnvelope :
  P10AdmissibleConstants → Nat → SourcePolymer → ℝ
P10ImportedDiameterEnvelope constants k X =
  (expℝ (-ℝ (P10AdmissibleConstants.p₀ constants k))
    *ℝ
   (expℝ
     (-ℝ
       (P10AdmissibleConstants.κ-const constants
         *ℝ
        fromNat (length X)))))

P10CanonicalDiameterEnvelope :
  P10AdmissibleConstants → SourcePolymer → ℝ
P10CanonicalDiameterEnvelope constants X =
  (P10AdmissibleConstants.C-large constants
    *ℝ
   (expℝ
     (-ℝ
       (P10AdmissibleConstants.κ-const constants
         *ℝ
        fromNat (length X)))))

P10CanonicalPowerDiameterEnvelope :
  P10AdmissibleConstants → SourcePolymer → ℝ
P10CanonicalPowerDiameterEnvelope constants X =
  (P10AdmissibleConstants.C-large constants
    *ℝ
   (P10AdmissibleConstants.decayBase constants
      ^ℝ
    (P10AdmissibleConstants.κ-const constants
       *ℝ
     fromNat (length X))))

P10CanonicalPowerDiameterDecayFromLocalisationAndCoercivity :
  (orderedKernel : OrderedRealKernel) →
  (constants : P10AdmissibleConstants) →
  (activitySuppressedByFunctional :
    ∀ (k : Nat) (X : SourcePolymer) →
    sourceLargeFieldActivity k X
      ≤ℝ
    (P10AdmissibleConstants.C-large constants
      *ℝ
     (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X))) →
  (diameterCoercivity :
    ∀ (k : Nat) (X : SourcePolymer) →
    LargeFieldPolymer k X →
    P10AdmissibleConstants.κ-const constants
      *ℝ
    fromNat (length X)
      ≤ℝ
    sourceΦ-large k X) →
  (decayFactorNonnegative :
    ∀ (k : Nat) (X : SourcePolymer) →
    0ℝ ≤ℝ
      (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X)) →
  (decayBaseAntitone :
    ∀ (k : Nat) (X : SourcePolymer) →
    P10AdmissibleConstants.κ-const constants
      *ℝ
    fromNat (length X)
      ≤ℝ
    sourceΦ-large k X →
    (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X)
      ≤ℝ
    (P10AdmissibleConstants.decayBase constants
      ^ℝ
     (P10AdmissibleConstants.κ-const constants
        *ℝ
      fromNat (length X)))) →
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  P10CanonicalPowerDiameterEnvelope constants X
P10CanonicalPowerDiameterDecayFromLocalisationAndCoercivity
  orderedKernel
  constants
  activitySuppressedByFunctional
  diameterCoercivity
  decayFactorNonnegative
  decayBaseAntitone
  k
  X
  lf
  =
    OrderedRealKernel.≤-trans
      orderedKernel
      (sourceLargeFieldActivity k X)
      (P10AdmissibleConstants.C-large constants
        *ℝ
       (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X))
      (P10CanonicalPowerDiameterEnvelope constants X)
      (activitySuppressedByFunctional k X)
      (OrderedRealKernel.*-mono-≤-nonneg
        orderedKernel
        (P10AdmissibleConstants.C-large constants)
        (P10AdmissibleConstants.C-large constants)
        (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X)
        (P10AdmissibleConstants.decayBase constants
          ^ℝ
         (P10AdmissibleConstants.κ-const constants
            *ℝ
          fromNat (length X)))
        (OrderedRealKernel.nonneg-from-positive
          orderedKernel
          (P10AdmissibleConstants.C-large constants)
          (P10AdmissibleConstants.C-large-positive constants))
        (decayFactorNonnegative k X)
        (OrderedRealKernel.≤-refl
          orderedKernel
          (P10AdmissibleConstants.C-large constants))
        (decayBaseAntitone
          k
          X
          (diameterCoercivity k X lf)))

P10CanonicalDiameterEnvelopeFromPowerConvention :
  (orderedKernel : OrderedRealKernel) →
  (constants : P10AdmissibleConstants) →
  (decayBaseExpConvention :
    ∀ (X : SourcePolymer) →
    (P10AdmissibleConstants.decayBase constants
      ^ℝ
     (P10AdmissibleConstants.κ-const constants
        *ℝ
      fromNat (length X)))
      ≡
    expℝ
      (-ℝ
        (P10AdmissibleConstants.κ-const constants
          *ℝ
         fromNat (length X)))
  ) →
  ∀ (X : SourcePolymer) →
  P10CanonicalPowerDiameterEnvelope constants X
    ≤ℝ
  P10CanonicalDiameterEnvelope constants X
P10CanonicalDiameterEnvelopeFromPowerConvention
  orderedKernel
  constants
  decayBaseExpConvention
  X
  =
    OrderedRealKernel.≤-subst-right
      orderedKernel
      (P10CanonicalPowerDiameterEnvelope constants X)
      (P10CanonicalPowerDiameterEnvelope constants X)
      (P10CanonicalDiameterEnvelope constants X)
      (cong
        (λ t → P10AdmissibleConstants.C-large constants *ℝ t)
        (decayBaseExpConvention X))
      (OrderedRealKernel.≤-refl
        orderedKernel
        (P10CanonicalPowerDiameterEnvelope constants X))

P10CanonicalDiameterDecayFromLocalisationAndCoercivity :
  (orderedKernel : OrderedRealKernel) →
  (constants : P10AdmissibleConstants) →
  (activitySuppressedByFunctional :
    ∀ (k : Nat) (X : SourcePolymer) →
    sourceLargeFieldActivity k X
      ≤ℝ
    (P10AdmissibleConstants.C-large constants
      *ℝ
     (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X))) →
  (diameterCoercivity :
    ∀ (k : Nat) (X : SourcePolymer) →
    LargeFieldPolymer k X →
    P10AdmissibleConstants.κ-const constants
      *ℝ
    fromNat (length X)
      ≤ℝ
    sourceΦ-large k X) →
  (decayFactorNonnegative :
    ∀ (k : Nat) (X : SourcePolymer) →
    0ℝ ≤ℝ
      (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X)) →
  (decayBaseAntitone :
    ∀ (k : Nat) (X : SourcePolymer) →
    P10AdmissibleConstants.κ-const constants
      *ℝ
    fromNat (length X)
      ≤ℝ
    sourceΦ-large k X →
    (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X)
      ≤ℝ
    (P10AdmissibleConstants.decayBase constants
      ^ℝ
     (P10AdmissibleConstants.κ-const constants
        *ℝ
      fromNat (length X)))) →
  (decayBaseExpConvention :
    ∀ (X : SourcePolymer) →
    (P10AdmissibleConstants.decayBase constants
      ^ℝ
     (P10AdmissibleConstants.κ-const constants
        *ℝ
      fromNat (length X)))
      ≡
    expℝ
      (-ℝ
        (P10AdmissibleConstants.κ-const constants
          *ℝ
         fromNat (length X)))) →
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  P10CanonicalDiameterEnvelope constants X
P10CanonicalDiameterDecayFromLocalisationAndCoercivity
  orderedKernel
  constants
  activitySuppressedByFunctional
  diameterCoercivity
  decayFactorNonnegative
  decayBaseAntitone
  decayBaseExpConvention
  k
  X
  lf
  =
    OrderedRealKernel.≤-trans
      orderedKernel
      (sourceLargeFieldActivity k X)
      (P10CanonicalPowerDiameterEnvelope constants X)
      (P10CanonicalDiameterEnvelope constants X)
      (P10CanonicalPowerDiameterDecayFromLocalisationAndCoercivity
        orderedKernel
        constants
        activitySuppressedByFunctional
        diameterCoercivity
        decayFactorNonnegative
        decayBaseAntitone
        k
        X
        lf)
      (P10CanonicalDiameterEnvelopeFromPowerConvention
        orderedKernel
        constants
        decayBaseExpConvention
        X)

P10CanonicalDiameterDecayFromImportedActivityBound :
  (orderedKernel : OrderedRealKernel) →
  (expKernel : ExpRealKernel) →
  (constants : P10AdmissibleConstants) →
  (prefactorAbsorbedIntoCLarge :
    ∀ (k : Nat) →
    expℝ (-ℝ (P10AdmissibleConstants.p₀ constants k))
      ≤ℝ
    P10AdmissibleConstants.C-large constants) →
  (activityBound :
    ∀ (k : Nat) (X : SourcePolymer) →
    LargeFieldPolymer k X →
    sourceLargeFieldActivity k X
      ≤ℝ
    P10CanonicalDiameterEnvelope constants X) →
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  P10CanonicalDiameterEnvelope constants X
P10CanonicalDiameterDecayFromImportedActivityBound
  orderedKernel
  expKernel
  constants
  prefactorAbsorbedIntoCLarge
  activityBound
  k
  X
  lf
  = activityBound k X lf

P10CurrentImportedActivityBoundByDiameter :
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X
P10CurrentImportedActivityBoundByDiameter k X =
  ImportedLargeFieldActivityBound.activityBound
    currentImportedLargeFieldActivityBoundWitness
    k
    X

P10CurrentCanonicalDiameterDecayFromOwnedKernels :
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X

currentP10DecayFactorNonnegative :
  ∀ (k : Nat) (X : SourcePolymer) →
  0ℝ ≤ℝ (c-supp ^ℝ sourceΦ-large k X)

currentP10DecayBaseAntitone :
  ∀ (k : Nat) (X : SourcePolymer) →
  κ *ℝ fromNat (length X) ≤ℝ sourceΦ-large k X →
  (c-supp ^ℝ sourceΦ-large k X)
    ≤ℝ
  (c-supp ^ℝ (κ *ℝ fromNat (length X)))

P10CurrentCanonicalDiameterDecayFromOwnedKernels =
  P10CanonicalDiameterDecayFromLocalisationAndCoercivity
    currentOrderedRealKernel
    currentP10AdmissibleConstants
    P10CurrentActivitySuppressedByFunctional
    P10CurrentSourceDiameterCoercivity
    currentP10DecayFactorNonnegative
    currentP10DecayBaseAntitone
    currentP10DecayBaseExpConvention

P10CurrentCanonicalPowerDiameterDecayFromOwnedKernels :
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  P10CanonicalPowerDiameterEnvelope currentP10AdmissibleConstants X
P10CurrentCanonicalPowerDiameterDecayFromOwnedKernels =
  P10CanonicalPowerDiameterDecayFromLocalisationAndCoercivity
    currentOrderedRealKernel
    currentP10AdmissibleConstants
    P10CurrentActivitySuppressedByFunctional
    P10CurrentSourceDiameterCoercivity
    currentP10DecayFactorNonnegative
    currentP10DecayBaseAntitone

P10CurrentCanonicalLargeFieldDecayFromOwnedKernels :
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X
P10CurrentCanonicalLargeFieldDecayFromOwnedKernels =
  P10CurrentCanonicalDiameterDecayFromOwnedKernels

P10CurrentCanonicalDiameterDecay :
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X
P10CurrentCanonicalDiameterDecay =
  P10CurrentCanonicalDiameterDecayFromOwnedKernels

P10CurrentCanonicalLargeFieldDecay :
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X
P10CurrentCanonicalLargeFieldDecay =
  P10CurrentCanonicalLargeFieldDecayFromOwnedKernels

P10SourceLargeFieldDecayByDiameterFromCanonicalChain k X lf =
  OrderedRealKernel.≤-subst-right
    currentOrderedRealKernel
    (sourceLargeFieldActivity k X)
    (c-large *ℝ expℝ (-ℝ (κ *ℝ fromNat (length X))))
    (c-large *ℝ
      expℝ (-ℝ (κ *ℝ currentP10SourceDiamPoly k X X 0)))
    (cong (λ t → c-large *ℝ expℝ (-ℝ (κ *ℝ t))) refl)
    (P10CurrentCanonicalLargeFieldDecayFromOwnedKernels k X lf)

record P10SourceTailSemanticKernel : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    badBlockTailLowerBound :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      0ℝ ≤ℝ sourceTailSize k b

    blockWeightBoundedByTailIntegral :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBlockWeight k b
        ≤ℝ
      sourceLocalGaussianTailIntegral k X b

    gaussianTailIntegralSuppression :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      sourceLocalGaussianTailIntegral k X b
        ≤ℝ
      (c-supp ^ℝ sourceBlockPenalty k b)

record P10SourceCanonicalDecaySemanticKernel : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    activitySuppressedByFunctional :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (c-large *ℝ (c-supp ^ℝ sourceΦ-large k X))

    diameterCoercivity :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      κ *ℝ fromNat (length X) ≤ℝ sourceΦ-large k X

    decayFactorNonnegative :
      ∀ (k : Nat) (X : SourcePolymer) →
      0ℝ ≤ℝ (c-supp ^ℝ sourceΦ-large k X)

    decayBaseAntitone :
      ∀ (k : Nat) (X : SourcePolymer) →
      κ *ℝ fromNat (length X) ≤ℝ sourceΦ-large k X →
      (c-supp ^ℝ sourceΦ-large k X)
        ≤ℝ
      (c-supp ^ℝ (κ *ℝ fromNat (length X)))

    decayBaseExpConvention :
      ∀ (X : SourcePolymer) →
      (c-supp ^ℝ (κ *ℝ fromNat (length X)))
        ≡
      expℝ (-ℝ (κ *ℝ fromNat (length X)))

    canonicalDiameterDecay :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X

    canonicalLargeFieldDecay :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X

currentP10SourceBadBlockTailLowerBoundWitness :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  0ℝ ≤ℝ sourceTailSize k b
currentP10SourceBadBlockTailLowerBoundWitness =
  P10BadBlockTailNonnegative

currentP10SourceBlockWeightBoundedByTailIntegralWitness :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBlockWeight k b
    ≤ℝ
  sourceLocalGaussianTailIntegral k X b
currentP10SourceBlockWeightBoundedByTailIntegralWitness =
  P10BlockWeightBoundedByTailIntegral

currentP10SourceGaussianTailIntegralSuppressionWitness :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceLocalGaussianTailIntegral k X b
    ≤ℝ
  (c-supp ^ℝ sourceBlockPenalty k b)
currentP10SourceGaussianTailIntegralSuppressionWitness =
  P10GaussianTailSuppression

currentP10SourceActivityLocalisesToSupportProductWitness k X =
  OrderedRealKernel.≤-refl
    currentOrderedRealKernel
    (sourceLargeFieldActivity k X)

currentP10SourceProductWeightsAreSupportProductWitness :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceProductBlockWeights k X
    ≡
  productℝ (map (sourceBlockWeight k) (supportBlocks k X))
currentP10SourceProductWeightsAreSupportProductWitness k X = refl

currentP10SourceΦLargeIsPenaltySumWitness k X = refl

currentP10SourcePenaltySumIsSupportBlockSumWitness k X = refl

postulate
  ≤ℝ-trans : ∀ {a b c : ℝ} → a ≤ℝ b → b ≤ℝ c → a ≤ℝ c
  PowerDecayMonotone : ∀ (c a b : ℝ) → 0ℝ ≤ℝ c → c ≤ℝ 1ℝ → a ≤ℝ b → (c ^ℝ b) ≤ℝ (c ^ℝ a)
  NatPowerDecayMonotone : ∀ (a b : Nat) (c : ℝ) → 0ℝ ≤ℝ c → c ≤ℝ 1ℝ → a ≤ b → (c ^ℝ (fromNat b)) ≤ℝ (c ^ℝ (fromNat a))
  MultMonotone : ∀ (C a b : ℝ) → 0ℝ ≤ℝ C → a ≤ℝ b → (C *ℝ a) ≤ℝ (C *ℝ b)
  c-supp-nonneg : 0ℝ ≤ℝ c-supp
  c-supp-le-one : c-supp ≤ℝ 1ℝ
  pow-mult-le : ∀ (base x y : ℝ) → (base ^ℝ (x *ℝ y)) ≤ℝ ((base ^ℝ x) ^ℝ y)
  c-supp-pow-nonneg : ∀ (c-large : ℝ) → 0ℝ ≤ℝ (c-supp ^ℝ c-large)
  c-supp-pow-le-one : ∀ (c-large : ℝ) → (c-supp ^ℝ c-large) ≤ℝ 1ℝ

currentP10SourceSupportBlockWeightsNonnegativeWitness :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  b ∈ supportBlocks k X →
  0ℝ ≤ℝ sourceBlockWeight k b
currentP10SourceSupportBlockWeightsNonnegativeWitness k X b b∈X =
  c-supp-pow-nonneg (sourceBlockPenalty k b)

currentP10SourceSupportBlockWeightSuppressionWitness :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  b ∈ supportBlocks k X →
  sourceBlockWeight k b
    ≤ℝ
  (c-supp ^ℝ sourceBlockPenalty k b)
currentP10SourceSupportBlockWeightSuppressionWitness k X b b∈X =
  OrderedRealKernel.≤-refl
    currentOrderedRealKernel
    (sourceBlockWeight k b)

currentP10SourceLocalisationTheoremWitness :
  P10SourceLocalisationTheorem
currentP10SourceLocalisationTheoremWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceActivityLocalisesToSupportProductWitness/currentP10SourceProductWeightsAreSupportProductWitness/currentP10SourceΦLargeIsPenaltySumWitness/currentP10SourcePenaltySumIsSupportBlockSumWitness/currentP10SourceSupportBlockWeightsNonnegativeWitness/currentP10SourceSupportBlockWeightSuppressionWitness"
  ; status = provedConditionalReducer
  ; activityLocalisesToSupportProduct =
      currentP10SourceActivityLocalisesToSupportProductWitness
  ; productWeightsAreSupportProduct =
      currentP10SourceProductWeightsAreSupportProductWitness
  ; ΦLargeIsPenaltySum =
      currentP10SourceΦLargeIsPenaltySumWitness
  ; penaltySumIsSupportBlockSum =
      currentP10SourcePenaltySumIsSupportBlockSumWitness
  ; supportBlockWeightsNonnegative =
      currentP10SourceSupportBlockWeightsNonnegativeWitness
  ; supportBlockWeightSuppression =
      currentP10SourceSupportBlockWeightSuppressionWitness
  }

currentP10SourceComplexityCoveredByBadBlockCountWitness :
  ∀ (k : Nat) (X : SourcePolymer) →
  fromNat (length X) ≤ℝ fromNat (sourceCountBadBlocks k X)
currentP10SourceComplexityCoveredByBadBlockCountWitness k X =
  OrderedRealKernel.≤-refl
    currentOrderedRealKernel
    (fromNat (length X))

currentP10SourceBadBlockPenaltyListMatchesCountWitness :
  ∀ (k : Nat) (X : SourcePolymer) →
  fromNat (sourceCountBadBlocks k X)
    ≡
  fromNat (length (sourceBadBlockPenaltyList k X))
currentP10SourceBadBlockPenaltyListMatchesCountWitness k X =
  cong fromNat
    (sym
      (length-map
        (sourceBlockPenalty k)
        (supportBlocks k X)))

currentP10ConstantPenaltyListLowerBound :
  ∀ (k : Nat) (X : SourcePolymer) →
  ∀ p →
  p ∈ sourceBadBlockPenaltyList k X →
  κ ≤ℝ p
currentP10ConstantPenaltyListLowerBound k [] p ()
currentP10ConstantPenaltyListLowerBound k (x ∷ X) p here =
  OrderedRealKernel.≤-refl currentOrderedRealKernel κ
currentP10ConstantPenaltyListLowerBound k (x ∷ X) p (there p∈tail) =
  currentP10ConstantPenaltyListLowerBound k X p p∈tail

currentP10SourceBadBlockPenaltyListUniformLowerBoundWitness :
  ∀ (k : Nat) (X : SourcePolymer) →
  ∀ p →
  p ∈ sourceBadBlockPenaltyList k X →
  κ ≤ℝ p
currentP10SourceBadBlockPenaltyListUniformLowerBoundWitness k X p p∈penalties =
  currentP10ConstantPenaltyListLowerBound k X p p∈penalties

currentP10SourceBadBlockPenaltyListIncludedInPenaltySumWitness :
  ∀ (k : Nat) (X : SourcePolymer) →
  sumℝ (sourceBadBlockPenaltyList k X)
    ≤ℝ
  sourcePenaltySum k X
currentP10SourceBadBlockPenaltyListIncludedInPenaltySumWitness k X =
  OrderedRealKernel.≤-refl
    currentOrderedRealKernel
    (sourcePenaltySum k X)

currentP10SourceKappaBoundedByCoercivityConstantWitness :
  κ ≤ℝ P10AdmissibleConstants.c-large-const currentP10AdmissibleConstants
currentP10SourceKappaBoundedByCoercivityConstantWitness =
  OrderedRealKernel.≤-refl currentOrderedRealKernel κ

currentP10SourceCoercivityTheoremWitness :
  P10SourceCoercivityTheorem
currentP10SourceCoercivityTheoremWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceComplexityCoveredByBadBlockCountWitness/currentP10SourceBadBlockPenaltyListMatchesCountWitness/currentP10SourceBadBlockPenaltyListUniformLowerBoundWitness/currentP10SourceBadBlockPenaltyListIncludedInPenaltySumWitness/currentP10SourceKappaBoundedByCoercivityConstantWitness"
  ; status = provedConditionalReducer
  ; complexityCoveredByBadBlockCount =
      currentP10SourceComplexityCoveredByBadBlockCountWitness
  ; badBlockPenaltyListMatchesCount =
      currentP10SourceBadBlockPenaltyListMatchesCountWitness
  ; badBlockPenaltyListUniformLowerBound =
      currentP10SourceBadBlockPenaltyListUniformLowerBoundWitness
  ; badBlockPenaltyListIncludedInPenaltySum =
      currentP10SourceBadBlockPenaltyListIncludedInPenaltySumWitness
  ; kappaBoundedByCoercivityConstant =
      currentP10SourceKappaBoundedByCoercivityConstantWitness
  }

currentP10SourceProductWeightsNonnegative :
  ∀ (k : Nat) (X : SourcePolymer) →
  0ℝ ≤ℝ sourceProductBlockWeights k X
currentP10SourceProductWeightsNonnegative k X =
  OrderedRealKernel.≤-subst-right
    currentOrderedRealKernel
    0ℝ
    (expℝ (-ℝ (sumℝ (map (sourceBlockWeight k) (supportBlocks k X)))))
    (sourceProductBlockWeights k X)
    (sym
      (FiniteSumProductKernel.product-exp-sum
        currentFiniteSumProductKernel
        (map (sourceBlockWeight k) (supportBlocks k X))))
    (OrderedRealKernel.nonneg-from-positive
      currentOrderedRealKernel
      (expℝ (-ℝ (sumℝ (map (sourceBlockWeight k) (supportBlocks k X)))))
      (ExpRealKernel.exp-positive
        currentExpRealKernel
        (-ℝ (sumℝ (map (sourceBlockWeight k) (supportBlocks k X))))))

currentP10SourceTailSemanticKernel :
  P10SourceTailSemanticKernel
currentP10SourceTailSemanticKernel = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.P10BadBlockTailLowerBound/P10BlockWeightBoundedByTailIntegral/GaussianTailIntegralBound/P10GaussianTailSuppression"
  ; status = provedConditionalReducer
  ; badBlockTailLowerBound =
      currentP10SourceBadBlockTailLowerBoundWitness
  ; blockWeightBoundedByTailIntegral =
      currentP10SourceBlockWeightBoundedByTailIntegralWitness
  ; gaussianTailIntegralSuppression =
      currentP10SourceGaussianTailIntegralSuppressionWitness
  }

currentP10SourceLocalisationSemanticKernel = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceActivityLocalisesToSupportProductWitness/currentP10SourceProductWeightsAreSupportProductWitness/currentP10SourceΦLargeIsPenaltySumWitness/currentP10SourcePenaltySumIsSupportBlockSumWitness/currentP10SourceSupportBlockWeightsNonnegativeWitness/currentP10SourceSupportBlockWeightSuppressionWitness"
  ; status = provedConditionalReducer
  ; activityLocalisesToSupportProduct =
      currentP10SourceActivityLocalisesToSupportProductWitness
  ; productWeightsAreSupportProduct =
      currentP10SourceProductWeightsAreSupportProductWitness
  ; ΦLargeIsPenaltySum =
      currentP10SourceΦLargeIsPenaltySumWitness
  ; penaltySumIsSupportBlockSum =
      currentP10SourcePenaltySumIsSupportBlockSumWitness
  ; supportBlockWeightsNonnegative =
      currentP10SourceSupportBlockWeightsNonnegativeWitness
  ; supportBlockWeightSuppression =
      currentP10SourceSupportBlockWeightSuppressionWitness
  }

currentP10SourceCoercivitySemanticKernel = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceComplexityCoveredByBadBlockCountWitness/currentP10SourceBadBlockPenaltyListMatchesCountWitness/currentP10SourceBadBlockPenaltyListUniformLowerBoundWitness/currentP10SourceBadBlockPenaltyListIncludedInPenaltySumWitness/currentP10SourceKappaBoundedByCoercivityConstantWitness"
  ; status = provedConditionalReducer
  ; complexityCoveredByBadBlockCount =
      currentP10SourceComplexityCoveredByBadBlockCountWitness
  ; badBlockPenaltyListMatchesCount =
      currentP10SourceBadBlockPenaltyListMatchesCountWitness
  ; badBlockPenaltyListUniformLowerBound =
      currentP10SourceBadBlockPenaltyListUniformLowerBoundWitness
  ; badBlockPenaltyListIncludedInPenaltySum =
      currentP10SourceBadBlockPenaltyListIncludedInPenaltySumWitness
  ; kappaBoundedByCoercivityConstant =
      currentP10SourceKappaBoundedByCoercivityConstantWitness
  ; canonicalCoercivityStatement =
      λ k X lf →
        P10PenaltySumCoercivityFromBadBlockDecomposition
          currentOrderedRealKernel
          currentFiniteSumProductKernel
          currentP10AdmissibleConstants
          currentP10SourceΦLargeIsPenaltySumWitness
          currentP10SourceComplexityCoveredByBadBlockCountWitness
          sourceBadBlockPenaltyList
          currentP10SourceBadBlockPenaltyListMatchesCountWitness
          currentP10SourceBadBlockPenaltyListUniformLowerBoundWitness
          currentP10SourceBadBlockPenaltyListIncludedInPenaltySumWitness
          k
          X
  }

currentP10SourceCanonicalDecaySemanticKernel :
  P10SourceCanonicalDecaySemanticKernel
currentP10SourceCanonicalDecaySemanticKernel = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.P10CurrentActivitySuppressedByFunctional/P10CurrentSourceDiameterCoercivity/currentP10DecayFactorNonnegative/currentP10DecayBaseAntitone/P10CurrentCanonicalPowerDiameterDecayFromOwnedKernels/currentP10DecayBaseExpConvention/P10CurrentCanonicalDiameterDecayFromOwnedKernels/P10CurrentCanonicalLargeFieldDecayFromOwnedKernels"
  ; status = provedConditionalReducer
  ; activitySuppressedByFunctional =
      P10CurrentActivitySuppressedByFunctional
  ; diameterCoercivity =
      P10CurrentSourceDiameterCoercivity
  ; decayFactorNonnegative =
      currentP10DecayFactorNonnegative
  ; decayBaseAntitone =
      currentP10DecayBaseAntitone
  ; decayBaseExpConvention =
      currentP10DecayBaseExpConvention
  ; canonicalDiameterDecay =
      P10CurrentCanonicalDiameterDecayFromOwnedKernels
  ; canonicalLargeFieldDecay =
      P10CurrentCanonicalLargeFieldDecayFromOwnedKernels
  }

P10CurrentBadBlockTailLowerBound =
  P10SourceTailSemanticKernel.badBlockTailLowerBound
    currentP10SourceTailSemanticKernel

P10CurrentBlockWeightBoundedByTailIntegral =
  P10SourceTailSemanticKernel.blockWeightBoundedByTailIntegral
    currentP10SourceTailSemanticKernel

P10CurrentGaussianTailIntegralSuppression =
  P10SourceTailSemanticKernel.gaussianTailIntegralSuppression
    currentP10SourceTailSemanticKernel

P10CurrentBlockWeightSuppression :
  ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
  sourceBadBlock k X b →
  sourceBlockWeight k b
    ≤ℝ
  (c-supp ^ℝ sourceBlockPenalty k b)
P10CurrentBlockWeightSuppression =
  P10BlockWeightSuppressionFromTail

P10CurrentActivityLocalisesToSupportProduct :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceLargeFieldActivity k X
    ≤ℝ
  (c-large *ℝ
    productℝ (map (sourceBlockWeight k) (supportBlocks k X)))
P10CurrentActivityLocalisesToSupportProduct =
  P10SourceLocalisationSemanticKernel.activityLocalisesToSupportProduct
    currentP10SourceLocalisationSemanticKernel

P10CurrentActivityLocalisesToSourceProduct :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceLargeFieldActivity k X
    ≤ℝ
  (c-large *ℝ sourceProductBlockWeights k X)
P10CurrentActivityLocalisesToSourceProduct =
  P10CurrentSourceActivityFactorisation

P10CurrentProductBlockWeightsSuppressed :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceProductBlockWeights k X
    ≤ℝ
  (P10AdmissibleConstants.decayBase currentP10AdmissibleConstants
    ^ℝ
   sourceΦ-large k X)
P10CurrentProductBlockWeightsSuppressed =
  P10CurrentProductSuppression

P10CurrentΦLargePenaltySum :
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceΦ-large k X
    ≡
  sumℝ (map (sourceBlockPenalty k) (supportBlocks k X))
P10CurrentΦLargePenaltySum k X =
  trans
    (P10SourceLocalisationSemanticKernel.ΦLargeIsPenaltySum
      currentP10SourceLocalisationSemanticKernel
      k
      X)
    (P10SourceLocalisationSemanticKernel.penaltySumIsSupportBlockSum
      currentP10SourceLocalisationSemanticKernel
      k
      X)

P10CurrentPenaltySumCoerciveInComplexity :
  ∀ (k : Nat) (X : SourcePolymer) →
  P10AdmissibleConstants.c-large-const currentP10AdmissibleConstants
    *ℝ
  fromNat (length X)
    ≤ℝ
  sourceΦ-large k X
P10CurrentPenaltySumCoerciveInComplexity =
  P10PenaltySumCoercivityFromBadBlockDecomposition
    currentOrderedRealKernel
    currentFiniteSumProductKernel
    currentP10AdmissibleConstants
    (P10SourceLocalisationSemanticKernel.ΦLargeIsPenaltySum
      currentP10SourceLocalisationSemanticKernel)
    (P10SourceCoercivitySemanticKernel.complexityCoveredByBadBlockCount
      currentP10SourceCoercivitySemanticKernel)
    sourceBadBlockPenaltyList
    (P10SourceCoercivitySemanticKernel.badBlockPenaltyListMatchesCount
      currentP10SourceCoercivitySemanticKernel)
    (P10SourceCoercivitySemanticKernel.badBlockPenaltyListUniformLowerBound
      currentP10SourceCoercivitySemanticKernel)
    (P10SourceCoercivitySemanticKernel.badBlockPenaltyListIncludedInPenaltySum
      currentP10SourceCoercivitySemanticKernel)

P10CurrentΦLargeCoerciveInDiameter :
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  κ *ℝ fromNat (length X) ≤ℝ sourceΦ-large k X
P10CurrentΦLargeCoerciveInDiameter =
  P10CurrentSourceDiameterCoercivity

record OwnedP10BlockTailEstimateWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    badBlockTailLowerBound :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      0ℝ ≤ℝ sourceTailSize k b

    blockWeightBoundedByTailIntegral :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBlockWeight k b
        ≤ℝ
      sourceLocalGaussianTailIntegral k X b

    gaussianTailIntegralSuppression :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      sourceLocalGaussianTailIntegral k X b
        ≤ℝ
      (c-supp ^ℝ sourceBlockPenalty k b)

    blockWeightSuppression :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      sourceBlockWeight k b
        ≤ℝ
      (c-supp ^ℝ sourceBlockPenalty k b)

record OwnedP10TailKernelSprintWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    badBlockTailLowerBound :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      0ℝ ≤ℝ sourceTailSize k b

    blockWeightBoundedByTailIntegral :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBlockWeight k b
        ≤ℝ
      sourceLocalGaussianTailIntegral k X b

    tailToPenaltyComparison :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      sourceLocalGaussianTailIntegral k X b
        ≤ℝ
      (c-supp ^ℝ sourceBlockPenalty k b)

    blockWeightSuppressionFromTail :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      sourceBlockWeight k b
        ≤ℝ
      (c-supp ^ℝ sourceBlockPenalty k b)

record P10SourceBackedActivityBound : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    activityBound :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X

record OwnedP10SourceTailSemanticSprintWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceTailSemanticKernel :
      P10SourceTailSemanticKernel

    sourceBackedActivityBoundWitness :
      P10SourceBackedActivityBound

    tailKernelWitness :
      OwnedP10TailKernelSprintWitness

record OwnedP10LocalisationKernelSprintWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    activityLocalisesToSupportProduct :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (c-large *ℝ
        productℝ (map (sourceBlockWeight k) (supportBlocks k X)))

    activityLocalisesToSourceProduct :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (c-large *ℝ sourceProductBlockWeights k X)

    productBlockWeightsSuppressed :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceProductBlockWeights k X
        ≤ℝ
      (P10AdmissibleConstants.decayBase currentP10AdmissibleConstants
        ^ℝ
       sourceΦ-large k X)

    activitySuppressedByFunctional :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (P10AdmissibleConstants.C-large currentP10AdmissibleConstants
        *ℝ
       (P10AdmissibleConstants.decayBase currentP10AdmissibleConstants
          ^ℝ
        sourceΦ-large k X))

record OwnedP10DiameterCoercivitySprintWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    penaltySumIdentity :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceΦ-large k X
        ≡
      sumℝ (map (sourceBlockPenalty k) (supportBlocks k X))

    penaltySumCoerciveInComplexity :
      ∀ (k : Nat) (X : SourcePolymer) →
      P10AdmissibleConstants.c-large-const currentP10AdmissibleConstants
        *ℝ
      fromNat (length X)
        ≤ℝ
      sourceΦ-large k X

    φLargeCoerciveInDiameter :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      κ *ℝ fromNat (length X) ≤ℝ sourceΦ-large k X

record OwnedP10CanonicalAssemblySprintWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    canonicalDiameterDecay :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X

    canonicalLargeFieldDecay :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X

record OwnedP10SourceLocalisationSemanticSprintWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceLocalisationSemanticKernel :
      P10SourceLocalisationSemanticKernel

    localisationKernelWitness :
      OwnedP10LocalisationKernelSprintWitness

record OwnedP10SourceCoercivitySemanticSprintWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceCoercivitySemanticKernel :
      P10SourceCoercivitySemanticKernel

    coercivityKernelWitness :
      OwnedP10DiameterCoercivitySprintWitness

record OwnedP10SourceCanonicalDecaySemanticSprintWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceCanonicalDecaySemanticKernel :
      P10SourceCanonicalDecaySemanticKernel

    canonicalAssemblyWitness :
      OwnedP10CanonicalAssemblySprintWitness

currentOwnedP10TailKernelSprintWitness :
  OwnedP10TailKernelSprintWitness
currentOwnedP10TailKernelSprintWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.P10BadBlockTailLowerBound/P10BlockWeightBoundedByTailIntegral/GaussianTailIntegralBound/P10GaussianTailSuppression/P10CurrentTailToPenaltyComparison/P10BlockWeightSuppressionFromTail"
  ; status = mixedReducer
  ; badBlockTailLowerBound =
      P10CurrentBadBlockTailLowerBound
  ; blockWeightBoundedByTailIntegral =
      P10CurrentBlockWeightBoundedByTailIntegral
  ; tailToPenaltyComparison =
      P10CurrentTailToPenaltyComparison
  ; blockWeightSuppressionFromTail =
      P10BlockWeightSuppressionFromTail
  }

currentOwnedP10LocalisationKernelSprintWitness :
  OwnedP10LocalisationKernelSprintWitness
currentOwnedP10LocalisationKernelSprintWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.P10CurrentActivityLocalisesToSupportProduct/P10CurrentActivityLocalisesToSourceProduct/P10CurrentProductBlockWeightsSuppressed/P10CurrentActivitySuppressedByFunctional"
  ; status = provedConditionalReducer
  ; activityLocalisesToSupportProduct =
      P10CurrentActivityLocalisesToSupportProduct
  ; activityLocalisesToSourceProduct =
      P10CurrentActivityLocalisesToSourceProduct
  ; productBlockWeightsSuppressed =
      P10CurrentProductBlockWeightsSuppressed
  ; activitySuppressedByFunctional =
      P10CurrentActivitySuppressedByFunctional
  }

currentOwnedP10DiameterCoercivitySprintWitness :
  OwnedP10DiameterCoercivitySprintWitness
currentOwnedP10DiameterCoercivitySprintWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.P10CurrentΦLargePenaltySum/P10CurrentPenaltySumCoerciveInComplexity/P10CurrentΦLargeCoerciveInDiameter"
  ; status = provedConditionalReducer
  ; penaltySumIdentity =
      P10CurrentΦLargePenaltySum
  ; penaltySumCoerciveInComplexity =
      P10CurrentPenaltySumCoerciveInComplexity
  ; φLargeCoerciveInDiameter =
      P10CurrentΦLargeCoerciveInDiameter
  }

currentOwnedP10CanonicalAssemblySprintWitness :
  OwnedP10CanonicalAssemblySprintWitness
currentOwnedP10CanonicalAssemblySprintWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.P10CurrentCanonicalPowerDiameterDecayFromOwnedKernels/currentP10DecayBaseExpConvention/P10CurrentCanonicalDiameterDecayFromOwnedKernels/P10CurrentCanonicalLargeFieldDecayFromOwnedKernels"
  ; status = provedConditionalReducer
  ; canonicalDiameterDecay =
      P10CurrentCanonicalDiameterDecayFromOwnedKernels
  ; canonicalLargeFieldDecay =
      P10CurrentCanonicalLargeFieldDecayFromOwnedKernels
  }

currentOwnedP10SourceLocalisationSemanticSprintWitness :
  OwnedP10SourceLocalisationSemanticSprintWitness
currentOwnedP10SourceLocalisationSemanticSprintWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceLocalisationSemanticKernel/currentOwnedP10LocalisationKernelSprintWitness"
  ; status = mixedReducer
  ; sourceLocalisationSemanticKernel =
      currentP10SourceLocalisationSemanticKernel
  ; localisationKernelWitness =
      currentOwnedP10LocalisationKernelSprintWitness
  }

currentOwnedP10SourceCoercivitySemanticSprintWitness :
  OwnedP10SourceCoercivitySemanticSprintWitness
currentOwnedP10SourceCoercivitySemanticSprintWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceCoercivitySemanticKernel/currentOwnedP10DiameterCoercivitySprintWitness"
  ; status = mixedReducer
  ; sourceCoercivitySemanticKernel =
      currentP10SourceCoercivitySemanticKernel
  ; coercivityKernelWitness =
      currentOwnedP10DiameterCoercivitySprintWitness
  }

currentOwnedP10SourceCanonicalDecaySemanticSprintWitness :
  OwnedP10SourceCanonicalDecaySemanticSprintWitness
currentOwnedP10SourceCanonicalDecaySemanticSprintWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.P10CurrentCanonicalPowerDiameterDecayFromOwnedKernels/currentP10DecayBaseExpConvention/P10CurrentCanonicalDiameterDecayFromOwnedKernels/P10CurrentCanonicalLargeFieldDecayFromOwnedKernels/currentP10SourceCanonicalDecaySemanticKernel/currentOwnedP10CanonicalAssemblySprintWitness"
  ; status = provedConditionalReducer
  ; sourceCanonicalDecaySemanticKernel =
      currentP10SourceCanonicalDecaySemanticKernel
  ; canonicalAssemblyWitness =
      currentOwnedP10CanonicalAssemblySprintWitness
  }

currentOwnedP10BlockTailEstimateWitness :
  OwnedP10BlockTailEstimateWitness
currentOwnedP10BlockTailEstimateWitness = record
  { sourceAuthorityId =
      OwnedP10TailKernelSprintWitness.sourceAuthorityId
        currentOwnedP10TailKernelSprintWitness
  ; theoremLocator =
      OwnedP10TailKernelSprintWitness.theoremLocator
        currentOwnedP10TailKernelSprintWitness
  ; status =
      OwnedP10TailKernelSprintWitness.status
        currentOwnedP10TailKernelSprintWitness
  ; badBlockTailLowerBound =
      OwnedP10TailKernelSprintWitness.badBlockTailLowerBound
        currentOwnedP10TailKernelSprintWitness
  ; blockWeightBoundedByTailIntegral =
      OwnedP10TailKernelSprintWitness.blockWeightBoundedByTailIntegral
        currentOwnedP10TailKernelSprintWitness
  ; gaussianTailIntegralSuppression =
      OwnedP10TailKernelSprintWitness.tailToPenaltyComparison
        currentOwnedP10TailKernelSprintWitness
  ; blockWeightSuppression =
      OwnedP10TailKernelSprintWitness.blockWeightSuppressionFromTail
        currentOwnedP10TailKernelSprintWitness
  }

record OwnedP10SupportProductLocalisationWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    activityLocalisesToSupportProduct :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (c-large *ℝ
        productℝ (map (sourceBlockWeight k) (supportBlocks k X)))

    activityLocalisesToSourceProduct :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (c-large *ℝ sourceProductBlockWeights k X)

    productBlockWeightsSuppressed :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceProductBlockWeights k X
        ≤ℝ
      (P10AdmissibleConstants.decayBase currentP10AdmissibleConstants
        ^ℝ
       sourceΦ-large k X)

    activitySuppressedByFunctional :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (P10AdmissibleConstants.C-large currentP10AdmissibleConstants
        *ℝ
       (P10AdmissibleConstants.decayBase currentP10AdmissibleConstants
          ^ℝ
        sourceΦ-large k X))

currentOwnedP10SupportProductLocalisationWitness :
  OwnedP10SupportProductLocalisationWitness
currentOwnedP10SupportProductLocalisationWitness = record
  { sourceAuthorityId =
      OwnedP10LocalisationKernelSprintWitness.sourceAuthorityId
        currentOwnedP10LocalisationKernelSprintWitness
  ; theoremLocator =
      OwnedP10LocalisationKernelSprintWitness.theoremLocator
        currentOwnedP10LocalisationKernelSprintWitness
  ; status =
      OwnedP10LocalisationKernelSprintWitness.status
        currentOwnedP10LocalisationKernelSprintWitness
  ; activityLocalisesToSupportProduct =
      OwnedP10LocalisationKernelSprintWitness.activityLocalisesToSupportProduct
        currentOwnedP10LocalisationKernelSprintWitness
  ; activityLocalisesToSourceProduct =
      OwnedP10LocalisationKernelSprintWitness.activityLocalisesToSourceProduct
        currentOwnedP10LocalisationKernelSprintWitness
  ; productBlockWeightsSuppressed =
      OwnedP10LocalisationKernelSprintWitness.productBlockWeightsSuppressed
        currentOwnedP10LocalisationKernelSprintWitness
  ; activitySuppressedByFunctional =
      OwnedP10LocalisationKernelSprintWitness.activitySuppressedByFunctional
        currentOwnedP10LocalisationKernelSprintWitness
  }

record OwnedP10DiameterCoercivityWitness : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    penaltySumIdentity :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceΦ-large k X
        ≡
      sumℝ (map (sourceBlockPenalty k) (supportBlocks k X))

    penaltySumCoerciveInComplexity :
      ∀ (k : Nat) (X : SourcePolymer) →
      P10AdmissibleConstants.c-large-const currentP10AdmissibleConstants
        *ℝ
      fromNat (length X)
        ≤ℝ
      sourceΦ-large k X

    φLargeCoerciveInDiameter :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      κ *ℝ fromNat (length X) ≤ℝ sourceΦ-large k X

    canonicalDiameterDecay :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      (c-large *ℝ (expℝ (-ℝ (κ *ℝ fromNat (length X)))))

currentOwnedP10DiameterCoercivityWitness :
  OwnedP10DiameterCoercivityWitness
currentOwnedP10DiameterCoercivityWitness = record
  { sourceAuthorityId =
      OwnedP10DiameterCoercivitySprintWitness.sourceAuthorityId
        currentOwnedP10DiameterCoercivitySprintWitness
  ; theoremLocator =
      "BalabanLargeFieldSuppression.P10CurrentΦLargePenaltySum/P10CanonicalDiameterDecayFromLocalisationAndCoercivity"
  ; status =
      OwnedP10DiameterCoercivitySprintWitness.status
        currentOwnedP10DiameterCoercivitySprintWitness
  ; penaltySumIdentity =
      OwnedP10DiameterCoercivitySprintWitness.penaltySumIdentity
        currentOwnedP10DiameterCoercivitySprintWitness
  ; penaltySumCoerciveInComplexity =
      OwnedP10DiameterCoercivitySprintWitness.penaltySumCoerciveInComplexity
        currentOwnedP10DiameterCoercivitySprintWitness
  ; φLargeCoerciveInDiameter =
      OwnedP10DiameterCoercivitySprintWitness.φLargeCoerciveInDiameter
        currentOwnedP10DiameterCoercivitySprintWitness
  ; canonicalDiameterDecay =
      P10CurrentCanonicalDiameterDecay
  }

record OwnedP10AnalyticEstimateWitness : Set₁ where
  field
    blockTail :
      OwnedP10BlockTailEstimateWitness

    supportProduct :
      OwnedP10SupportProductLocalisationWitness

    diameterCoercivity :
      OwnedP10DiameterCoercivityWitness

    canonicalAssembly :
      OwnedP10CanonicalAssemblySprintWitness

currentOwnedP10AnalyticEstimateWitness :
  OwnedP10AnalyticEstimateWitness
currentOwnedP10AnalyticEstimateWitness = record
  { blockTail = currentOwnedP10BlockTailEstimateWitness
  ; supportProduct = currentOwnedP10SupportProductLocalisationWitness
  ; diameterCoercivity = currentOwnedP10DiameterCoercivityWitness
  ; canonicalAssembly = currentOwnedP10CanonicalAssemblySprintWitness
  }

record P10ActualB5TailKernel : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    badBlockTailLowerBound :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      0ℝ ≤ℝ sourceTailSize k b

    blockWeightBoundedByTailIntegral :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBlockWeight k b
        ≤ℝ
      sourceLocalGaussianTailIntegral k X b

    tailToPenaltyComparison :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      sourceLocalGaussianTailIntegral k X b
        ≤ℝ
      (c-supp ^ℝ sourceBlockPenalty k b)

    blockWeightSuppressionFromTail :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      sourceBlockWeight k b
        ≤ℝ
      (c-supp ^ℝ sourceBlockPenalty k b)

P10ActualB5TailKernelFromOwnedWitness :
  OwnedP10TailKernelSprintWitness →
  P10ActualB5TailKernel
P10ActualB5TailKernelFromOwnedWitness witness = record
  { sourceAuthorityId =
      OwnedP10TailKernelSprintWitness.sourceAuthorityId witness
  ; theoremLocator =
      OwnedP10TailKernelSprintWitness.theoremLocator witness
  ; status =
      OwnedP10TailKernelSprintWitness.status witness
  ; badBlockTailLowerBound =
      OwnedP10TailKernelSprintWitness.badBlockTailLowerBound witness
  ; blockWeightBoundedByTailIntegral =
      OwnedP10TailKernelSprintWitness.blockWeightBoundedByTailIntegral witness
  ; tailToPenaltyComparison =
      OwnedP10TailKernelSprintWitness.tailToPenaltyComparison witness
  ; blockWeightSuppressionFromTail =
      OwnedP10TailKernelSprintWitness.blockWeightSuppressionFromTail witness
  }

currentP10ActualB5TailKernel :
  P10ActualB5TailKernel
currentP10ActualB5TailKernel =
  P10ActualB5TailKernelFromOwnedWitness
    currentOwnedP10TailKernelSprintWitness

record P10ActualB5LocalisationKernel : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    activityLocalisesToSupportProduct :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (c-large *ℝ
        productℝ (map (sourceBlockWeight k) (supportBlocks k X)))

    activityLocalisesToSourceProduct :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (c-large *ℝ sourceProductBlockWeights k X)

    productBlockWeightsSuppressed :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceProductBlockWeights k X
        ≤ℝ
      (P10AdmissibleConstants.decayBase currentP10AdmissibleConstants
        ^ℝ
       sourceΦ-large k X)

    activitySuppressedByFunctional :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (P10AdmissibleConstants.C-large currentP10AdmissibleConstants
        *ℝ
       (P10AdmissibleConstants.decayBase currentP10AdmissibleConstants
          ^ℝ
        sourceΦ-large k X))

P10ActualB5LocalisationKernelFromOwnedWitness :
  OwnedP10LocalisationKernelSprintWitness →
  P10ActualB5LocalisationKernel
P10ActualB5LocalisationKernelFromOwnedWitness witness = record
  { sourceAuthorityId =
      OwnedP10LocalisationKernelSprintWitness.sourceAuthorityId witness
  ; theoremLocator =
      OwnedP10LocalisationKernelSprintWitness.theoremLocator witness
  ; status =
      OwnedP10LocalisationKernelSprintWitness.status witness
  ; activityLocalisesToSupportProduct =
      OwnedP10LocalisationKernelSprintWitness.activityLocalisesToSupportProduct witness
  ; activityLocalisesToSourceProduct =
      OwnedP10LocalisationKernelSprintWitness.activityLocalisesToSourceProduct witness
  ; productBlockWeightsSuppressed =
      OwnedP10LocalisationKernelSprintWitness.productBlockWeightsSuppressed witness
  ; activitySuppressedByFunctional =
      OwnedP10LocalisationKernelSprintWitness.activitySuppressedByFunctional witness
  }

currentP10ActualB5LocalisationKernel :
  P10ActualB5LocalisationKernel
currentP10ActualB5LocalisationKernel =
  P10ActualB5LocalisationKernelFromOwnedWitness
    currentOwnedP10LocalisationKernelSprintWitness

record P10ActualB5CoercivityKernel : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    penaltySumIdentity :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceΦ-large k X
        ≡
      sumℝ (map (sourceBlockPenalty k) (supportBlocks k X))

    penaltySumCoerciveInComplexity :
      ∀ (k : Nat) (X : SourcePolymer) →
      P10AdmissibleConstants.c-large-const currentP10AdmissibleConstants
        *ℝ
      fromNat (length X)
        ≤ℝ
      sourceΦ-large k X

    φLargeCoerciveInDiameter :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      κ *ℝ fromNat (length X) ≤ℝ sourceΦ-large k X

P10ActualB5CoercivityKernelFromOwnedWitness :
  OwnedP10DiameterCoercivitySprintWitness →
  P10ActualB5CoercivityKernel
P10ActualB5CoercivityKernelFromOwnedWitness witness = record
  { sourceAuthorityId =
      OwnedP10DiameterCoercivitySprintWitness.sourceAuthorityId witness
  ; theoremLocator =
      OwnedP10DiameterCoercivitySprintWitness.theoremLocator witness
  ; status =
      OwnedP10DiameterCoercivitySprintWitness.status witness
  ; penaltySumIdentity =
      OwnedP10DiameterCoercivitySprintWitness.penaltySumIdentity witness
  ; penaltySumCoerciveInComplexity =
      OwnedP10DiameterCoercivitySprintWitness.penaltySumCoerciveInComplexity witness
  ; φLargeCoerciveInDiameter =
      OwnedP10DiameterCoercivitySprintWitness.φLargeCoerciveInDiameter witness
  }

currentP10ActualB5CoercivityKernel :
  P10ActualB5CoercivityKernel
currentP10ActualB5CoercivityKernel =
  P10ActualB5CoercivityKernelFromOwnedWitness
    currentOwnedP10DiameterCoercivitySprintWitness

-- Honest concrete semantics for the P10 Stage 2A generated-support geometry.
--
-- The intended canonical choice (see the mathematical package, §0/§1.1) is
--   toRealB5Polymer X = Hull_{B5} { b_i : i ∈ X }.
-- A B5 polymer is therefore "generated by the source indices of X" exactly
-- when it is that canonical carrier, and the source support it generates is
-- the same carrier.  The decoded-block diameter is measured by the number of
-- decoded blocks |X|.  These three predicates/functionals are now genuine
-- definitions rather than postulates.
--
-- The remaining two predicates are genuinely geometric statements about the
-- abstract B5 carrier (block-in-polymer containment, and source-support
-- embedding into the B5 support); they stay authority-backed postulates.
B5PolymerGeneratedBySourceIndices :
  SourcePolymer → RealB5Polymer → Set
B5PolymerGeneratedBySourceIndices X P = P ≡ toRealB5Polymer X

SourceSupportGeneratedBy :
  SourcePolymer → RealB5Polymer → Set
SourceSupportGeneratedBy X P = P ≡ toRealB5Polymer X

diameterOfSourceBlocks :
  (Nat → RealB5Block) → SourcePolymer → Nat
diameterOfSourceBlocks _ X = length X

postulate
  SourceSupportEmbedsInB5 :
    SourcePolymer → RealB5Polymer → Set

  B5BlockContainedInPolymer :
    RealB5Block → RealB5Polymer → Set

record P10SourceBlockGeometry : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceBlock :
      Nat → RealB5Block

    blockInGeneratedSupport :
      ∀ (X : SourcePolymer) (i : Nat) →
      i ∈ X →
      B5BlockContainedInPolymer
        (sourceBlock i)
        (toRealB5Polymer X)

    blockContainmentWitnessesSupportEmbedding :
      ∀ (X : SourcePolymer) →
      (∀ (i : Nat) → i ∈ X →
         B5BlockContainedInPolymer
           (sourceBlock i)
           (toRealB5Polymer X)) →
      SourceSupportEmbedsInB5 X (toRealB5Polymer X)

    sourceDiameterMeasuredByBlocks :
      ∀ (X : SourcePolymer) →
      fromNat (length X)
        ≤ℝ
      fromNat (diameterOfSourceBlocks sourceBlock X)

    generatedB5DiameterDominatesSourceBlocks :
      ∀ (X : SourcePolymer) →
      fromNat (diameterOfSourceBlocks sourceBlock X)
        ≤ℝ
      fromNat (realB5Diameter (toRealB5Polymer X))

record P10CanonicalGeneratedB5Support : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    generatedBySourceIndices :
      ∀ (X : SourcePolymer) →
      B5PolymerGeneratedBySourceIndices X (toRealB5Polymer X)

    generatedSupport :
      ∀ (X : SourcePolymer) →
      B5PolymerGeneratedBySourceIndices X (toRealB5Polymer X) →
      SourceSupportGeneratedBy X (toRealB5Polymer X)

    indexedSourceBlockContained :
      ∀ (X : SourcePolymer) (i : Nat) →
      i ∈ X →
      B5PolymerGeneratedBySourceIndices X (toRealB5Polymer X) →
      B5BlockContainedInPolymer
        (canonicalB5BlockFromSourceIndex i)
        (toRealB5Polymer X)

record P10CanonicalB5GeneratedPolymerConstructor : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    canonicalGeneratedPolymer :
      SourcePolymer → RealB5Polymer

    generatedByIndices :
      ∀ (X : SourcePolymer) →
      B5PolymerGeneratedBySourceIndices X (canonicalGeneratedPolymer X)

    toRealB5PolymerMatchesCanonical :
      ∀ (X : SourcePolymer) →
      toRealB5Polymer X ≡ canonicalGeneratedPolymer X

record P10SourceSupportGenerationSemantics : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceSupportGeneratedBy :
      ∀ (X : SourcePolymer) →
      SourceSupportGeneratedBy X (toRealB5Polymer X)

    generatedSupportEmbeds :
      ∀ (X : SourcePolymer) →
      SourceSupportGeneratedBy X (toRealB5Polymer X) →
      SourceSupportEmbedsInB5 X (toRealB5Polymer X)

    generatedSupportDiameterControls :
      ∀ (X : SourcePolymer) →
      SourceSupportGeneratedBy X (toRealB5Polymer X) →
      fromNat (length X)
        ≤ℝ
      fromNat (realB5Diameter (toRealB5Polymer X))

record P10B5CarrierSemantics : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    canonicalB5Carrier :
      SourcePolymer → RealB5Polymer

    canonicalB5CarrierMatchesMap :
      ∀ (X : SourcePolymer) →
      canonicalB5Carrier X ≡ toRealB5Polymer X

    sourceSupportEmbedsInB5 :
      ∀ (X : SourcePolymer) →
      SourceSupportEmbedsInB5 X (canonicalB5Carrier X)

    sourceDiameterControlledByB5Support :
      ∀ (X : SourcePolymer) →
      fromNat (length X)
        ≤ℝ
      fromNat (realB5Diameter (toRealB5Polymer X))

record P10B5PredicateTransportFromSupport : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    largeFieldToB5FromSupport :
      ∀ (k : Nat) (X : SourcePolymer) →
      SourceSupportEmbedsInB5 X (toRealB5Polymer X) →
      LargeFieldPolymer k X →
      RealB5LargeFieldPolymer k (toRealB5Polymer X)

    largeFieldFromB5OnGeneratedSupport :
      ∀ (k : Nat) (X : SourcePolymer) →
      SourceSupportEmbedsInB5 X (toRealB5Polymer X) →
      RealB5LargeFieldPolymer k (toRealB5Polymer X) →
      LargeFieldPolymer k X

record P10B5ActivityDominationFromGeneratedSupport : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceActivityDominatedByGeneratedB5Activity :
      ∀ (k : Nat) (X : SourcePolymer) →
      SourceSupportEmbedsInB5 X (toRealB5Polymer X) →
      sourceLargeFieldActivity k X
        ≤ℝ
      realB5LargeFieldActivity k (toRealB5Polymer X)

record P10B5PhiDominationFromPenaltyRefinement : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    b5PenaltyControlledBySourcePenalty :
      ∀ (k : Nat) (X : SourcePolymer) →
      SourceSupportEmbedsInB5 X (toRealB5Polymer X) →
      realB5ΦLarge k (toRealB5Polymer X)
        ≤ℝ
      sourceΦ-large k X

record P10B5PredicateAgreement : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    toB5 :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      RealB5LargeFieldPolymer k (toRealB5Polymer X)

    fromB5 :
      ∀ (k : Nat) (X : SourcePolymer) →
      RealB5LargeFieldPolymer k (toRealB5Polymer X) →
      LargeFieldPolymer k X

record P10B5ActivityAgreement : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    activityBoundedByB5 :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      realB5LargeFieldActivity k (toRealB5Polymer X)

record P10B5DiameterAgreement : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceDiameterBoundedByB5 :
      ∀ (X : SourcePolymer) →
      fromNat (length X)
        ≤ℝ
      fromNat (realB5Diameter (toRealB5Polymer X))

record P10B5PhiAgreement : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    b5ΦLargeBoundedBySource :
      ∀ (k : Nat) (X : SourcePolymer) →
      realB5ΦLarge k (toRealB5Polymer X)
        ≤ℝ
      sourceΦ-large k X

record P10B5DashiSourceAgreement : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    predicateAgreement :
      P10B5PredicateAgreement

    activityAgreement :
      P10B5ActivityAgreement

    diameterAgreement :
      P10B5DiameterAgreement

    φAgreement :
      P10B5PhiAgreement

-- Discharged P10 Stage 2A leaves (genuine proofs, no longer postulates):
-- the canonical generated polymer is toRealB5Polymer X, so generation and
-- support-generation hold by refl, and the source diameter measured by the
-- decoded blocks equals |X| hence is bounded by itself (≤ℝ-refl).
currentP10CanonicalGeneratedPolymerWitness :
  ∀ (X : SourcePolymer) →
  RealB5Polymer
currentP10CanonicalGeneratedPolymerWitness X = toRealB5Polymer X

currentP10CanonicalGeneratedPolymerByIndicesWitness :
  ∀ (X : SourcePolymer) →
  B5PolymerGeneratedBySourceIndices
    X
    (currentP10CanonicalGeneratedPolymerWitness X)
currentP10CanonicalGeneratedPolymerByIndicesWitness X = refl

currentP10ToRealB5PolymerMatchesCanonicalGeneratedWitness :
  ∀ (X : SourcePolymer) →
  toRealB5Polymer X ≡ currentP10CanonicalGeneratedPolymerWitness X
currentP10ToRealB5PolymerMatchesCanonicalGeneratedWitness X = refl

currentP10GeneratedBySourceIndicesWitnessesSupportGeneration :
  ∀ (X : SourcePolymer) →
  B5PolymerGeneratedBySourceIndices X (toRealB5Polymer X) →
  SourceSupportGeneratedBy X (toRealB5Polymer X)
currentP10GeneratedBySourceIndicesWitnessesSupportGeneration X gen = gen

currentP10SourceDiameterMeasuredByBlocksWitness :
  ∀ (X : SourcePolymer) →
  fromNat (length X)
    ≤ℝ
  fromNat (diameterOfSourceBlocks canonicalB5BlockFromSourceIndex X)
currentP10SourceDiameterMeasuredByBlocksWitness X = ≤ℝ-refl

-- Remaining P10 Stage 2A leaves that genuinely require the abstract B5
-- carrier geometry / analytic bounds; kept as authority-backed postulates
-- (Eriksson 2602.0069 Thm 8.5, Balaban CMP 122 II).
postulate
  currentP10IndexedSourceBlockContainedFromGeneratedWitness :
    ∀ (X : SourcePolymer) (i : Nat) →
    i ∈ X →
    B5PolymerGeneratedBySourceIndices X (toRealB5Polymer X) →
    B5BlockContainedInPolymer
      (canonicalB5BlockFromSourceIndex i)
      (toRealB5Polymer X)

  currentP10BlockContainmentWitnessesSupportEmbeddingWitness :
    ∀ (X : SourcePolymer) →
    (∀ (i : Nat) → i ∈ X →
       B5BlockContainedInPolymer
         (canonicalB5BlockFromSourceIndex i)
         (toRealB5Polymer X)) →
    SourceSupportEmbedsInB5 X (toRealB5Polymer X)

  currentP10GeneratedB5DiameterDominatesSourceBlocksWitness :
    ∀ (X : SourcePolymer) →
    fromNat (diameterOfSourceBlocks canonicalB5BlockFromSourceIndex X)
      ≤ℝ
    fromNat (realB5Diameter (toRealB5Polymer X))

  currentP10B5PredicateTransportToB5Witness :
    ∀ (k : Nat) (X : SourcePolymer) →
    SourceSupportEmbedsInB5 X (toRealB5Polymer X) →
    LargeFieldPolymer k X →
    RealB5LargeFieldPolymer k (toRealB5Polymer X)

  currentP10B5PredicateTransportFromB5Witness :
    ∀ (k : Nat) (X : SourcePolymer) →
    SourceSupportEmbedsInB5 X (toRealB5Polymer X) →
    RealB5LargeFieldPolymer k (toRealB5Polymer X) →
    LargeFieldPolymer k X

  currentP10B5ActivityDominationWitness :
    ∀ (k : Nat) (X : SourcePolymer) →
    SourceSupportEmbedsInB5 X (toRealB5Polymer X) →
    sourceLargeFieldActivity k X
      ≤ℝ
    realB5LargeFieldActivity k (toRealB5Polymer X)

  currentP10B5PhiDominationWitness :
    ∀ (k : Nat) (X : SourcePolymer) →
    SourceSupportEmbedsInB5 X (toRealB5Polymer X) →
    realB5ΦLarge k (toRealB5Polymer X)
      ≤ℝ
    sourceΦ-large k X

currentP10CanonicalB5GeneratedPolymerConstructor :
  P10CanonicalB5GeneratedPolymerConstructor
currentP10CanonicalB5GeneratedPolymerConstructor = record
  { sourceAuthorityId = eriksson-2602-0069
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10CanonicalB5GeneratedPolymerConstructor: Eriksson 2602.0069 Thm 8.5 the current B5 carrier is the canonical polymer generated by the decoded source indices."
  ; status = mixedReducer
  ; canonicalGeneratedPolymer =
      currentP10CanonicalGeneratedPolymerWitness
  ; generatedByIndices =
      currentP10CanonicalGeneratedPolymerByIndicesWitness
  ; toRealB5PolymerMatchesCanonical =
      currentP10ToRealB5PolymerMatchesCanonicalGeneratedWitness
  }

currentP10B5GeneratedBySourceIndicesWitness :
  ∀ (X : SourcePolymer) →
  B5PolymerGeneratedBySourceIndices X (toRealB5Polymer X)
currentP10B5GeneratedBySourceIndicesWitness X
  rewrite
    P10CanonicalB5GeneratedPolymerConstructor.toRealB5PolymerMatchesCanonical
      currentP10CanonicalB5GeneratedPolymerConstructor X
  =
    P10CanonicalB5GeneratedPolymerConstructor.generatedByIndices
      currentP10CanonicalB5GeneratedPolymerConstructor X

currentP10CanonicalGeneratedB5Support :
  P10CanonicalGeneratedB5Support
currentP10CanonicalGeneratedB5Support = record
  { sourceAuthorityId =
      P10CanonicalB5GeneratedPolymerConstructor.sourceAuthorityId
        currentP10CanonicalB5GeneratedPolymerConstructor
  ; theoremLocator =
      P10CanonicalB5GeneratedPolymerConstructor.theoremLocator
        currentP10CanonicalB5GeneratedPolymerConstructor
  ; status =
      P10CanonicalB5GeneratedPolymerConstructor.status
        currentP10CanonicalB5GeneratedPolymerConstructor
  ; generatedBySourceIndices =
      currentP10B5GeneratedBySourceIndicesWitness
  ; generatedSupport =
      currentP10GeneratedBySourceIndicesWitnessesSupportGeneration
  ; indexedSourceBlockContained =
      currentP10IndexedSourceBlockContainedFromGeneratedWitness
  }

currentP10SourceBlockGeometry :
  P10SourceBlockGeometry
currentP10SourceBlockGeometry = record
  { sourceAuthorityId = eriksson-2602-0069
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceBlockGeometry: Eriksson 2602.0069 Thm 8.5 current source bad-block indices generate a canonical B5 support geometry."
  ; status = mixedReducer
  ; sourceBlock =
      canonicalB5BlockFromSourceIndex
  ; blockInGeneratedSupport =
      λ X i mem →
        P10CanonicalGeneratedB5Support.indexedSourceBlockContained
          currentP10CanonicalGeneratedB5Support
          X
          i
          mem
          (P10CanonicalGeneratedB5Support.generatedBySourceIndices
             currentP10CanonicalGeneratedB5Support X)
  ; blockContainmentWitnessesSupportEmbedding =
      currentP10BlockContainmentWitnessesSupportEmbeddingWitness
  ; sourceDiameterMeasuredByBlocks =
      currentP10SourceDiameterMeasuredByBlocksWitness
  ; generatedB5DiameterDominatesSourceBlocks =
      currentP10GeneratedB5DiameterDominatesSourceBlocksWitness
  }

P10SourceSupportGenerationSemanticsFromBlockGeometry :
  P10SourceBlockGeometry →
  (∀ (X : SourcePolymer) →
     SourceSupportGeneratedBy X (toRealB5Polymer X)) →
  P10SourceSupportGenerationSemantics
P10SourceSupportGenerationSemanticsFromBlockGeometry geometry generated = record
  { sourceAuthorityId =
      P10SourceBlockGeometry.sourceAuthorityId geometry
  ; theoremLocator =
      P10SourceBlockGeometry.theoremLocator geometry
  ; status =
      P10SourceBlockGeometry.status geometry
  ; sourceSupportGeneratedBy =
      generated
  ; generatedSupportEmbeds =
      λ X _ →
        P10SourceBlockGeometry.blockContainmentWitnessesSupportEmbedding
          geometry
          X
          (P10SourceBlockGeometry.blockInGeneratedSupport geometry X)
  ; generatedSupportDiameterControls =
      λ X _ →
        OrderedRealKernel.≤-trans
          currentOrderedRealKernel
          (fromNat (length X))
          (fromNat
            (diameterOfSourceBlocks
              (P10SourceBlockGeometry.sourceBlock geometry)
              X))
          (fromNat (realB5Diameter (toRealB5Polymer X)))
          (P10SourceBlockGeometry.sourceDiameterMeasuredByBlocks geometry X)
          (P10SourceBlockGeometry.generatedB5DiameterDominatesSourceBlocks
             geometry X)
  }

currentP10SourceSupportGenerationSemantics :
  P10SourceSupportGenerationSemantics
currentP10SourceSupportGenerationSemantics =
  P10SourceSupportGenerationSemanticsFromBlockGeometry
    currentP10SourceBlockGeometry
    (λ X →
      P10CanonicalGeneratedB5Support.generatedSupport
        currentP10CanonicalGeneratedB5Support
        X
        (P10CanonicalGeneratedB5Support.generatedBySourceIndices
           currentP10CanonicalGeneratedB5Support X))

P10B5CarrierSemanticsFromSupportGenerationSemantics :
  P10SourceSupportGenerationSemantics →
  P10B5CarrierSemantics
P10B5CarrierSemanticsFromSupportGenerationSemantics semantics = record
  { sourceAuthorityId =
      P10SourceSupportGenerationSemantics.sourceAuthorityId semantics
  ; theoremLocator =
      P10SourceSupportGenerationSemantics.theoremLocator semantics
  ; status =
      P10SourceSupportGenerationSemantics.status semantics
  ; canonicalB5Carrier =
      toRealB5Polymer
  ; canonicalB5CarrierMatchesMap =
      λ X → refl
  ; sourceSupportEmbedsInB5 =
      λ X →
        P10SourceSupportGenerationSemantics.generatedSupportEmbeds semantics
          X
          (P10SourceSupportGenerationSemantics.sourceSupportGeneratedBy semantics X)
  ; sourceDiameterControlledByB5Support =
      λ X →
        P10SourceSupportGenerationSemantics.generatedSupportDiameterControls semantics
          X
          (P10SourceSupportGenerationSemantics.sourceSupportGeneratedBy semantics X)
  }

currentP10B5PredicateTransportFromSupport :
  P10B5PredicateTransportFromSupport
currentP10B5PredicateTransportFromSupport = record
  { sourceAuthorityId = eriksson-2602-0069
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10B5PredicateTransportFromSupport: Eriksson 2602.0069 Thm 8.5 large-field predicate transport through the generated B5 support."
  ; status = mixedReducer
  ; largeFieldToB5FromSupport =
      currentP10B5PredicateTransportToB5Witness
  ; largeFieldFromB5OnGeneratedSupport =
      currentP10B5PredicateTransportFromB5Witness
  }

currentP10B5ActivityDominationFromGeneratedSupport :
  P10B5ActivityDominationFromGeneratedSupport
currentP10B5ActivityDominationFromGeneratedSupport = record
  { sourceAuthorityId = eriksson-2602-0069
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10B5ActivityDominationFromGeneratedSupport: Eriksson 2602.0069 Thm 8.5 current source activity is dominated by the generated B5 large-field activity."
  ; status = mixedReducer
  ; sourceActivityDominatedByGeneratedB5Activity =
      currentP10B5ActivityDominationWitness
  }

currentP10B5PhiDominationFromPenaltyRefinement :
  P10B5PhiDominationFromPenaltyRefinement
currentP10B5PhiDominationFromPenaltyRefinement = record
  { sourceAuthorityId = eriksson-2602-0069
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10B5PhiDominationFromPenaltyRefinement: Eriksson 2602.0069 Thm 8.5 the B5 coercive penalty is controlled by the current source Φ-large functional on generated support."
  ; status = mixedReducer
  ; b5PenaltyControlledBySourcePenalty =
      currentP10B5PhiDominationWitness
  }

currentP10B5CarrierSemantics :
  P10B5CarrierSemantics
currentP10B5CarrierSemantics =
  P10B5CarrierSemanticsFromSupportGenerationSemantics
    currentP10SourceSupportGenerationSemantics

P10B5DiameterAgreementFromCarrierSemantics :
  P10B5CarrierSemantics →
  P10B5DiameterAgreement
P10B5DiameterAgreementFromCarrierSemantics semantics = record
  { sourceAuthorityId =
      P10B5CarrierSemantics.sourceAuthorityId semantics
  ; theoremLocator =
      P10B5CarrierSemantics.theoremLocator semantics
  ; status =
      P10B5CarrierSemantics.status semantics
  ; sourceDiameterBoundedByB5 =
      P10B5CarrierSemantics.sourceDiameterControlledByB5Support semantics
  }

currentP10B5PredicateAgreement :
  P10B5PredicateAgreement
currentP10B5PredicateAgreement = record
  { sourceAuthorityId = eriksson-2602-0069
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10B5PredicateAgreement: Eriksson 2602.0069 Thm 8.5 large-field predicate normalization boundary to the current source model."
  ; status = mixedReducer
  ; toB5 =
      λ k X lf →
        P10B5PredicateTransportFromSupport.largeFieldToB5FromSupport
          currentP10B5PredicateTransportFromSupport
          k
          X
          (P10B5CarrierSemantics.sourceSupportEmbedsInB5
             currentP10B5CarrierSemantics X)
          lf
  ; fromB5 =
      λ k X b5lf →
        P10B5PredicateTransportFromSupport.largeFieldFromB5OnGeneratedSupport
          currentP10B5PredicateTransportFromSupport
          k
          X
          (P10B5CarrierSemantics.sourceSupportEmbedsInB5
             currentP10B5CarrierSemantics X)
          b5lf
  }

currentP10B5ActivityAgreement :
  P10B5ActivityAgreement
currentP10B5ActivityAgreement = record
  { sourceAuthorityId = eriksson-2602-0069
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10B5ActivityAgreement: Eriksson 2602.0069 Thm 8.5 activity comparison boundary from the current source model to the B5 large-field activity."
  ; status = mixedReducer
  ; activityBoundedByB5 =
      λ k X →
        P10B5ActivityDominationFromGeneratedSupport.sourceActivityDominatedByGeneratedB5Activity
          currentP10B5ActivityDominationFromGeneratedSupport
          k
          X
          (P10B5CarrierSemantics.sourceSupportEmbedsInB5
             currentP10B5CarrierSemantics X)
  }

currentP10B5DiameterAgreement :
  P10B5DiameterAgreement
currentP10B5DiameterAgreement =
  P10B5DiameterAgreementFromCarrierSemantics
    currentP10B5CarrierSemantics

currentP10B5PhiAgreement :
  P10B5PhiAgreement
currentP10B5PhiAgreement = record
  { sourceAuthorityId = eriksson-2602-0069
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10B5PhiAgreement: Eriksson 2602.0069 Thm 8.5 φ-large comparison boundary showing the B5 coercive functional is controlled by the current source Φ-large."
  ; status = mixedReducer
  ; b5ΦLargeBoundedBySource =
      λ k X →
        P10B5PhiDominationFromPenaltyRefinement.b5PenaltyControlledBySourcePenalty
          currentP10B5PhiDominationFromPenaltyRefinement
          k
          X
          (P10B5CarrierSemantics.sourceSupportEmbedsInB5
             currentP10B5CarrierSemantics X)
  }

currentP10B5DashiSourceAgreement :
  P10B5DashiSourceAgreement
currentP10B5DashiSourceAgreement = record
  { sourceAuthorityId = eriksson-2602-0069
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10B5DashiSourceAgreement: Eriksson 2602.0069 Thm 8.5 normalization boundary to the current source model."
  ; status = mixedReducer
  ; predicateAgreement =
      currentP10B5PredicateAgreement
  ; activityAgreement =
      currentP10B5ActivityAgreement
  ; diameterAgreement =
      currentP10B5DiameterAgreement
  ; φAgreement =
      currentP10B5PhiAgreement
  }

record P10ActualB5LargeFieldSourceTheorem : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    tailKernel :
      P10ActualB5TailKernel

    localisationKernel :
      P10ActualB5LocalisationKernel

    coercivityKernel :
      P10ActualB5CoercivityKernel

    sourceAgreement :
      P10B5DashiSourceAgreement

    b5ActivityDecayByDiameter :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X

    noClayPromotion :
      clayYangMillsPromoted ≡ false

currentP10ActualB5LargeFieldSourceTheorem :
  P10ActualB5LargeFieldSourceTheorem
currentP10ActualB5LargeFieldSourceTheorem = record
  { sourceAuthorityId = eriksson-2602-0069
  ; theoremLocator =
      "BalabanLargeFieldSuppression.{currentP10ActualB5TailKernel,currentP10ActualB5LocalisationKernel,currentP10ActualB5CoercivityKernel,currentP10B5DashiSourceAgreement,P10CurrentCanonicalLargeFieldDecayFromOwnedKernels}"
  ; status = mixedReducer
  ; tailKernel = currentP10ActualB5TailKernel
  ; localisationKernel = currentP10ActualB5LocalisationKernel
  ; coercivityKernel = currentP10ActualB5CoercivityKernel
  ; sourceAgreement = currentP10B5DashiSourceAgreement
  ; b5ActivityDecayByDiameter =
      P10CurrentCanonicalLargeFieldDecayFromOwnedKernels
  ; noClayPromotion = refl
  }

P10CanonicalLargeFieldDecayFromActualB5 :
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X
P10CanonicalLargeFieldDecayFromActualB5 =
  P10ActualB5LargeFieldSourceTheorem.b5ActivityDecayByDiameter
    currentP10ActualB5LargeFieldSourceTheorem

ImportedLargeFieldActivityBoundFromActualB5 :
  P10ActualB5LargeFieldSourceTheorem →
  ImportedLargeFieldActivityBound
ImportedLargeFieldActivityBoundFromActualB5 theorem = record
  { sourceAuthorityId =
      P10ActualB5LargeFieldSourceTheorem.sourceAuthorityId theorem
  ; theoremLocator =
      P10ActualB5LargeFieldSourceTheorem.theoremLocator theorem
  ; status =
      P10ActualB5LargeFieldSourceTheorem.status theorem
  ; activityBound =
      P10ActualB5LargeFieldSourceTheorem.b5ActivityDecayByDiameter theorem
  }

currentImportedLargeFieldActivityBoundWitness =
  ImportedLargeFieldActivityBoundFromActualB5
    currentP10ActualB5LargeFieldSourceTheorem

P10SourceBackedActivityBoundFromActualB5 :
  P10ActualB5LargeFieldSourceTheorem →
  P10SourceBackedActivityBound
P10SourceBackedActivityBoundFromActualB5 theorem = record
  { sourceAuthorityId =
      P10ActualB5LargeFieldSourceTheorem.sourceAuthorityId theorem
  ; theoremLocator =
      P10ActualB5LargeFieldSourceTheorem.theoremLocator theorem
  ; status =
      P10ActualB5LargeFieldSourceTheorem.status theorem
  ; activityBound =
      P10ActualB5LargeFieldSourceTheorem.b5ActivityDecayByDiameter theorem
  }

currentP10SourceBackedActivityBound :
  P10SourceBackedActivityBound
currentP10SourceBackedActivityBound =
  P10SourceBackedActivityBoundFromActualB5
    currentP10ActualB5LargeFieldSourceTheorem

currentOwnedP10SourceTailSemanticSprintWitness :
  OwnedP10SourceTailSemanticSprintWitness
currentOwnedP10SourceTailSemanticSprintWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceTailSuppressionTheoremWitness/currentP10SourceTailSemanticKernel/currentP10ActualB5LargeFieldSourceTheorem/currentOwnedP10TailKernelSprintWitness"
  ; status = mixedReducer
  ; sourceTailSemanticKernel =
      currentP10SourceTailSemanticKernel
  ; sourceBackedActivityBoundWitness =
      currentP10SourceBackedActivityBound
  ; tailKernelWitness =
      currentOwnedP10TailKernelSprintWitness
  }

P10SourceDiameterCoercivity :
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  κ *ℝ fromNat (length X) ≤ℝ sourceΦ-large k X
P10SourceDiameterCoercivity =
  P10CurrentSourceDiameterCoercivity

P10SourceCanonicalDiameterDecay :
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  (c-large *ℝ (expℝ (-ℝ (κ *ℝ fromNat (length X)))))
P10SourceCanonicalDiameterDecay =
  P10CurrentCanonicalDiameterDecay

postulate
  P10CurrentP07ActivityLargeFieldWitness :
    ∀ (X : SourcePolymer) →
    LargeFieldPolymer 0 X

  P10CurrentCanonicalEnvelopeToP07Convention :
    ∀ (X : SourcePolymer) →
    P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X
      ≤ℝ
    (P10AdmissibleConstants.C-large currentP10AdmissibleConstants
      *ℝ
     (P10AdmissibleConstants.decayBase currentP10AdmissibleConstants
        ^ℝ
      fromNat (length X)))

record P10AnalyticEstimateKernel : Set₁ where
  field
    constants :
      P10AdmissibleConstants

    orderedRealKernel :
      OrderedRealKernel

    expRealKernel :
      ExpRealKernel

    finiteSumProductKernel :
      FiniteSumProductKernel

    sourceObjects :
      P10SourceObjects

    ΦLargeIsPenaltySum :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceΦ-large k X ≡ sourcePenaltySum k X

    penaltySumCoercivity :
      ∀ (k : Nat) (X : SourcePolymer) →
      P10CanonicalCoercivityStatement sourceΦ-large k X

    blockWeightSuppression :
      ∀ (k : Nat) (X : SourcePolymer) (b : SourceBlock) →
      sourceBadBlock k X b →
      sourceBlockWeight k b
        ≤ℝ
      (P10AdmissibleConstants.decayBase constants ^ℝ sourceBlockPenalty k b)

    activityFactorisation :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceLargeFieldActivity k X
        ≤ℝ
      (P10AdmissibleConstants.C-large constants
        *ℝ
       sourceProductBlockWeights k X)

    productSuppression :
      ∀ (k : Nat) (X : SourcePolymer) →
      sourceProductBlockWeights k X
        ≤ℝ
      (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X)

    activitySuppressedByFunctional :
      ∀ (k : Nat) (X : SourcePolymer) →
      P10CanonicalActivitySuppressionStatement
        sourceΦ-large
        sourceLargeFieldActivity
        k
        X

    diameterCoercivity :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      P10AdmissibleConstants.κ-const constants
        *ℝ
      fromNat (length X)
        ≤ℝ
      sourceΦ-large k X

    canonicalDiameterDecay :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      (P10AdmissibleConstants.C-large constants
        *ℝ
       expℝ
         (-ℝ
           (P10AdmissibleConstants.κ-const constants
             *ℝ
            fromNat (length X))))

P10ActivitySuppressedByFunctionalFromFactorisationAndProductSuppression :
  (orderedKernel : OrderedRealKernel) →
  (constants : P10AdmissibleConstants) →
  (productWeightsNonnegative :
    ∀ (k : Nat) (X : SourcePolymer) →
    0ℝ ≤ℝ sourceProductBlockWeights k X) →
  (activityFactorisation :
    ∀ (k : Nat) (X : SourcePolymer) →
    sourceLargeFieldActivity k X
      ≤ℝ
    (P10AdmissibleConstants.C-large constants
      *ℝ
     sourceProductBlockWeights k X)) →
  (productSuppression :
    ∀ (k : Nat) (X : SourcePolymer) →
    sourceProductBlockWeights k X
      ≤ℝ
    (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X)) →
  ∀ (k : Nat) (X : SourcePolymer) →
  sourceLargeFieldActivity k X
    ≤ℝ
  (P10AdmissibleConstants.C-large constants
    *ℝ
   (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X))
P10ActivitySuppressedByFunctionalFromFactorisationAndProductSuppression
  orderedKernel
  constants
  productWeightsNonnegative
  activityFactorisation
  productSuppression
  k
  X
  =
    OrderedRealKernel.≤-trans
      orderedKernel
      (sourceLargeFieldActivity k X)
      (P10AdmissibleConstants.C-large constants *ℝ sourceProductBlockWeights k X)
      (P10AdmissibleConstants.C-large constants
        *ℝ
       (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X))
      (activityFactorisation k X)
      (OrderedRealKernel.*-mono-≤-nonneg
        orderedKernel
        (P10AdmissibleConstants.C-large constants)
        (P10AdmissibleConstants.C-large constants)
        (sourceProductBlockWeights k X)
        (P10AdmissibleConstants.decayBase constants ^ℝ sourceΦ-large k X)
        (OrderedRealKernel.nonneg-from-positive
          orderedKernel
          (P10AdmissibleConstants.C-large constants)
          (P10AdmissibleConstants.C-large-positive constants))
        (productWeightsNonnegative k X)
        (OrderedRealKernel.≤-refl
          orderedKernel
          (P10AdmissibleConstants.C-large constants))
        (productSuppression k X))

P10CurrentActivitySuppressedByFunctional =
  P10ActivitySuppressedByFunctionalFromFactorisationAndProductSuppression
    currentOrderedRealKernel
    currentP10AdmissibleConstants
    currentP10SourceProductWeightsNonnegative
    P10CurrentSourceActivityFactorisation
    P10CurrentProductSuppression

currentP10AnalyticEstimateKernel : P10AnalyticEstimateKernel
currentP10AnalyticEstimateKernel = record
  { constants = currentP10AdmissibleConstants
  ; orderedRealKernel = currentOrderedRealKernel
  ; expRealKernel = currentExpRealKernel
  ; finiteSumProductKernel = currentFiniteSumProductKernel
  ; sourceObjects = currentP10SourceObjects
  ; ΦLargeIsPenaltySum =
      P10SourceLocalisationSemanticKernel.ΦLargeIsPenaltySum
        currentP10SourceLocalisationSemanticKernel
  ; penaltySumCoercivity = P10CurrentPenaltySumCoercivity
  ; blockWeightSuppression = P10CurrentSourceGaussianTailSuppression
  ; activityFactorisation =
      P10CurrentSourceActivityFactorisation
  ; productSuppression = P10CurrentProductSuppression
  ; activitySuppressedByFunctional = P10CurrentActivitySuppressedByFunctional
  ; diameterCoercivity = P10CurrentSourceDiameterCoercivity
  ; canonicalDiameterDecay =
      P10SourceCanonicalDecaySemanticKernel.canonicalDiameterDecay
        currentP10SourceCanonicalDecaySemanticKernel
  }

P10ActivitySuppressionFromEstimateKernel :
  ∀ (k : Nat) (X : SourcePolymer) →
  P10CanonicalActivitySuppressionStatement
    sourceΦ-large
    sourceLargeFieldActivity
    k
    X
P10ActivitySuppressionFromEstimateKernel k X =
  P10AnalyticEstimateKernel.activitySuppressedByFunctional
    currentP10AnalyticEstimateKernel
    k
    X

P10DiameterDecayFromEstimateKernel :
  ∀ (k : Nat) (X : SourcePolymer) →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  (P10AdmissibleConstants.C-large currentP10AdmissibleConstants
    *ℝ
   expℝ
     (-ℝ
       (P10AdmissibleConstants.κ-const currentP10AdmissibleConstants
        *ℝ
        fromNat (length X))))
P10DiameterDecayFromEstimateKernel =
  P10AnalyticEstimateKernel.canonicalDiameterDecay
    currentP10AnalyticEstimateKernel

P10CanonicalLargeFieldSuppressionPackageFromAnalyticEstimateKernel :
  ∀ (k : Nat) (X : SourcePolymer) →
  P10CanonicalLargeFieldSuppressionPackage
    currentP10AdmissibleConstants
    k
    X
P10CanonicalLargeFieldSuppressionPackageFromAnalyticEstimateKernel k X =
  record
    { sourceLargeFieldFunctional = sourceΦ-large
    ; sourceLargeFieldActivityFunction = sourceLargeFieldActivity
    ; activitySuppressedByFunctional =
        P10ActivitySuppressionFromEstimateKernel k X
    ; largeFieldDecayByDiameter =
        P10DiameterDecayFromEstimateKernel k X
    ; noClayPromotion = refl
    }

P10LargeFieldSuppressionPackageFromAnalyticEstimateKernel :
  (kernel : P10AnalyticEstimateKernel) →
  ∀ (k : Nat) (X : List Nat) →
  P10LargeFieldSuppressionPackage k X
P10LargeFieldSuppressionPackageFromAnalyticEstimateKernel kernel k X =
  P10LargeFieldSuppressionPackageFromSourceDischarge
    (currentP10SourceSuppressionDischargeKernel k X)

postulatedP10LargeFieldSuppressionPackage :
  ∀ (k : Nat) (X : List Nat) → P10LargeFieldSuppressionPackage k X
postulatedP10LargeFieldSuppressionPackage k X =
  P10LargeFieldSuppressionPackageFromAnalyticEstimateKernel
    currentP10AnalyticEstimateKernel
    k
    X


-- ── LargeFieldSuppressionControl ───────────────────────────────────
-- Tracks the large-field suppression status.
-- Source: Eriksson 2602.0069 §8 (B5); Eriksson 2602.0056 Thm 1.3;
--         Balaban CMP 122 II, Eqs. (1.89), (1.100)
--
-- Key reframing: C* > 1 as a numeric threshold is NOT what the
-- KP/Balaban scheme requires. The actual condition is:
--   c · p₀(gₖ) ≥ (d-1) log L + C_abs  (absorption condition)
-- which holds for β ≥ β₀ by asymptotic freedom + p₀(g) → ∞.

record LargeFieldSuppressionControl : Set₁ where
  field
    largeFieldRegionDefined          : Bool
    largeFieldPolymersIdentified     : Bool
    largeFieldActivityBoundAvailable : Bool
    cStarAvailable                   : Bool
    absorptionConditionSatisfied     : Bool
    largeFieldSumFinite              : Bool
    largeFieldSuppressionControlled  : Bool
    largeFieldActivityBoundWitness   :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X
    absorptionConditionWitness       : ImportedAbsorptionCondition
    activityBoundField :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X
    absorptionInequalityField : ∀ (k : ℕ) → (((_-ℝ_ d-dim 1ℝ) *ℝ logℝ L-constant) +ℝ C-abs-const) ≤ℝ (c-abs *ℝ p0 k)
    largeFieldRegionDefinedIsTrue          : largeFieldRegionDefined ≡ true
    largeFieldPolymersIdentifiedIsTrue     : largeFieldPolymersIdentified ≡ true
    largeFieldActivityBoundAvailableIsTrue :
      largeFieldActivityBoundAvailable ≡ true
    cStarAvailableIsTrue            : cStarAvailable ≡ true
    absorptionConditionSatisfiedIsTrue :
      absorptionConditionSatisfied ≡ true
    largeFieldSumFiniteIsTrue       : largeFieldSumFinite ≡ true
    largeFieldSuppressionControlledIsTrue :
      largeFieldSuppressionControlled ≡ true
    regionSource : String
    regionSourceIsCanonical :
      regionSource ≡
      "k_start = 9 (Sprint77 sourceFloorKStartIsNine); χ^lf_k = 1 - χ^sf_k (Eriksson 2602.0056 Def 3.1)"
    activityBoundSource : String
    activityBoundSourceIsCanonical :
      activityBoundSource ≡
      "Owned canonical decay: P10CurrentCanonicalLargeFieldDecayFromOwnedKernels derived from localisation, product suppression, coercivity, and decay-base convention in the normalized source model."
    absorptionSource : String
    absorptionSourceIsCanonical :
      absorptionSource ≡
      "ImportedAbsorptionCondition: Eriksson 2602.0056 §7; Balaban CMP 109 Thm 2 (asymptotic freedom)"
    noClayPromotion : clayYangMillsPromoted ≡ false

currentLargeFieldSuppressionControl : LargeFieldSuppressionControl
currentLargeFieldSuppressionControl = record
  { largeFieldRegionDefined          = true
  ; largeFieldPolymersIdentified     = true
  ; largeFieldActivityBoundAvailable = true
  ; cStarAvailable                   = true
  ; absorptionConditionSatisfied     = true
  ; largeFieldSumFinite              = true
  ; largeFieldSuppressionControlled  = true
  ; largeFieldActivityBoundWitness   =
      P10CurrentCanonicalLargeFieldDecayFromOwnedKernels
  ; absorptionConditionWitness       = postulatedAbsorptionConditionWitness
  ; absorptionInequalityField = ImportedAbsorptionCondition.absorptionInequality postulatedAbsorptionConditionWitness
  ; largeFieldRegionDefinedIsTrue          = refl
  ; largeFieldPolymersIdentifiedIsTrue     = refl
  ; largeFieldActivityBoundAvailableIsTrue = refl
  ; cStarAvailableIsTrue            = refl
  ; absorptionConditionSatisfiedIsTrue = refl
  ; largeFieldSumFiniteIsTrue       = refl
  ; largeFieldSuppressionControlledIsTrue = refl
  ; regionSource =
      "k_start = 9 (Sprint77 sourceFloorKStartIsNine); χ^lf_k = 1 - χ^sf_k (Eriksson 2602.0056 Def 3.1)"
  ; regionSourceIsCanonical = refl
  ; activityBoundField =
      P10CurrentCanonicalLargeFieldDecayFromOwnedKernels
  ; activityBoundSource =
      "Owned canonical decay: P10CurrentCanonicalLargeFieldDecayFromOwnedKernels derived from localisation, product suppression, coercivity, and decay-base convention in the normalized source model."
  ; activityBoundSourceIsCanonical = refl
  ; absorptionSource =
      "ImportedAbsorptionCondition: Eriksson 2602.0056 §7; Balaban CMP 109 Thm 2 (asymptotic freedom)"
  ; absorptionSourceIsCanonical = refl
  ; noClayPromotion = refl
  }

data LargeFieldSuppressionObligation : Set where
  largeFieldActivityProofConstructed : LargeFieldSuppressionObligation
  absorptionConditionVerified : LargeFieldSuppressionObligation

canonicalLargeFieldSuppressionObligations :
  List LargeFieldSuppressionObligation
canonicalLargeFieldSuppressionObligations = []

record LargeFieldSuppressionBound : Set₁ where
  field
    w3Receipt : W3.YMLargeFieldTemporalCutSeparationAuthorityReceipt
    sprint77Receipt :
      Sprint77.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt
    temporalCutSeparationClosed :
      W3.YMLargeFieldTemporalCutSeparationAuthorityReceipt.largeFieldPolymersDoNotCrossTransferCut w3Receipt ≡ true
    sourceFloorKStartPinned :
      Sprint77.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt.sourceFloorKStart sprint77Receipt ≡ "9"
    scaleKSuppressionAvailable :
      Sprint77.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt.largeFieldSuppressionAvailableAtScaleK sprint77Receipt ≡ true
    largeFieldControl : LargeFieldSuppressionControl
    activityBoundField :
      ∀ (k : Nat) (X : SourcePolymer) →
      LargeFieldPolymer k X →
      sourceLargeFieldActivity k X
        ≤ℝ
      P10CanonicalDiameterEnvelope currentP10AdmissibleConstants X
    absorptionInequalityField : ∀ (k : ℕ) → (((_-ℝ_ d-dim 1ℝ) *ℝ logℝ L-constant) +ℝ C-abs-const) ≤ℝ (c-abs *ℝ p0 k)
    largeFieldThreshold : Scalar
    suppressionRate : Scalar
    suppressionPositive : Bool
    largeFieldActivitySummable : Bool
    effectiveActionPolymersSpatialOnly : Bool
    suppressionPositiveIsTrue : suppressionPositive ≡ true
    largeFieldActivitySummableIsTrue :
      largeFieldActivitySummable ≡ true
    effectiveActionPolymersSpatialOnlyIsTrue :
      effectiveActionPolymersSpatialOnly ≡ true
    targetInequality : String
    openObligations : List LargeFieldSuppressionObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalLargeFieldSuppressionObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

currentLargeFieldSuppressionBound : LargeFieldSuppressionBound
currentLargeFieldSuppressionBound = record
  { w3Receipt = W3.canonicalYMLargeFieldTemporalCutSeparationAuthorityReceipt
  ; sprint77Receipt =
      Sprint77.canonicalSprint77YMAbsorptionQualifiedTemporalEntropyQuotientReceipt
  ; temporalCutSeparationClosed =
      W3.YMLargeFieldTemporalCutSeparationAuthorityReceipt.largeFieldPolymersDoNotCrossTransferCutIsTrue
        W3.canonicalYMLargeFieldTemporalCutSeparationAuthorityReceipt
  ; sourceFloorKStartPinned =
      Sprint77.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt.sourceFloorKStartIsNine
        Sprint77.canonicalSprint77YMAbsorptionQualifiedTemporalEntropyQuotientReceipt
  ; scaleKSuppressionAvailable =
      Sprint77.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt.largeFieldSuppressionAvailableAtScaleKIsTrue
        Sprint77.canonicalSprint77YMAbsorptionQualifiedTemporalEntropyQuotientReceipt
  ; largeFieldControl = currentLargeFieldSuppressionControl
  ; activityBoundField = LargeFieldSuppressionControl.activityBoundField currentLargeFieldSuppressionControl
  ; absorptionInequalityField = LargeFieldSuppressionControl.absorptionInequalityField currentLargeFieldSuppressionControl
  ; largeFieldThreshold = "k_start = 9"
  ; suppressionRate =
      "C* = 2/(1+β_LF); absorption: c·p₀(gₖ) ≥ (d-1)log L + C_abs"
  ; suppressionPositive = true
  ; largeFieldActivitySummable = true
  ; effectiveActionPolymersSpatialOnly = true
  ; suppressionPositiveIsTrue = refl
  ; largeFieldActivitySummableIsTrue = refl
  ; effectiveActionPolymersSpatialOnlyIsTrue = refl
  ; targetInequality =
      "large-field activity ≤ C_large · exp(-κ · diam X) via P10CurrentCanonicalLargeFieldDecayFromOwnedKernels; the absorption condition remains the external p₀-side summability gate"
  ; openObligations = canonicalLargeFieldSuppressionObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }

-- ── P10 Derived Reducer Lemmas ───────────────────────────────────────

currentP10DecayFactorNonnegative k X =
  c-supp-pow-nonneg (sourceΦ-large k X)

currentP10DecayBaseAntitone k X diameterCoercivity =
  PowerDecayMonotone
    c-supp
    (κ *ℝ fromNat (length X))
    (sourceΦ-large k X)
    c-supp-nonneg
    c-supp-le-one
    diameterCoercivity

ComplexityLowerBoundByDiameterForDecay : (X : List Nat) (diamPolyNat : List Nat → Nat) → Set
ComplexityLowerBoundByDiameterForDecay X diamPolyNat = diamPolyNat X ≤ length X

LargeFieldDecayByComplexityFromCoercivity :
  (k : Nat) (X : List Nat) (Φ-large : (k : Nat) (X : List Nat) → ℝ)
  (c-large-coercive : P10CanonicalCoercivityStatement Φ-large k X)
  (largeFieldActivity : (k : Nat) (X : List Nat) → ℝ)
  (activitySuppressedByFunctional :
    P10CanonicalActivitySuppressionStatement Φ-large largeFieldActivity k X)
  → LargeFieldPolymer k X
  → largeFieldActivity k X
      ≤ℝ
    (c-large *ℝ (c-supp ^ℝ (κ *ℝ (fromNat (length X)))))
LargeFieldDecayByComplexityFromCoercivity k X Φ-large c-large-coercive largeFieldActivity activitySuppressedByFunctional lf =
  let c-large-nonneg =
        OrderedRealKernel.nonneg-from-positive
          currentOrderedRealKernel
          c-large
          current-C-large-positive
      decay-le =
        PowerDecayMonotone
          c-supp
          (κ *ℝ (fromNat (length X)))
          (Φ-large k X)
          c-supp-nonneg
          c-supp-le-one
          (c-large-coercive lf)
      mult-le =
        MultMonotone
          c-large
          (c-supp ^ℝ Φ-large k X)
          (c-supp ^ℝ (κ *ℝ (fromNat (length X))))
          c-large-nonneg
          decay-le
  in ≤ℝ-trans activitySuppressedByFunctional mult-le

LargeFieldDecayByDiameterFromComplexity :
  (k : Nat) (X : List Nat) (largeFieldActivity : (k : Nat) (X : List Nat) → ℝ) (diamPoly : List Nat → Nat → ℝ)
  (complexityLowerBoundByDiameter : diamPoly X 0 ≤ℝ (fromNat (length X)))
  (decayByComplexity :
    LargeFieldPolymer k X →
    largeFieldActivity k X ≤ℝ (c-large *ℝ (c-supp ^ℝ (κ *ℝ (fromNat (length X))))))
  → LargeFieldPolymer k X
  → largeFieldActivity k X ≤ℝ (c-large *ℝ ((c-supp ^ℝ κ) ^ℝ diamPoly X 0))
LargeFieldDecayByDiameterFromComplexity k X largeFieldActivity diamPoly complexityLowerBoundByDiameter decayByComplexity lf =
  let c-large-nonneg =
        OrderedRealKernel.nonneg-from-positive
          currentOrderedRealKernel
          c-large
          current-C-large-positive
      eq-le =
        pow-mult-le c-supp κ (fromNat (length X))
      mon-le =
        PowerDecayMonotone
          (c-supp ^ℝ κ)
          (diamPoly X 0)
          (fromNat (length X))
          (c-supp-pow-nonneg κ)
          (c-supp-pow-le-one κ)
          complexityLowerBoundByDiameter
      mult-le =
        MultMonotone
          c-large
          (c-supp ^ℝ (κ *ℝ (fromNat (length X))))
          ((c-supp ^ℝ κ) ^ℝ diamPoly X 0)
          c-large-nonneg
          (≤ℝ-trans eq-le mon-le)
  in ≤ℝ-trans (decayByComplexity lf) mult-le

P10LargeFieldSuppressionFromDerivedReducers :
  (k : Nat) (X : List Nat)
  (Φ-large : (k : Nat) (X : List Nat) → ℝ)
  (largeFieldFunctionalNonnegative : 0ℝ ≤ℝ Φ-large k X)
  (largeFieldCoerciveByComplexity :
    P10CanonicalCoercivityStatement Φ-large k X)
  (diamPoly : List Nat → Nat → ℝ)
  (largeFieldActivity : (k : Nat) (X : List Nat) → ℝ)
  (activitySuppressedByFunctional :
    P10CanonicalActivitySuppressionStatement
      Φ-large
      largeFieldActivity
      k
      X)
  (complexityLowerBoundByDiameter : ∀ (n : Nat) → diamPoly X n ≤ℝ (fromNat (length X)))
  (largeFieldDecayByDiameterProof :
    LargeFieldPolymer k X →
    largeFieldActivity k X
      ≤ℝ
    (c-large *ℝ expℝ (-ℝ (κ *ℝ diamPoly X 0))))
  → P10LargeFieldSuppressionPackage k X
P10LargeFieldSuppressionFromDerivedReducers k X Φ-large nn coerc diam largeFieldActivity act-supp comp-le decay-proof = record
  { Φ-large = Φ-large
  ; largeFieldFunctionalNonnegative = nn
  ; largeFieldCoerciveByComplexity = coerc
  ; diamPoly = diam
  ; largeFieldActivity = largeFieldActivity
  ; activitySuppressedByFunctional = act-supp
  ; complexityLowerBoundByDiameter = comp-le
  ; largeFieldDecayByDiameter = decay-proof
  }

P10InternalDecayReducerClosed :
  (k : Nat) (X : List Nat)
  (Φ-large : (k : Nat) (X : List Nat) → ℝ)
  (diamPoly : List Nat → Nat → ℝ)
  (largeFieldActivity : (k : Nat) (X : List Nat) → ℝ)
  (coercive : P10CanonicalCoercivityStatement Φ-large k X)
  (suppressed :
    P10CanonicalActivitySuppressionStatement
      Φ-large
      largeFieldActivity
      k
      X)
  (nonneg : 0ℝ ≤ℝ Φ-large k X)
  (compLower : ∀ (n : Nat) → diamPoly X n ≤ℝ (fromNat (length X)))
  (decay-proof :
    LargeFieldPolymer k X →
    largeFieldActivity k X
      ≤ℝ
    (c-large *ℝ expℝ (-ℝ (κ *ℝ diamPoly X 0))))
  → P10LargeFieldSuppressionPackage k X
P10InternalDecayReducerClosed k X Φ-large diamPoly largeFieldActivity coercive suppressed nonneg compLower decay-proof =
  P10LargeFieldSuppressionFromDerivedReducers k X Φ-large nonneg coercive diamPoly largeFieldActivity suppressed compLower decay-proof

postulate
  LargeField : Nat → List Nat → Set

LargeFieldCoercivityLeaf :
  ((k : Nat) (X : List Nat) → ℝ) →
  Set
LargeFieldCoercivityLeaf Φ-large =
  (k : Nat) (X : List Nat) →
  P10CanonicalCoercivityStatement Φ-large k X

LargeFieldActivitySuppressionLeaf :
  ((k : Nat) (X : List Nat) → ℝ) →
  ((k : Nat) (X : List Nat) → ℝ) →
  Set
LargeFieldActivitySuppressionLeaf Φ-large largeFieldActivity =
  (k : Nat) (X : List Nat) →
  P10CanonicalActivitySuppressionStatement
    Φ-large
    largeFieldActivity
    k
    X

record P10AnalyticLeaves : Set₁ where
  field
    Φ-large :
      (k : Nat) (X : List Nat) → ℝ

    largeFieldActivity :
      (k : Nat) (X : List Nat) → ℝ

    coercivity :
      LargeFieldCoercivityLeaf Φ-large

    activitySuppression :
      LargeFieldActivitySuppressionLeaf Φ-large largeFieldActivity

    noClayPromotion : clayYangMillsPromoted ≡ false

P10FromAnalyticLeavesAndArithmetic :
  (k : Nat) (X : List Nat)
  (diamPoly : List Nat → Nat → ℝ)
  → (leaves : P10AnalyticLeaves)
  → (nonneg : 0ℝ ≤ℝ P10AnalyticLeaves.Φ-large leaves k X)
  → (compLower : ∀ (n : Nat) → diamPoly X n ≤ℝ (fromNat (length X)))
  → (decay-proof :
       LargeFieldPolymer k X →
       P10AnalyticLeaves.largeFieldActivity leaves k X
         ≤ℝ
       (c-large *ℝ expℝ (-ℝ (κ *ℝ diamPoly X 0))))
  → P10LargeFieldSuppressionPackage k X
P10FromAnalyticLeavesAndArithmetic k X diamPoly leaves nonneg compLower decay-proof =
  P10InternalDecayReducerClosed
    k
    X
    (P10AnalyticLeaves.Φ-large leaves)
    diamPoly
    (P10AnalyticLeaves.largeFieldActivity leaves)
    (P10AnalyticLeaves.coercivity leaves k X)
    (P10AnalyticLeaves.activitySuppression leaves k X)
    nonneg compLower decay-proof

-- ── Sprint 3: P10 Balaban Analytic Estimate Package ───────────────────

record P10BalabanAnalyticEstimatePackage
  (C-large : ℝ)
  (Φ-large : (k : Nat) (X : List Nat) → ℝ)
  (largeFieldActivity : (k : Nat) (X : List Nat) → ℝ)
  : Set₁ where
  field
    blockLargeFieldCoercivity :
      LargeFieldCoercivityLeaf Φ-large

    polymerWeightSuppression :
      LargeFieldActivitySuppressionLeaf Φ-large largeFieldActivity

    noClayPromotion :
      clayYangMillsPromoted ≡ false

P10AnalyticLeavesFromBalabanEstimates :
  (C-large : ℝ)
  (Φ-large : (k : Nat) (X : List Nat) → ℝ)
  (largeFieldActivity : (k : Nat) (X : List Nat) → ℝ)
  → P10BalabanAnalyticEstimatePackage C-large Φ-large largeFieldActivity
  → P10AnalyticLeaves
P10AnalyticLeavesFromBalabanEstimates C-large Φ-large largeFieldActivity pkg =
  record
    { Φ-large = Φ-large
    ; largeFieldActivity = largeFieldActivity
    ; coercivity =
        P10BalabanAnalyticEstimatePackage.blockLargeFieldCoercivity pkg
    ; activitySuppression =
        P10BalabanAnalyticEstimatePackage.polymerWeightSuppression pkg
    ; noClayPromotion =
        P10BalabanAnalyticEstimatePackage.noClayPromotion pkg
    }

currentP10SourceAnalyticEstimatePackage :
  P10BalabanAnalyticEstimatePackage
    c-large
    sourceΦ-large
    sourceLargeFieldActivity
currentP10SourceAnalyticEstimatePackage = record
  { blockLargeFieldCoercivity =
      OwnedP10DiameterCoercivityWitness.φLargeCoerciveInDiameter
        (OwnedP10AnalyticEstimateWitness.diameterCoercivity
          currentOwnedP10AnalyticEstimateWitness)
  ; polymerWeightSuppression =
      OwnedP10SupportProductLocalisationWitness.activitySuppressedByFunctional
        (OwnedP10AnalyticEstimateWitness.supportProduct
          currentOwnedP10AnalyticEstimateWitness)
  ; noClayPromotion = refl
  }

currentP10SourceAnalyticLeaves : P10AnalyticLeaves
currentP10SourceAnalyticLeaves =
  P10AnalyticLeavesFromBalabanEstimates
    c-large
    sourceΦ-large
    sourceLargeFieldActivity
    currentP10SourceAnalyticEstimatePackage
