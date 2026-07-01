module DASHI.Physics.YangMills.P10BalabanFaithfulnessBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String using (String)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

postulate
  _^ℝ_ : ℝ → ℝ → ℝ

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    to : A → B
    from : B → A

record P10BalabanObjectAdapter (Block Polymer : Set) : Set₁ where
  field
    BalabanΦ-large :
      ℕ → Polymer → ℝ

    BalabanLargeFieldActivity :
      ℕ → Polymer → ℝ

    BalabanBlockPenalty :
      ℕ → Block → ℝ

    BalabanBadBlock :
      ℕ → Polymer → Block → Set

    BalabanSupportBlocks :
      ℕ → Polymer → List Block

    BalabanComplexity :
      Polymer → ℕ

record P10BalabanSourceAnchor : Set₁ where
  field
    sourceName :
      String

    theoremSpan :
      String

    objectDefinitionsSpan :
      String

    normalizationConvention :
      String

    parserReceipt :
      String

    noClayPromotion :
      clayYangMillsPromoted ≡ false

record P10BalabanFaithfulnessBridge
  (Block Polymer : Set)
  (BadBlock : ℕ → Block → Set)
  (P10SupportBlocks : Polymer → List Block)
  (complexity : Polymer → ℕ)
  (Φ-large : ℕ → Polymer → ℝ)
  (largeFieldActivity : ℕ → Polymer → ℝ)
  (blockPenalty : ℕ → Block → ℝ)
  : Set₁ where
  field
    objectAdapter :
      P10BalabanObjectAdapter Block Polymer

    agreesOnFunctional :
      ∀ k X →
      Φ-large k X ≡
      P10BalabanObjectAdapter.BalabanΦ-large objectAdapter k X

    agreesOnActivity :
      ∀ k X →
      largeFieldActivity k X ≡
      P10BalabanObjectAdapter.BalabanLargeFieldActivity objectAdapter k X

    agreesOnBlockPenalty :
      ∀ k b →
      blockPenalty k b ≡
      P10BalabanObjectAdapter.BalabanBlockPenalty objectAdapter k b

    agreesOnBadBlocks :
      ∀ k X b →
      BadBlock k b ↔
      P10BalabanObjectAdapter.BalabanBadBlock objectAdapter k X b

    agreesOnSupportBlocks :
      ∀ k X →
      P10SupportBlocks X ≡
      P10BalabanObjectAdapter.BalabanSupportBlocks objectAdapter k X

    agreesOnComplexity :
      ∀ X →
      complexity X ≡
      P10BalabanObjectAdapter.BalabanComplexity objectAdapter X

data SourceBackedFaithfulnessCandidate : Set where
  sourceBackedFaithfulnessCandidate : SourceBackedFaithfulnessCandidate

record P10BalabanFaithfulnessReceipt
  (Block Polymer : Set)
  (BadBlock : ℕ → Block → Set)
  (P10SupportBlocks : Polymer → List Block)
  (complexity : Polymer → ℕ)
  (Φ-large : ℕ → Polymer → ℝ)
  (largeFieldActivity : ℕ → Polymer → ℝ)
  (blockPenalty : ℕ → Block → ℝ)
  : Set₁ where
  field
    anchor :
      P10BalabanSourceAnchor

    bridge :
      P10BalabanFaithfulnessBridge
        Block
        Polymer
        BadBlock
        P10SupportBlocks
        complexity
        Φ-large
        largeFieldActivity
        blockPenalty

    status :
      SourceBackedFaithfulnessCandidate

    noClayPromotion :
      clayYangMillsPromoted ≡ false

record P10BadBlockWeightSuppressionKernel
  (Block : Set)
  (BadBlock : ℕ → Block → Set)
  (blockWeight : ℕ → Block → ℝ)
  (localGaussianTailWeight : ℕ → Block → ℝ)
  (tailSize : ℕ → Block → ℝ)
  (tailThreshold : ℝ)
  (decayBase : ℝ)
  (blockPenalty : ℕ → Block → ℝ)
  : Set₁ where
  field
    blockWeightDefinition :
      ∀ k b →
      blockWeight k b ≡ localGaussianTailWeight k b

    badBlockGivesTailLowerBound :
      ∀ k b →
      BadBlock k b →
      tailThreshold ≤ℝ tailSize k b

    gaussianTailSuppression :
      ∀ k b →
      tailThreshold ≤ℝ tailSize k b →
      localGaussianTailWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b

P10BadBlockWeightSuppressionFromKernel :
  ∀
    {Block : Set}
    {BadBlock : ℕ → Block → Set}
    {blockWeight : ℕ → Block → ℝ}
    {localGaussianTailWeight : ℕ → Block → ℝ}
    {tailSize : ℕ → Block → ℝ}
    {tailThreshold : ℝ}
    {decayBase : ℝ}
    {blockPenalty : ℕ → Block → ℝ} →
  P10BadBlockWeightSuppressionKernel
    Block
    BadBlock
    blockWeight
    localGaussianTailWeight
    tailSize
    tailThreshold
    decayBase
    blockPenalty
  → ∀ k b →
      BadBlock k b →
      blockWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b
P10BadBlockWeightSuppressionFromKernel kernel k b bad
  rewrite
    P10BadBlockWeightSuppressionKernel.blockWeightDefinition kernel k b
  =
    P10BadBlockWeightSuppressionKernel.gaussianTailSuppression
      kernel
      k
      b
      (P10BadBlockWeightSuppressionKernel.badBlockGivesTailLowerBound
        kernel
        k
        b
        bad)

record P10BalabanAnalyticDischarge
  (Block Polymer : Set)
  (BadBlock : ℕ → Block → Set)
  (P10SupportBlocks : Polymer → List Block)
  (complexity : Polymer → ℕ)
  (Φ-large : ℕ → Polymer → ℝ)
  (largeFieldActivity : ℕ → Polymer → ℝ)
  (blockPenalty : ℕ → Block → ℝ)
  (blockWeight : ℕ → Block → ℝ)
  (localGaussianTailWeight : ℕ → Block → ℝ)
  (tailSize : ℕ → Block → ℝ)
  (tailThreshold : ℝ)
  (decayBase : ℝ)
  : Set₁ where
  field
    faithfulnessReceipt :
      P10BalabanFaithfulnessReceipt
        Block
        Polymer
        BadBlock
        P10SupportBlocks
        complexity
        Φ-large
        largeFieldActivity
        blockPenalty

    badBlockWeightSuppressionKernel :
      P10BadBlockWeightSuppressionKernel
        Block
        BadBlock
        blockWeight
        localGaussianTailWeight
        tailSize
        tailThreshold
        decayBase
        blockPenalty

    noClayPromotion :
      clayYangMillsPromoted ≡ false
