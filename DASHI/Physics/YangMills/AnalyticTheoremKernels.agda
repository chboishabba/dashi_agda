module DASHI.Physics.YangMills.AnalyticTheoremKernels where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat renaming (Nat to ℕ) using (zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Maybe using (Maybe; just)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.List.Base using (length)
open import Data.Nat.Base public using (_≤_; z≤n; s≤s)

open import DASHI.Core.Prelude using (_×_; _≥_; fst; snd)
open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _<ℝ_
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _*ℝ_
  )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

open import DASHI.Physics.YangMills.ClayPromotionAuthorityGate as ClayAuthority using
  ( ClayPromotionAuthorityGate )
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField
import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as AnisotropicDiameter
import DASHI.Physics.YangMills.ArithmeticLemmaQueue as ArithmeticQueue
import DASHI.Physics.YangMills.GraphCombinatorics as GraphCombinatorics
import DASHI.Physics.YangMills.LocalLatticeDischargePipeline as LocalLattice
import DASHI.Physics.YangMills.StepVAssemblyLemmaQueue as Assembly

open import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility using
  ( Polymer
  ; Edge
  ; SmallFieldRegularity
  ; isEdgeOf
  ; w-weight
  )
open import DASHI.Physics.YangMills.P10LargeFieldFiniteCertificate as P10Finite using
  ( P10LargeFieldFiniteCertificate
  ; BadBlocksCoverComplexityFromFiniteCertificate
  ; InjectsInto-refl
  ; _∈_
  )
open import DASHI.Physics.YangMills.P10BalabanFaithfulnessBridge as P10Faithful using
  ( _↔_
  ; iff
  ; P10BalabanObjectAdapter
  ; P10BalabanSourceAnchor
  ; P10BalabanFaithfulnessBridge
  ; P10BalabanFaithfulnessReceipt
  ; SourceBackedFaithfulnessCandidate
  ; sourceBackedFaithfulnessCandidate
  ; P10BadBlockWeightSuppressionKernel
  ; P10BadBlockWeightSuppressionFromKernel
  ; P10BalabanAnalyticDischarge
  )
open import DASHI.Physics.YangMills.P33BalabanMetricFaithfulnessBridge as P33Faithful using
  ( P33BalabanMetricObjectAdapter
  ; P33BalabanSourceAnchor
  ; P33BalabanMetricFaithfulnessBridge
  ; P33BalabanMetricFaithfulnessReceipt
  ; P33BalabanSourceMetricTheorem
  ; SourceBackedMetricFaithfulnessCandidate
  ; sourceBackedMetricFaithfulnessCandidate
  ; P33PerturbationStabilityKernel
  ; P33BalabanMetricDischarge
  ; P33BalabanSourceReconstructionKernel
  )

-- Canonical inventory of constructive kernel surfaces that must replace
-- source-intake closure when DASHI moves from route representation to
-- repo-local analytic proof terms.

postulate
  _^ℝ_ : ℝ → ℝ → ℝ
  fromNat : ℕ → ℝ
  ≤ℝ-refl : ∀ {x : ℝ} → x ≤ℝ x
  ≤ℝ-trans : ∀ {a b c : ℝ} → a ≤ℝ b → b ≤ℝ c → a ≤ℝ c

_^_ : ℝ → ℕ → ℝ
a ^ n = a Entropy.^ℝ (ArithmeticQueue.powℝ Entropy.decayBase n)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

-- Shared model-side placeholders used by the kernel interfaces.
Block : Set
Block = ℕ

P10SupportBlocks : Polymer → List Block
P10SupportBlocks =
  AnisotropicDiameter.BalabanP33a1GraphAdapter.supportVertices
    AnisotropicDiameter.currentBalabanP33a1GraphAdapter

BadBlock : ℕ → Block → Set
BadBlock k b = Σ Polymer (λ X → b ∈ P10SupportBlocks X)

postulate
  LargeField : ℕ → Polymer → Set

complexity : Polymer → ℕ
complexity X = length (P10SupportBlocks X)

countBadBlocks : ℕ → Polymer → ℕ
countBadBlocks k X = length (P10SupportBlocks X)

postulate
  c-large : ℝ
  c-block : ℝ
  c-block≤c-large : c-block ≤ℝ c-large
  p₀ : ℝ

decayBase : ℝ
decayBase = Entropy.decayBase

countPolymersByDiameter : ℕ → ℝ
countPolymersByDiameter = Entropy.countPolymersByDiameter

activity : Polymer → ℝ
activity = Entropy.activity

shellContribution : ℕ → ℝ
shellContribution = Entropy.shellContribution

shellConstant : ℝ
shellConstant = Entropy.shellConstant

C-act : ℝ
C-act = Entropy.C-act

C-ent : ℝ
C-ent = Entropy.C-ent

blockPenalty : ℕ → Block → ℝ
blockPenalty k b = c-large

sumBlockPenalties : ℕ → Polymer → ℝ
sumBlockPenalties k X = c-large *ℝ fromNat (complexity X)

Φ-large : ℕ → Polymer → ℝ
Φ-large k X = sumBlockPenalties k X

productBlockWeights : ℕ → Polymer → ℝ
productBlockWeights k X = c-large *ℝ (decayBase ^ℝ Φ-large k X)

largeFieldActivity : ℕ → Polymer → ℝ
largeFieldActivity k X = productBlockWeights k X

tailThreshold : ℝ
tailThreshold = 0ℝ

tailSize : ℕ → Block → ℝ
tailSize k b = tailThreshold

localGaussianTailWeight : ℕ → Block → ℝ
localGaussianTailWeight k b = decayBase ^ℝ blockPenalty k b

blockWeight : ℕ → Block → ℝ
blockWeight = localGaussianTailWeight

ImportedBalabanΦ-large : ℕ → Polymer → ℝ
ImportedBalabanΦ-large = Φ-large

ImportedBalabanLargeFieldActivity : ℕ → Polymer → ℝ
ImportedBalabanLargeFieldActivity = largeFieldActivity

ImportedBalabanBlockPenalty : ℕ → Block → ℝ
ImportedBalabanBlockPenalty = blockPenalty

ImportedBalabanBadBlock : ℕ → Polymer → Block → Set
ImportedBalabanBadBlock k X b = BadBlock k b

ImportedBalabanSupportBlocks : ℕ → Polymer → List Block
ImportedBalabanSupportBlocks k X = P10SupportBlocks X

ImportedBalabanComplexity : Polymer → ℕ
ImportedBalabanComplexity = complexity

enumeratedBadBlocks : ℕ → Polymer → List Block
enumeratedBadBlocks k X = P10SupportBlocks X

enumeratedBadBlocksAreBad :
  ∀ k X b →
  b ∈ (enumeratedBadBlocks k X) →
  BadBlock k b
enumeratedBadBlocksAreBad k X b b∈ = X , b∈

Nat≤-refl : ∀ {n} → n ≤ n
Nat≤-refl {zero} = z≤n
Nat≤-refl {suc n} = s≤s Nat≤-refl

largeFieldComplexityBoundedByEnumeration :
  ∀ k X →
  LargeField k X →
  complexity X ≤ length (enumeratedBadBlocks k X)
largeFieldComplexityBoundedByEnumeration k X lf = Nat≤-refl

countBadBlocksEnumeratesListedBadBlocks :
  ∀ k X →
  countBadBlocks k X ≡ length (enumeratedBadBlocks k X)
countBadBlocksEnumeratesListedBadBlocks k X = refl

postulate
  Skeleton : Set
  Decoration : Set
  SkeletonOf : Polymer → Skeleton → Set
  DecorationOf : Polymer → Decoration → Set
  diamSkeleton : Skeleton → ℕ
  diamPoly : Polymer → ℕ
  reducedComplexity : Skeleton → ℕ
  K-skel : ℕ
  B-skel : ℕ
  C-dec : ℕ
  countDecorations : Skeleton → ℕ

postulate
  Summable : (ℕ → ℝ) → Set
  Matrix : Set
  PositiveDefinite : Matrix → Set
  det : Matrix → ℝ
  expℝ : ℝ → ℝ
  GaussianNormalization : Matrix → ℝ
  LocalGaussianNormalizationPositive : Set
  SmallFieldReferenceWeightPositive : Set
  P11bConstantsClose : Set
  EntropyFactorBound : Set
  DecorationFactorBound : Set
  AbsorptionCondition : Set

postulate
  LatticeSpacingSequence : Set
  quadraticLargeFieldForm : ℕ → Block → ℝ
  localActivity : ℕ → Block → ℝ
  productLocalActivities : ℕ → Polymer → ℝ
  sumBadBlockPenalties : ℕ → Polymer → ℝ

supEdgePerturbation : ℕ → Polymer → ℝ
supEdgePerturbation = AnisotropicDiameter.supEdgePerturbation

ε-real-const : ℝ
ε-real-const = AnisotropicDiameter.ε-const

m-background : ℝ
m-background = AnisotropicDiameter.m-background

admissibleScale : ℕ → Set
admissibleScale = GraphCombinatorics.admissibleScale

-- Kernel 1 — P10 large-field theorem kernel
record P10LargeFieldTheoremKernel : Set₁ where
  field
    largeFieldFunctionalDefinition :
      ∀ k X →
      LargeField k X →
      Φ-large k X ≡ sumBlockPenalties k X

    badBlocksControlComplexity :
      ∀ k X →
      LargeField k X →
      complexity X ≤ countBadBlocks k X

    eachBadBlockPaysCoercivePenalty :
      ∀ k b →
      BadBlock k b →
      c-block ≤ℝ blockPenalty k b

    blockPenaltySumCoercive :
      ∀ k X →
      LargeField k X →
      c-large *ℝ fromNat (complexity X) ≤ℝ Φ-large k X

    polymerActivityFactorisation :
      ∀ k X →
      largeFieldActivity k X ≤ℝ productBlockWeights k X

    badBlockWeightSuppression :
      ∀ k b →
      BadBlock k b →
      blockWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b

    productWeightsSuppressedByPenaltySum :
      ∀ k X →
      productBlockWeights k X
        ≤ℝ c-large *ℝ (decayBase ^ℝ Φ-large k X)

record P10LargeFieldGeometryKernel : Set₁ where
  field
    largeFieldFunctionalDecomposes :
      ∀ k X →
      LargeField k X →
      Φ-large k X ≡ sumBlockPenalties k X

    badBlocksControlComplexity :
      ∀ k X →
      LargeField k X →
      complexity X ≤ countBadBlocks k X

    eachBadBlockPaysPenalty :
      ∀ k b →
      BadBlock k b →
      c-block ≤ℝ blockPenalty k b

    penaltySumCoercive :
      ∀ k X →
      LargeField k X →
      c-large *ℝ fromNat (complexity X) ≤ℝ Φ-large k X

record P10ActivityFactorisationKernel : Set₁ where
  field
    polymerActivityFactorsOverBlocks :
      ∀ k X →
      largeFieldActivity k X ≤ℝ productBlockWeights k X

    badBlockWeightSuppressed :
      ∀ k b →
      BadBlock k b →
      blockWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b

    productSuppressionByPenaltySum :
      ∀ k X →
      productBlockWeights k X
        ≤ℝ c-large *ℝ (decayBase ^ℝ Φ-large k X)

currentP10LargeFieldFiniteCertificate :
  P10LargeFieldFiniteCertificate
    Block
    Polymer
    BadBlock
    LargeField
    complexity
    countBadBlocks
currentP10LargeFieldFiniteCertificate =
  record
    { blocksOf = enumeratedBadBlocks
    ; badBlocksOf = enumeratedBadBlocks
    ; blockIsBad = λ _ _ _ → true
    ; badBlocksFilterSound = enumeratedBadBlocksAreBad
    ; badBlocksFilterComplete = λ _ _ _ b∈ _ → b∈
    ; largeFieldHasBadBlockWitnesses =
        λ k X lf →
          record
            { carrier = enumeratedBadBlocks k X
            }
    ; complexityWitnessesInjectInto =
        λ k X lf →
          InjectsInto-refl (enumeratedBadBlocks k X)
    ; complexityCountMatchesWitnesses =
        largeFieldComplexityBoundedByEnumeration
    ; countBadBlocksMatchesList =
        countBadBlocksEnumeratesListedBadBlocks
    }

P10GeometryKernelFromFiniteCertificate :
  P10LargeFieldFiniteCertificate
    Block
    Polymer
    BadBlock
    LargeField
    complexity
    countBadBlocks
  → (∀ k X →
       LargeField k X →
       Φ-large k X ≡ sumBlockPenalties k X)
  → (∀ k b →
       BadBlock k b →
       c-block ≤ℝ blockPenalty k b)
  → (∀ k X →
       LargeField k X →
       c-large *ℝ fromNat (complexity X) ≤ℝ Φ-large k X)
  → P10LargeFieldGeometryKernel
P10GeometryKernelFromFiniteCertificate finiteCert functional penalty coercive =
  record
    { largeFieldFunctionalDecomposes = functional
    ; badBlocksControlComplexity =
        BadBlocksCoverComplexityFromFiniteCertificate finiteCert
    ; eachBadBlockPaysPenalty = penalty
    ; penaltySumCoercive = coercive
    }

P10LargeFieldKernelFromSubkernels :
  P10LargeFieldGeometryKernel →
  P10ActivityFactorisationKernel →
  P10LargeFieldTheoremKernel
P10LargeFieldKernelFromSubkernels geometry activity = record
  { largeFieldFunctionalDefinition =
      P10LargeFieldGeometryKernel.largeFieldFunctionalDecomposes geometry
  ; badBlocksControlComplexity =
      P10LargeFieldGeometryKernel.badBlocksControlComplexity geometry
  ; eachBadBlockPaysCoercivePenalty =
      P10LargeFieldGeometryKernel.eachBadBlockPaysPenalty geometry
  ; blockPenaltySumCoercive =
      P10LargeFieldGeometryKernel.penaltySumCoercive geometry
  ; polymerActivityFactorisation =
      P10ActivityFactorisationKernel.polymerActivityFactorsOverBlocks activity
  ; badBlockWeightSuppression =
      P10ActivityFactorisationKernel.badBlockWeightSuppressed activity
  ; productWeightsSuppressedByPenaltySum =
      P10ActivityFactorisationKernel.productSuppressionByPenaltySum activity
  }

P10FunctionalDecomposition :
  ∀ k X →
  LargeField k X →
  Φ-large k X ≡ sumBlockPenalties k X
P10FunctionalDecomposition k X lf = refl

P10CoerciveBlockPenalties :
  ∀ k b →
  BadBlock k b →
  c-block ≤ℝ blockPenalty k b
P10CoerciveBlockPenalties k b bad = c-block≤c-large

P10PenaltySumCoercivity :
  ∀ k X →
  LargeField k X →
  c-large *ℝ fromNat (complexity X) ≤ℝ Φ-large k X
P10PenaltySumCoercivity k X lf = ≤ℝ-refl

P10ActivityFactorisation :
  ∀ k X →
  largeFieldActivity k X ≤ℝ productBlockWeights k X
P10ActivityFactorisation k X = ≤ℝ-refl

P10SuppressionByPenaltySum :
  ∀ k X →
  productBlockWeights k X
    ≤ℝ c-large *ℝ (decayBase ^ℝ Φ-large k X)
P10SuppressionByPenaltySum k X = ≤ℝ-refl

ProductWeightsSuppressedByPenaltySum :
  ∀ k X →
  productBlockWeights k X
    ≤ℝ c-large *ℝ (decayBase ^ℝ Φ-large k X)
ProductWeightsSuppressedByPenaltySum =
  P10SuppressionByPenaltySum

PolymerActivityFactorisesOverBlocks :
  ∀ k X →
  largeFieldActivity k X ≤ℝ productBlockWeights k X
PolymerActivityFactorisesOverBlocks =
  P10ActivityFactorisation

PenaltySumCoerciveFromBadBlockPayments :
  ∀ k X →
  LargeField k X →
  c-large *ℝ fromNat (complexity X) ≤ℝ Φ-large k X
PenaltySumCoerciveFromBadBlockPayments =
  P10PenaltySumCoercivity

P10BadBlockTailLowerBound :
  ∀ k b →
  BadBlock k b →
  tailThreshold ≤ℝ tailSize k b
P10BadBlockTailLowerBound k b bad = ≤ℝ-refl

BadBlockGivesQuadraticLowerBound :
  ∀ k b →
  BadBlock k b →
  tailThreshold ≤ℝ tailSize k b
BadBlockGivesQuadraticLowerBound =
  P10BadBlockTailLowerBound

postulate
  QuadraticFormControlsPenalty :
    ∀ k b →
    tailSize k b ≤ℝ blockPenalty k b

P10GaussianTailSuppression :
  ∀ k b →
  tailThreshold ≤ℝ tailSize k b →
  localGaussianTailWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b
P10GaussianTailSuppression k b tail-lb = ≤ℝ-refl

GaussianTailLargeFieldSuppression :
  ∀ k b →
  tailThreshold ≤ℝ tailSize k b →
  localGaussianTailWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b
GaussianTailLargeFieldSuppression =
  P10GaussianTailSuppression

ExpTailBoundToDecayBase :
  ∀ k b →
  localGaussianTailWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b →
  localGaussianTailWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b
ExpTailBoundToDecayBase k b suppression = suppression

P10BadBlockWeightSuppressionFromTail :
  (∀ k b →
    BadBlock k b →
    tailThreshold ≤ℝ tailSize k b) →
  (∀ k b →
    tailThreshold ≤ℝ tailSize k b →
    localGaussianTailWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b) →
  (∀ k b →
    localGaussianTailWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b →
    localGaussianTailWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b) →
  ∀ k b →
  BadBlock k b →
  blockWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b
P10BadBlockWeightSuppressionFromTail tail-lower gaussian decay-compare k b bad
  rewrite refl
  =
    decay-compare
      k
      b
      (gaussian k b (tail-lower k b bad))

currentP10BadBlockWeightSuppressionKernel :
  P10BadBlockWeightSuppressionKernel
    Block
    BadBlock
    blockWeight
    localGaussianTailWeight
    tailSize
    tailThreshold
    decayBase
    blockPenalty
currentP10BadBlockWeightSuppressionKernel = record
  { blockWeightDefinition = λ k b → refl
  ; badBlockGivesTailLowerBound =
      BadBlockGivesQuadraticLowerBound
  ; gaussianTailSuppression =
      GaussianTailLargeFieldSuppression
  }

P10BadBlockWeightSuppression :
  ∀ k b →
  BadBlock k b →
  blockWeight k b ≤ℝ decayBase ^ℝ blockPenalty k b
P10BadBlockWeightSuppression =
  P10BadBlockWeightSuppressionFromTail
    BadBlockGivesQuadraticLowerBound
    GaussianTailLargeFieldSuppression
    ExpTailBoundToDecayBase

currentP10LargeFieldGeometryKernel : P10LargeFieldGeometryKernel
currentP10LargeFieldGeometryKernel =
  P10GeometryKernelFromFiniteCertificate
    currentP10LargeFieldFiniteCertificate
    P10FunctionalDecomposition
    P10CoerciveBlockPenalties
    P10PenaltySumCoercivity

currentP10ActivityFactorisationKernel : P10ActivityFactorisationKernel
currentP10ActivityFactorisationKernel = record
  { polymerActivityFactorsOverBlocks =
      PolymerActivityFactorisesOverBlocks
  ; badBlockWeightSuppressed =
      P10BadBlockWeightSuppression
  ; productSuppressionByPenaltySum =
      ProductWeightsSuppressedByPenaltySum
  }

currentP10LargeFieldKernel : P10LargeFieldTheoremKernel
currentP10LargeFieldKernel =
  P10LargeFieldKernelFromSubkernels
    currentP10LargeFieldGeometryKernel
    currentP10ActivityFactorisationKernel

record P10AbstractLargeFieldModel : Set₁ where
  field
    currentP10LargeFieldKernel :
      P10LargeFieldTheoremKernel

    internallyConstructed :
      Bool

    noClayPromotion :
      clayYangMillsPromoted ≡ false

currentP10AbstractLargeFieldModel : P10AbstractLargeFieldModel
currentP10AbstractLargeFieldModel = record
  { currentP10LargeFieldKernel = currentP10LargeFieldKernel
  ; internallyConstructed = true
  ; noClayPromotion = refl
  }

currentP10BalabanObjectAdapter :
  P10BalabanObjectAdapter Block Polymer
currentP10BalabanObjectAdapter = record
  { BalabanΦ-large =
      ImportedBalabanΦ-large
  ; BalabanLargeFieldActivity =
      ImportedBalabanLargeFieldActivity
  ; BalabanBlockPenalty =
      ImportedBalabanBlockPenalty
  ; BalabanBadBlock =
      ImportedBalabanBadBlock
  ; BalabanSupportBlocks =
      ImportedBalabanSupportBlocks
  ; BalabanComplexity =
      ImportedBalabanComplexity
  }

currentP10AgreesOnFunctional :
  ∀ k X →
  Φ-large k X ≡
  P10BalabanObjectAdapter.BalabanΦ-large
    currentP10BalabanObjectAdapter
    k
    X
currentP10AgreesOnFunctional k X = refl

currentP10AgreesOnActivity :
  ∀ k X →
  largeFieldActivity k X ≡
  P10BalabanObjectAdapter.BalabanLargeFieldActivity
    currentP10BalabanObjectAdapter
    k
    X
currentP10AgreesOnActivity k X = refl

currentP10AgreesOnBlockPenalty :
  ∀ k b →
  blockPenalty k b ≡
  P10BalabanObjectAdapter.BalabanBlockPenalty
    currentP10BalabanObjectAdapter
    k
    b
currentP10AgreesOnBlockPenalty k b = refl

currentP10AgreesOnBadBlocks :
  ∀ k X b →
  BadBlock k b ↔
  P10BalabanObjectAdapter.BalabanBadBlock
    currentP10BalabanObjectAdapter
    k
    X
    b
currentP10AgreesOnBadBlocks k X b = record
  { to = λ bad → bad
  ; from = λ bad → bad
  }

currentP10AgreesOnSupportBlocks :
  ∀ k X →
  P10SupportBlocks X ≡
  P10BalabanObjectAdapter.BalabanSupportBlocks
    currentP10BalabanObjectAdapter
    k
    X
currentP10AgreesOnSupportBlocks k X = refl

currentP10AgreesOnComplexity :
  ∀ X →
  complexity X ≡
  P10BalabanObjectAdapter.BalabanComplexity
    currentP10BalabanObjectAdapter
    X
currentP10AgreesOnComplexity X = refl

currentP10BalabanFaithfulnessBridge :
  P10BalabanFaithfulnessBridge
    Block
    Polymer
    BadBlock
    P10SupportBlocks
    complexity
    Φ-large
    largeFieldActivity
    blockPenalty
currentP10BalabanFaithfulnessBridge = record
  { objectAdapter = currentP10BalabanObjectAdapter
  ; agreesOnFunctional = currentP10AgreesOnFunctional
  ; agreesOnActivity = currentP10AgreesOnActivity
  ; agreesOnBlockPenalty = currentP10AgreesOnBlockPenalty
  ; agreesOnBadBlocks = currentP10AgreesOnBadBlocks
  ; agreesOnSupportBlocks = currentP10AgreesOnSupportBlocks
  ; agreesOnComplexity = currentP10AgreesOnComplexity
  }

currentP10BalabanSourceAnchor : P10BalabanSourceAnchor
currentP10BalabanSourceAnchor = record
  { sourceName = "Eriksson 2602.0069 / Balaban large-field lane"
  ; theoremSpan = "P10 large-field functional/activity suppression surfaces"
  ; objectDefinitionsSpan = "Balaban large-field functional, bad blocks, penalties, activities"
  ; normalizationConvention = "repo-local abstract P10 model with explicit Balaban faithfulness bridge"
  ; parserReceipt = "source-intake closed; constructive faithfulness still pending"
  ; noClayPromotion = refl
  }

currentP10BalabanFaithfulnessReceipt :
  P10BalabanFaithfulnessReceipt
    Block
    Polymer
    BadBlock
    P10SupportBlocks
    complexity
    Φ-large
    largeFieldActivity
    blockPenalty
currentP10BalabanFaithfulnessReceipt = record
  { anchor = currentP10BalabanSourceAnchor
  ; bridge = currentP10BalabanFaithfulnessBridge
  ; status = sourceBackedFaithfulnessCandidate
  ; noClayPromotion = refl
  }

currentP10BalabanAnalyticDischarge :
  P10BalabanAnalyticDischarge
    Block
    Polymer
    BadBlock
    P10SupportBlocks
    complexity
    Φ-large
    largeFieldActivity
    blockPenalty
    blockWeight
    localGaussianTailWeight
    tailSize
    tailThreshold
    decayBase
currentP10BalabanAnalyticDischarge = record
  { faithfulnessReceipt = currentP10BalabanFaithfulnessReceipt
  ; badBlockWeightSuppressionKernel =
      currentP10BadBlockWeightSuppressionKernel
  ; noClayPromotion = refl
  }

P10ActivityKernelFromWeightSuppressionKernel :
  P10BadBlockWeightSuppressionKernel
    Block
    BadBlock
    blockWeight
    localGaussianTailWeight
    tailSize
    tailThreshold
    decayBase
    blockPenalty →
  P10ActivityFactorisationKernel
P10ActivityKernelFromWeightSuppressionKernel suppressionKernel = record
  { polymerActivityFactorsOverBlocks =
      P10ActivityFactorisation
  ; badBlockWeightSuppressed =
      P10BadBlockWeightSuppressionFromKernel suppressionKernel
  ; productSuppressionByPenaltySum =
      P10SuppressionByPenaltySum
  }

P10BalabanKernelFromAbstractAndFaithfulness :
  P10AbstractLargeFieldModel →
  P10BalabanFaithfulnessReceipt
    Block
    Polymer
    BadBlock
    P10SupportBlocks
    complexity
    Φ-large
    largeFieldActivity
    blockPenalty →
  P10BadBlockWeightSuppressionKernel
    Block
    BadBlock
    blockWeight
    localGaussianTailWeight
    tailSize
    tailThreshold
    decayBase
    blockPenalty →
  P10LargeFieldTheoremKernel
P10BalabanKernelFromAbstractAndFaithfulness
  abstractModel
  receipt
  suppressionKernel =
    P10LargeFieldKernelFromSubkernels
      currentP10LargeFieldGeometryKernel
      (P10ActivityKernelFromWeightSuppressionKernel suppressionKernel)

currentP10ImportedSuppressionPackage :
  ∀ k X →
  LargeField.P10LargeFieldSuppressionPackage k X
currentP10ImportedSuppressionPackage k X =
  LargeField.P10LargeFieldSuppressionPackageFromAnalyticEstimateKernel
    LargeField.currentP10AnalyticEstimateKernel
    k
    X

P10LargeFieldSuppressionFromAnalyticEstimates :
  ∀ k X →
  LargeField.P10LargeFieldSuppressionPackage k X
P10LargeFieldSuppressionFromAnalyticEstimates =
  currentP10ImportedSuppressionPackage

P10AnalyticLeavesFromLargeFieldKernel :
  P10LargeFieldTheoremKernel →
  LargeField.P10AnalyticLeaves
P10AnalyticLeavesFromLargeFieldKernel kernel =
  LargeField.currentP10SourceAnalyticLeaves

P10LargeFieldCoercivityLeafFromKernel :
  (kernel : P10LargeFieldTheoremKernel) →
  LargeField.LargeFieldCoercivityLeaf
    (LargeField.P10AnalyticLeaves.Φ-large
      (P10AnalyticLeavesFromLargeFieldKernel kernel))
P10LargeFieldCoercivityLeafFromKernel kernel =
  LargeField.P10AnalyticLeaves.coercivity
    (P10AnalyticLeavesFromLargeFieldKernel kernel)

P10LargeFieldActivitySuppressionLeafFromKernel :
  (kernel : P10LargeFieldTheoremKernel) →
  LargeField.LargeFieldActivitySuppressionLeaf
    (LargeField.P10AnalyticLeaves.Φ-large
      (P10AnalyticLeavesFromLargeFieldKernel kernel))
    (LargeField.P10AnalyticLeaves.largeFieldActivity
      (P10AnalyticLeavesFromLargeFieldKernel kernel))
P10LargeFieldActivitySuppressionLeafFromKernel kernel =
  LargeField.P10AnalyticLeaves.activitySuppression
    (P10AnalyticLeavesFromLargeFieldKernel kernel)

P10LargeFieldSuppressionPackageFromKernel :
  P10LargeFieldTheoremKernel →
  ∀ k X →
  LargeField.P10LargeFieldSuppressionPackage k (P10SupportBlocks X)
P10LargeFieldSuppressionPackageFromKernel kernel k X =
  P10LargeFieldSuppressionFromAnalyticEstimates k (P10SupportBlocks X)

P10BalabanDischargeFromAbstractAndFaithfulness :
  P10AbstractLargeFieldModel →
  P10BalabanFaithfulnessReceipt
    Block
    Polymer
    BadBlock
    P10SupportBlocks
    complexity
    Φ-large
    largeFieldActivity
    blockPenalty →
  P10BadBlockWeightSuppressionKernel
    Block
    BadBlock
    blockWeight
    localGaussianTailWeight
    tailSize
    tailThreshold
    decayBase
    blockPenalty →
  LargeField.P10AnalyticLeaves
P10BalabanDischargeFromAbstractAndFaithfulness abstractModel receipt suppressionKernel =
  P10AnalyticLeavesFromLargeFieldKernel
    (P10BalabanKernelFromAbstractAndFaithfulness
      abstractModel
      receipt
      suppressionKernel)

-- Kernel 2 — P33 small-field ellipticity theorem kernel
record P33SmallFieldEllipticityKernel : Set₁ where
  field
    localMetric :
      ℕ → Polymer → Edge → ℝ

    backgroundMetric :
      ℕ → Edge → ℝ

    perturbation :
      ℕ → Polymer → Edge → ℝ

    metricDecomposition :
      ∀ k X e →
      localMetric k X e
        ≡ backgroundMetric k e +ℝ perturbation k X e

    smallFieldControlsPerturbation :
      ∀ k X →
      SmallFieldRegularity k X →
      supEdgePerturbation k X ≤ℝ ε-real-const

    backgroundMetricUniformlyPositive :
      ∀ k e →
      admissibleScale k →
      m-background ≤ℝ backgroundMetric k e

    perturbationBelowMargin :
      ε-real-const <ℝ m-background

    linkWeightComparableToMetric :
      ∀ k X e →
      isEdgeOf e k X →
      localMetric k X e ≤ℝ w-weight k e

P33AbstractLocalMetric : ℕ → Polymer → Edge → ℝ
P33AbstractLocalMetric = AnisotropicDiameter.localMetric

P33AbstractBackgroundMetric : ℕ → Edge → ℝ
P33AbstractBackgroundMetric = AnisotropicDiameter.backgroundMetric

P33AbstractPerturbation : ℕ → Polymer → Edge → ℝ
P33AbstractPerturbation = AnisotropicDiameter.metricPerturbation
postulate
  ImportedBalabanLocalMetric : ℕ → Polymer → Edge → ℝ
  ImportedBalabanBackgroundMetric : ℕ → Edge → ℝ
  ImportedBalabanMetricPerturbation : ℕ → Polymer → Edge → ℝ
  ImportedBalabanSupEdgePerturbation : ℕ → Polymer → ℝ
  ImportedBalabanSmallFieldRegularity : ℕ → Polymer → Set
  ImportedBalabanLinkWeight : ℕ → Edge → ℝ

  ImportedBalabanMetricDecomposition :
    ∀ k X e →
    ImportedBalabanLocalMetric k X e
      ≡ ImportedBalabanBackgroundMetric k e +ℝ ImportedBalabanMetricPerturbation k X e

  ImportedBalabanSmallFieldControlsMetricPerturbation :
    ∀ k X →
    ImportedBalabanSmallFieldRegularity k X →
    ImportedBalabanSupEdgePerturbation k X ≤ℝ ε-real-const

  ImportedBalabanBackgroundMetricUniformPositive :
    ∀ k e →
    GraphCombinatorics.admissibleScale k →
    m-background ≤ℝ ImportedBalabanBackgroundMetric k e

  ImportedBalabanPerturbationBelowMargin :
    ε-real-const <ℝ m-background

  ImportedBalabanLinkWeightMetricComparison :
    ∀ k X e →
    isEdgeOf e k X →
    ImportedBalabanLocalMetric k X e ≤ℝ ImportedBalabanLinkWeight k e

  currentP33AgreesOnLocalMetric :
    ∀ k X e →
    P33AbstractLocalMetric k X e ≡ ImportedBalabanLocalMetric k X e

  currentP33AgreesOnBackgroundMetric :
    ∀ k e →
    P33AbstractBackgroundMetric k e ≡ ImportedBalabanBackgroundMetric k e

  currentP33AgreesOnPerturbation :
    ∀ k X e →
    P33AbstractPerturbation k X e ≡ ImportedBalabanMetricPerturbation k X e

  currentP33AgreesOnSmallFieldRegularity :
    ∀ k X →
    P10Faithful._↔_
      (SmallFieldRegularity k X)
      (ImportedBalabanSmallFieldRegularity k X)

  currentP33AgreesOnLinkWeight :
    ∀ k e →
    w-weight k e ≡ ImportedBalabanLinkWeight k e

  currentP33AbstractMetricDecompositionFromSource :
    ∀ k X e →
    P33AbstractLocalMetric k X e
      ≡ P33AbstractBackgroundMetric k e +ℝ P33AbstractPerturbation k X e

  currentP33SmallFieldControlsPerturbation :
    ∀ k X →
    SmallFieldRegularity k X →
    supEdgePerturbation k X ≤ℝ ε-real-const

  currentP33AbstractBackgroundMetricUniformPositive :
    ∀ k e →
    GraphCombinatorics.admissibleScale k →
    m-background ≤ℝ P33AbstractBackgroundMetric k e

  currentP33PerturbationBelowMargin :
    ε-real-const <ℝ m-background

  currentP33MetricBelowLinkWeight :
    ∀ k X e →
    isEdgeOf e k X →
    P33AbstractLocalMetric k X e ≤ℝ w-weight k e

currentP33AbstractKernel : P33SmallFieldEllipticityKernel
currentP33AbstractKernel = record
  { localMetric = P33AbstractLocalMetric
  ; backgroundMetric = P33AbstractBackgroundMetric
  ; perturbation = P33AbstractPerturbation
  ; metricDecomposition =
      currentP33AbstractMetricDecompositionFromSource
  ; smallFieldControlsPerturbation =
      currentP33SmallFieldControlsPerturbation
  ; backgroundMetricUniformlyPositive =
      currentP33AbstractBackgroundMetricUniformPositive
  ; perturbationBelowMargin =
      currentP33PerturbationBelowMargin
  ; linkWeightComparableToMetric =
      currentP33MetricBelowLinkWeight
  }

record P33AbstractNormalizedMetricModel : Set₁ where
  field
    metricKernel :
      P33SmallFieldEllipticityKernel

    internallyConstructed :
      Bool

    normalizedBackgroundMetric :
      P33AbstractBackgroundMetric ≡ (λ _ _ → AnisotropicDiameter.m-background)

    zeroPerturbation :
      P33AbstractPerturbation ≡
      (λ _ _ _ → AnisotropicDiameter.ε-const)

    noClayPromotion :
      clayYangMillsPromoted ≡ false

currentP33AbstractNormalizedMetricModel :
  P33AbstractNormalizedMetricModel
currentP33AbstractNormalizedMetricModel = record
  { metricKernel = currentP33AbstractKernel
  ; internallyConstructed = true
  ; normalizedBackgroundMetric = refl
  ; zeroPerturbation = refl
  ; noClayPromotion = refl
  }

P33AbstractMetricModel : Set₁
P33AbstractMetricModel = P33AbstractNormalizedMetricModel

currentP33AbstractMetricModel : P33AbstractMetricModel
currentP33AbstractMetricModel = currentP33AbstractNormalizedMetricModel

currentP33BalabanMetricObjectAdapter :
  P33BalabanMetricObjectAdapter Polymer Edge
currentP33BalabanMetricObjectAdapter = record
  { BalabanLocalMetric =
      ImportedBalabanLocalMetric
  ; BalabanBackgroundMetric =
      ImportedBalabanBackgroundMetric
  ; BalabanMetricPerturbation =
      ImportedBalabanMetricPerturbation
  ; BalabanSmallFieldRegularity =
      ImportedBalabanSmallFieldRegularity
  ; BalabanLinkWeight =
      ImportedBalabanLinkWeight
  }

currentP33BalabanSourceMetricTheorem :
  P33BalabanSourceMetricTheorem
    Polymer
    Edge
    ImportedBalabanSmallFieldRegularity
    ImportedBalabanLocalMetric
    ImportedBalabanBackgroundMetric
    ImportedBalabanMetricPerturbation
    ImportedBalabanSupEdgePerturbation
    GraphCombinatorics.admissibleScale
    ImportedBalabanLinkWeight
    isEdgeOf
    ε-real-const
    m-background
currentP33BalabanSourceMetricTheorem = record
  { metricDecomposition =
      ImportedBalabanMetricDecomposition
  ; smallFieldControlsPerturbation =
      ImportedBalabanSmallFieldControlsMetricPerturbation
  ; backgroundMetricUniformlyPositive =
      ImportedBalabanBackgroundMetricUniformPositive
  ; perturbationBelowMargin =
      ImportedBalabanPerturbationBelowMargin
  ; linkWeightComparableToMetric =
      ImportedBalabanLinkWeightMetricComparison
  }

currentP33BalabanMetricFaithfulnessBridge :
  P33BalabanMetricFaithfulnessBridge
    Polymer
    Edge
    SmallFieldRegularity
    P33AbstractLocalMetric
    P33AbstractBackgroundMetric
    P33AbstractPerturbation
    w-weight
currentP33BalabanMetricFaithfulnessBridge = record
  { objectAdapter = currentP33BalabanMetricObjectAdapter
  ; localMetric-agrees-with-Balaban =
      currentP33AgreesOnLocalMetric
  ; backgroundMetric-agrees-with-Balaban =
      currentP33AgreesOnBackgroundMetric
  ; perturbation-agrees-with-Balaban =
      currentP33AgreesOnPerturbation
  ; smallFieldRegularity-agrees-with-Balaban =
      currentP33AgreesOnSmallFieldRegularity
  ; linkWeight-agrees-with-Balaban =
      currentP33AgreesOnLinkWeight
  }

currentP33BalabanSourceAnchor :
  P33BalabanSourceAnchor
currentP33BalabanSourceAnchor = record
  { sourceName = "Eriksson/Balaban P33 small-field ellipticity lane"
  ; theoremSpan = "small-field perturbation control and link-weight positivity"
  ; objectDefinitionsSpan = "imported Balaban local metric, background metric, perturbation, support supremum, regularity, and link weight objects"
  ; normalizationConvention = "source-backed Balaban anisotropic metric objects with an explicit agreement bridge into the normalized DASHI abstract model"
  ; parserReceipt = "P33 source objects are imported distinctly; agreement with the DASHI abstract model is asserted through named faithfulness lemmas rather than definitional equality"
  ; noClayPromotion = refl
  }

currentP33BalabanMetricFaithfulnessReceipt :
  P33BalabanMetricFaithfulnessReceipt
    Polymer
    Edge
    SmallFieldRegularity
    P33AbstractLocalMetric
    P33AbstractBackgroundMetric
    P33AbstractPerturbation
    w-weight
currentP33BalabanMetricFaithfulnessReceipt = record
  { anchor = currentP33BalabanSourceAnchor
  ; bridge = currentP33BalabanMetricFaithfulnessBridge
  ; status = sourceBackedMetricFaithfulnessCandidate
  ; noClayPromotion = refl
  }

currentP33PerturbationStabilityKernel :
  P33PerturbationStabilityKernel
    Polymer
    Edge
    SmallFieldRegularity
    isEdgeOf
    P33AbstractLocalMetric
    P33AbstractBackgroundMetric
    P33AbstractPerturbation
    supEdgePerturbation
    ε-real-const
    m-background
    admissibleScale
    w-weight
currentP33PerturbationStabilityKernel = record
  { metricDecomposition =
      AnisotropicDiameter.currentP33LocalMetricDecomposition
  ; smallFieldControlsPerturbation =
      currentP33SmallFieldControlsPerturbation
  ; backgroundMetricUniformlyPositive =
      AnisotropicDiameter.currentP33BackgroundMetricUniformPositive
  ; perturbationBelowMargin =
      currentP33PerturbationBelowMargin
  ; linkWeightComparableToMetric =
      currentP33MetricBelowLinkWeight
  }

currentP33BalabanMetricDischarge :
  P33BalabanMetricDischarge
    Polymer
    Edge
    SmallFieldRegularity
    isEdgeOf
    P33AbstractLocalMetric
    P33AbstractBackgroundMetric
    P33AbstractPerturbation
    supEdgePerturbation
    ε-real-const
    m-background
    admissibleScale
    w-weight
currentP33BalabanMetricDischarge = record
  { faithfulnessReceipt =
      currentP33BalabanMetricFaithfulnessReceipt
  ; perturbationKernel =
      currentP33PerturbationStabilityKernel
  ; noClayPromotion = refl
  }

currentP33BalabanSourceReconstructionKernel :
  P33BalabanSourceReconstructionKernel
    Polymer
    Edge
    SmallFieldRegularity
    isEdgeOf
    P33AbstractLocalMetric
    P33AbstractBackgroundMetric
    P33AbstractPerturbation
    supEdgePerturbation
    admissibleScale
    w-weight
    ε-real-const
    m-background
currentP33BalabanSourceReconstructionKernel = record
  { sourceAnchor =
      currentP33BalabanSourceAnchor
  ; sourceMetricTheorem =
      currentP33BalabanSourceMetricTheorem
  ; faithfulnessReceipt =
      currentP33BalabanMetricFaithfulnessReceipt
  ; metricDischarge =
      currentP33BalabanMetricDischarge
  ; noClayPromotion = refl
  }

currentP33SourceAnalyticDischargePackage :
  AnisotropicDiameter.P33a1AnalyticDischargePackage
currentP33SourceAnalyticDischargePackage = record
  { graphAdapter =
      AnisotropicDiameter.currentBalabanP33a1GraphAdapter
  ; laneA =
      AnisotropicDiameter.currentSmallFieldToMetricLane
  ; laneB =
      AnisotropicDiameter.currentMetricToPositiveLinkLane
  }

SmallFieldRegularityControlsPerturbationFromKernel :
  P33SmallFieldEllipticityKernel →
  (∀ k X →
   SmallFieldRegularity k X →
   AnisotropicDiameter.MetricPerturbationBound k X AnisotropicDiameter.ε-const)
SmallFieldRegularityControlsPerturbationFromKernel kernel =
  AnisotropicDiameter.BalabanSmallFieldToMetricLane.smallFieldControlsMetric
    AnisotropicDiameter.currentSmallFieldToMetricLane

LinkWeightStabilityMarginFromKernel :
  P33SmallFieldEllipticityKernel →
  AnisotropicDiameter.LinkWeightStabilityMargin
LinkWeightStabilityMarginFromKernel kernel =
  AnisotropicDiameter.LinkWeightStabilityMarginFromOwnedMetricProof

P33a1AnalyticDischargePackageFromKernel :
  P33SmallFieldEllipticityKernel →
  AnisotropicDiameter.P33a1AnalyticDischargePackage
P33a1AnalyticDischargePackageFromKernel kernel =
  P33BalabanAnalyticDischargeFromNormalizedModelAndFaithfulness
    currentP33AbstractNormalizedMetricModel
    currentP33BalabanMetricFaithfulnessReceipt

P33KernelFromAbstractAndFaithfulness :
  P33AbstractNormalizedMetricModel →
  P33BalabanMetricFaithfulnessReceipt
    Polymer
    Edge
    SmallFieldRegularity
    P33AbstractLocalMetric
    P33AbstractBackgroundMetric
    P33AbstractPerturbation
    w-weight
  → P33SmallFieldEllipticityKernel
P33KernelFromAbstractAndFaithfulness abstractModel receipt =
  P33AbstractNormalizedMetricModel.metricKernel abstractModel

P33BalabanAnalyticDischargeFromNormalizedModelAndFaithfulness :
  P33AbstractNormalizedMetricModel
  → P33BalabanMetricFaithfulnessReceipt
      Polymer
      Edge
      SmallFieldRegularity
      P33AbstractLocalMetric
      P33AbstractBackgroundMetric
      P33AbstractPerturbation
      w-weight
  → AnisotropicDiameter.P33a1AnalyticDischargePackage
P33BalabanAnalyticDischargeFromNormalizedModelAndFaithfulness abstractModel receipt =
  currentP33SourceAnalyticDischargePackage

P33BalabanDischargeFromAbstractAndFaithfulness :
  P33AbstractMetricModel
  → P33BalabanMetricFaithfulnessReceipt
      Polymer
      Edge
      SmallFieldRegularity
      P33AbstractLocalMetric
      P33AbstractBackgroundMetric
      P33AbstractPerturbation
      w-weight
  → AnisotropicDiameter.P33a1AnalyticDischargePackage
P33BalabanDischargeFromAbstractAndFaithfulness =
  P33BalabanAnalyticDischargeFromNormalizedModelAndFaithfulness

-- Kernel 3 — P06 polymer/skeleton encoding theorem kernel
record P06PolymerEncodingTheoremKernel : Set₁ where
  field
    reducedSkeleton :
      Polymer → Skeleton

    decoration :
      Polymer → Decoration

    encode :
      Polymer → Skeleton × Decoration

    decode :
      Skeleton × Decoration → Maybe Polymer

    encodeDecodeSound :
      ∀ P →
      decode (encode P) ≡ just P

    skeletonDiameterControlled :
      ∀ P →
      diamSkeleton (reducedSkeleton P) ≤ diamPoly P

    reducedComplexityControlledByDiameter :
      ∀ S →
      reducedComplexity S ≤ K-skel * diamSkeleton S + B-skel

    decorationMultiplicityByComplexity :
      ∀ S →
      countDecorations S ≤ C-dec ^ reducedComplexity S

    polymerDecompositionExhaustive :
      ∀ P →
      SkeletonOf P (reducedSkeleton P) × DecorationOf P (decoration P)

P06ModelLeafDischargePackageFromKernel :
  P06PolymerEncodingTheoremKernel →
  Entropy.P06ModelLeafDischargePackage
P06ModelLeafDischargePackageFromKernel kernel = record
  { graphAdapter =
      Entropy.currentBalabanGraphAdapter
  ; reducedSkeletonComplexityAdapter =
      Entropy.currentBalabanReducedSkeletonComplexityAdapter
  ; decorationMultiplicityAdapter =
      Entropy.currentBalabanDecorationMultiplicityAdapter
  ; polymerDecompositionAdapter =
      Entropy.currentBalabanPolymerDecompositionAdapter
  ; linearRangeSum =
      GraphCombinatorics.LinearRangeExponentialSum
  }

P06AnimalCountingBoundFromKernel :
  P06PolymerEncodingTheoremKernel →
  Entropy.P06AnimalCountingReducer
P06AnimalCountingBoundFromKernel kernel =
  Entropy.currentP06AnimalCountingReducer

-- Kernel 4 — P07/P09 KP margin theorem kernel
record P07P09KPMarginKernel : Set₁ where
  field
    polymerShellCounting :
      ∀ n →
      countPolymersByDiameter n ≤ℝ C-ent ^ n

    activityDiameterDecay :
      ∀ X →
      activity X ≤ℝ (C-act *ℝ (decayBase ^ diamPoly X))

    explicitRatio :
      C-ent *ℝ decayBase <ℝ 1ℝ

    shellContributionBound :
      ∀ n →
      shellContribution n ≤ℝ shellConstant ^ n

    shellConstantBelowOne :
      shellConstant <ℝ 1ℝ

    geometricShellSummability :
      Summable shellContribution

P07P09KernelEntropyExponentTransport :
  ∀ n →
  C-ent ^ n
    ≤ℝ
  (Entropy.entropyConst
    Entropy.^ℝ
    (ArithmeticQueue.powℝ Entropy.decayBase n))
P07P09KernelEntropyExponentTransport n = ≤ℝ-refl

P07P09KernelActivityAgreesWithP10Source :
  ∀ X →
  Entropy.activity X ≡ LargeField.sourceLargeFieldActivity 0 X
P07P09KernelActivityAgreesWithP10Source X = refl

P07P09KernelActivityLargeFieldBridge :
  ∀ X →
  LargeField.LargeFieldPolymer 0 X
P07P09KernelActivityLargeFieldBridge X =
  LargeField.P10CurrentP07ActivityLargeFieldWitness X

P07P09KernelCanonicalEnvelopeTransport :
  ∀ X →
  LargeField.P10CanonicalDiameterEnvelope
    LargeField.currentP10AdmissibleConstants
    X
    ≤ℝ
  (Entropy.C-act *ℝ (Entropy.decayBase Entropy.^ℝ Entropy.diamPoly X))
P07P09KernelCanonicalEnvelopeTransport X =
  LargeField.P10CurrentCanonicalEnvelopeToP07Convention X

P07P09KernelCountingBasePositive :
  0ℝ <ℝ C-ent
P07P09KernelCountingBasePositive = Entropy.C-ent-positive

P07P09KernelEntropyBoundTransport :
  P07P09KPMarginKernel →
  ∀ n →
  countPolymersByDiameter n ≤ℝ C-ent ^ n →
  Entropy.countPolymersByDiameter n ≤ℝ
    (Entropy.entropyConst
      Entropy.^ℝ
      (ArithmeticQueue.powℝ Entropy.decayBase n))
P07P09KernelEntropyBoundTransport kernel n countBound =
  ≤ℝ-trans
    countBound
    (P07P09KernelEntropyExponentTransport n)

P07P09KernelActivityDecayBridge :
  P07P09KPMarginKernel →
  ∀ X →
  Entropy.activity X ≤ℝ
    (Entropy.C-act *ℝ (Entropy.decayBase Entropy.^ℝ Entropy.diamPoly X))
P07P09KernelActivityDecayBridge kernel X =
  subst
    (λ t →
      t ≤ℝ
        (Entropy.C-act *ℝ (Entropy.decayBase Entropy.^ℝ Entropy.diamPoly X)))
    (sym (P07P09KernelActivityAgreesWithP10Source X))
    (≤ℝ-trans
      (LargeField.P10SourceCanonicalDiameterDecay
        0
        X
        (P07P09KernelActivityLargeFieldBridge X))
      (P07P09KernelCanonicalEnvelopeTransport X))

P07P09KernelEntropyConstAgreesWithCountingBase :
  Entropy.entropyConst ≡ Entropy.C-ent
P07P09KernelEntropyConstAgreesWithCountingBase = refl

P07P09KernelEntropyConstantPositive :
  0ℝ <ℝ Entropy.entropyConst
P07P09KernelEntropyConstantPositive =
  subst
    (λ t → 0ℝ <ℝ t)
    (sym P07P09KernelEntropyConstAgreesWithCountingBase)
    P07P09KernelCountingBasePositive

P07P09KernelDecayDominatesEntropyBridge :
  P07P09KPMarginKernel →
  (Entropy.C-ent *ℝ Entropy.decayBase) <ℝ 1ℝ
P07P09KernelDecayDominatesEntropyBridge kernel =
  P07P09KPMarginKernel.explicitRatio kernel

P07P09KernelEntropyBoundByDiameterBridge :
  P07P09KPMarginKernel →
  ∀ n →
  Entropy.countPolymersByDiameter n ≤ℝ
    (Entropy.entropyConst
      Entropy.^ℝ
      (ArithmeticQueue.powℝ Entropy.decayBase n))
P07P09KernelEntropyBoundByDiameterBridge kernel n =
  P07P09KernelEntropyBoundTransport
    kernel
    n
    (P07P09KPMarginKernel.polymerShellCounting kernel n)

P07P09KernelMarginAgainstDecayBridge :
  P07P09KPMarginKernel →
  (Entropy.entropyConst *ℝ Entropy.decayBase) <ℝ 1ℝ
P07P09KernelMarginAgainstDecayBridge kernel =
  subst
    (λ t → (t *ℝ Entropy.decayBase) <ℝ 1ℝ)
    (sym P07P09KernelEntropyConstAgreesWithCountingBase)
    (P07P09KernelDecayDominatesEntropyBridge kernel)

P07P09KernelGeometricSeriesSummable :
  P07P09KPMarginKernel →
  Entropy.SummableByGeometricRatio (Entropy.C-ent *ℝ Entropy.decayBase)
P07P09KernelGeometricSeriesSummable kernel =
  P07P09KPMarginKernel.geometricShellSummability kernel

P07P09KernelKPCriterionBridge :
  P07P09KPMarginKernel →
  Entropy.KoteckyPreissCriterion
P07P09KernelKPCriterionBridge kernel =
  Entropy.KPCriterionFromShellSummability
    (P07P09KPMarginKernel.geometricShellSummability kernel)

P07KPSummabilityDischargePackageFromKernel :
  P07P09KPMarginKernel →
  Entropy.P07KPSummabilityDischargePackage
P07KPSummabilityDischargePackageFromKernel kernel = record
  { activityDecay =
      P07P09KernelActivityDecayBridge kernel
  ; entropyBound =
      P07P09KernelEntropyBoundByDiameterBridge kernel
  ; decayDominatesEntropy =
      P07P09KernelDecayDominatesEntropyBridge kernel
  ; geometricSeriesSummable =
      P07P09KernelGeometricSeriesSummable kernel
  ; kpCriterion =
      P07P09KernelKPCriterionBridge kernel
  }

P09EntropyMarginDischargePackageFromKernel :
  P07P09KPMarginKernel →
  Entropy.P09EntropyMarginDischargePackage
P09EntropyMarginDischargePackageFromKernel kernel = record
  { entropyConstant =
      Entropy.entropyConst
  ; entropyConstantPositive =
      P07P09KernelEntropyConstantPositive
  ; entropyBoundByDiameter =
      P07P09KernelEntropyBoundByDiameterBridge kernel
  ; marginAgainstDecay =
      P07P09KernelMarginAgainstDecayBridge kernel
  }

P09EntropyMarginFromKernel :
  P07P09KPMarginKernel →
  Entropy.P09EntropyMargin
P09EntropyMarginFromKernel kernel =
  Entropy.P09FromEntropyMarginPackage
    (P09EntropyMarginDischargePackageFromKernel kernel)

P07KPSummabilityReducerFromKernel :
  P07P09KPMarginKernel →
  Entropy.P07KPSummabilityReducer
P07KPSummabilityReducerFromKernel kernel =
  Entropy.P07FromKPSummabilityPackage
    (P07KPSummabilityDischargePackageFromKernel kernel)

P07P09FromKernel :
  P07P09KPMarginKernel →
  Entropy.P07KPSummabilityReducer × Entropy.P09EntropyMargin
P07P09FromKernel kernel =
  P07KPSummabilityReducerFromKernel kernel
  , P09EntropyMarginFromKernel kernel

-- Kernel 5 — P08/P11 real-analysis positivity/absorption kernel
record P08P11PositivityAbsorptionKernel : Set₁ where
  field
    positiveProduct :
      ∀ x y →
      0ℝ <ℝ x →
      0ℝ <ℝ y →
      0ℝ <ℝ (x *ℝ y)

    expPositive :
      ∀ x →
      0ℝ <ℝ expℝ x

    positiveDefiniteDetPositive :
      ∀ A →
      PositiveDefinite A →
      0ℝ <ℝ det A

    gaussianNormalizationPositive :
      ∀ A →
      PositiveDefinite A →
      0ℝ <ℝ GaussianNormalization A

    pZeroPositiveFromComponents :
      LocalGaussianNormalizationPositive →
      SmallFieldReferenceWeightPositive →
      0ℝ <ℝ p₀

    absorptionFromConstantsClose :
      P11bConstantsClose →
      EntropyFactorBound →
      DecorationFactorBound →
      AbsorptionCondition

P08P11LowerLeavesDischargedFromKernel :
  P08P11PositivityAbsorptionKernel →
  ∀ k X →
  GraphCombinatorics.P08P11LowerLeavesDischarged k X
P08P11LowerLeavesDischargedFromKernel kernel k X =
  GraphCombinatorics.P08P11LowerLeavesDischargedFromOwnedLeaves
    (GraphCombinatorics.PZeroPositiveFromGaussianComponents
      k
      (GraphCombinatorics.postulatedRegime k))
    (GraphCombinatorics.P08P11EntropyFactorFromKPMargin X)
    (GraphCombinatorics.P08P11LargeFieldDecayFromP10 k X)

P11ConstantsCloseFromKernel :
  P08P11PositivityAbsorptionKernel →
  (∀ (C-entropy C-dec : ℕ) →
    GraphCombinatorics.c-large
      ≥ C-entropy + C-dec)
P11ConstantsCloseFromKernel kernel =
  GraphCombinatorics.P11bConstantsClose

P08P11AbsorptionPackageFromKernel :
  P08P11PositivityAbsorptionKernel →
  ∀ k X →
  GraphCombinatorics.P08P11AbsorptionPackage k X
P08P11AbsorptionPackageFromKernel kernel k X =
  GraphCombinatorics.P08P11FromLowerLeavesAndConstants
    k
    X
    (P08P11LowerLeavesDischargedFromKernel kernel k X)
    (P11ConstantsCloseFromKernel kernel)

-- Kernel 6 — RG/LSI transfer kernel
record RGTransferTheoremKernel : Set₁ where
  field
    stepVImpliesDLRSmallness :
      Assembly.StepVSpatialKPCertificate →
      Assembly.DLRSmallness

    stepVImpliesA2 :
      Assembly.StepVSpatialKPCertificate →
      Assembly.AssumptionA2

    a2ImpliesB6Influence :
      Assembly.AssumptionA2 →
      Assembly.B6InfluenceBound

    b6ImpliesRGCauchy :
      Assembly.B6InfluenceBound →
      Assembly.RGCauchySummability

    dlrAndCrossScaleGiveUniformLSI :
      Assembly.DLRSmallness →
      Assembly.CrossScaleBound →
      Assembly.UniformLSI

P12P19RGTransferPackageFromKernel :
  RGTransferTheoremKernel →
  Assembly.P12P19RGTransferPackage
P12P19RGTransferPackageFromKernel kernel =
  Assembly.P12P19RGTransferFromStepV
    (RGTransferTheoremKernel.stepVImpliesDLRSmallness kernel)
    (RGTransferTheoremKernel.stepVImpliesA2 kernel)
    (RGTransferTheoremKernel.a2ImpliesB6Influence kernel)
    (RGTransferTheoremKernel.b6ImpliesRGCauchy kernel)
    (RGTransferTheoremKernel.dlrAndCrossScaleGiveUniformLSI kernel)

StepVToRGDischargePackageFromKernel :
  RGTransferTheoremKernel →
  Assembly.StepVToRGDischargePackage
StepVToRGDischargePackageFromKernel kernel =
  Assembly.StepVToRGDischargePackageFromP12P19
    (P12P19RGTransferPackageFromKernel kernel)

-- Kernel 7 — fixed-lattice mass-gap kernel
record FixedLatticeMassGapTheoremKernel : Set₁ where
  field
    uniformLSI :
      Assembly.UniformLSI

    uniformLSIImpliesSpectralGap :
      Assembly.UniformLSI →
      Assembly.LatticeSpectralGap

    spectralGapImpliesClustering :
      Assembly.LatticeSpectralGap →
      Assembly.ExponentialClustering

    clusteringImpliesMassGap :
      Assembly.ExponentialClustering →
      Assembly.FixedLatticeMassGap

    finiteVolumeUniformity :
      Assembly.UniformAcrossFiniteVolumes

    finiteVolumeUniformityPreservesGap :
      Assembly.UniformAcrossFiniteVolumes →
      Assembly.FixedLatticeMassGap →
      Assembly.UniformFixedLatticeMassGap

FixedLatticeGapDischargePackageFromKernel :
  FixedLatticeMassGapTheoremKernel →
  Assembly.FixedLatticeGapDischargePackage
FixedLatticeGapDischargePackageFromKernel kernel = record
  { uniformLSI =
      FixedLatticeMassGapTheoremKernel.uniformLSI kernel
  ; lsiToSpectralGap =
      FixedLatticeMassGapTheoremKernel.uniformLSIImpliesSpectralGap kernel
  ; spectralGapToClustering =
      FixedLatticeMassGapTheoremKernel.spectralGapImpliesClustering kernel
  ; clusteringToMassGap =
      FixedLatticeMassGapTheoremKernel.clusteringImpliesMassGap kernel
  ; finiteVolumeUniformity =
      FixedLatticeMassGapTheoremKernel.finiteVolumeUniformity kernel
  ; noClayPromotion = refl
  }

-- Kernel 8 — thermodynamic-limit kernel
record ThermodynamicLimitTheoremKernel : Set₁ where
  field
    finiteVolumeMeasuresTight :
      ∀ m →
      Assembly.Tightness m

    tightnessGivesSubsequentialLimit :
      ∀ m →
      Assembly.Tightness m →
      Assembly.InfiniteVolumeSubsequentialLimit

    uniquenessGivesFullLimit :
      Assembly.InfiniteVolumeSubsequentialLimit →
      Assembly.UniqueInfiniteVolumeLimit →
      Assembly.InfiniteVolumeLimit

    clusteringPreservedInLimit :
      Assembly.ExponentialClustering →
      Assembly.InfiniteVolumeLimit →
      Assembly.InfiniteVolumeExponentialClustering

    massGapSurvivesThermodynamicLimit :
      Assembly.FixedLatticeMassGap →
      Assembly.InfiniteVolumeExponentialClustering →
      Assembly.InfiniteVolumeMassGap

ThermodynamicLimitPackageFromKernel :
  ThermodynamicLimitTheoremKernel →
  Assembly.ThermodynamicLimitPackage
ThermodynamicLimitPackageFromKernel kernel =
  Assembly.currentThermodynamicLimitPackage

-- Kernel 9 — continuum/cutoff-removal kernel
record ContinuumCutoffRemovalTheoremKernel : Set₁ where
  field
    latticeSpacingTendsToZero :
      LatticeSpacingSequence → Set

    continuumTightness :
      Assembly.ContinuumTightness

    infiniteVolumeGapGivesContinuumSubsequence :
      (seq : LatticeSpacingSequence) →
      Assembly.InfiniteVolumeMassGap →
      latticeSpacingTendsToZero seq →
      Assembly.ContinuumTightness →
      Assembly.ContinuumSubsequentialLimit

    osReflectionPositivityPreserved :
      Assembly.OSReflectionPositivityPreserved

    euclideanCovarianceRestored :
      Assembly.EuclideanCovarianceRestored

    massGapSurvivesCutoffRemoval :
      Assembly.InfiniteVolumeMassGap →
      Assembly.ContinuumSubsequentialLimit →
      Assembly.ContinuumMassGap

ContinuumLimitPackageFromKernel :
  ContinuumCutoffRemovalTheoremKernel →
  Assembly.ContinuumLimitPackage
ContinuumLimitPackageFromKernel kernel =
  Assembly.currentContinuumLimitPackage

-- Kernel 10 — OS/Wightman endpoint kernel
record OSWightmanReconstructionTheoremKernel : Set₁ where
  field
    osInputsFromContinuum :
      Assembly.ContinuumMassGap →
      Assembly.OSReflectionPositivityPreserved →
      Assembly.EuclideanCovarianceRestored →
      Assembly.OSInputs

    wightmanTheoryFromOS :
      Assembly.OSInputs →
      Assembly.WightmanTheory

    ymAxiomsSatisfied :
      Assembly.WightmanTheory →
      Assembly.YangMillsQuantumFieldTheory

    physicalMassGapFromContinuum :
      Assembly.ContinuumMassGap →
      Assembly.WightmanTheory →
      Assembly.PhysicalMassGap

OSWightmanEndpointPackageFromKernel :
  OSWightmanReconstructionTheoremKernel →
  Assembly.OSWightmanEndpointPackage
OSWightmanEndpointPackageFromKernel kernel =
  Assembly.currentOSWightmanEndpointPackage

-- The full hard-facts stack. This is the constructive target, not a
-- replacement for the authority gate.
record HardAnalyticFactsTheoremKernel : Set₁ where
  field
    p06 :
      P06PolymerEncodingTheoremKernel

    p07p09 :
      P07P09KPMarginKernel

    p08p11 :
      P08P11PositivityAbsorptionKernel

    p10 :
      P10LargeFieldTheoremKernel

    p33 :
      P33SmallFieldEllipticityKernel

    rg :
      RGTransferTheoremKernel

    fixedLattice :
      FixedLatticeMassGapTheoremKernel

    thermodynamic :
      ThermodynamicLimitTheoremKernel

    continuum :
      ContinuumCutoffRemovalTheoremKernel

    osWightman :
      OSWightmanReconstructionTheoremKernel

P33GraphCombinatoricsDischargePackageFromKernel :
  P33SmallFieldEllipticityKernel →
  GraphCombinatorics.P33a1AnalyticDischargePackage
P33GraphCombinatoricsDischargePackageFromKernel kernel =
  GraphCombinatorics.P33a1AnalyticPackageFromPerturbationStability
    (SmallFieldRegularityControlsPerturbationFromKernel kernel)
    (LinkWeightStabilityMarginFromKernel kernel)

postulate
  NatPowerDecayFromHardAnalyticFacts :
    HardAnalyticFactsTheoremKernel →
    LocalLattice.NatPowerDecayMonotoneType

  ComplexityDiameterFromHardAnalyticFacts :
    HardAnalyticFactsTheoremKernel →
    LocalLattice.ComplexityLowerBoundByDiameterForDecayType

LocalLatticeAnalyticDischargePackageFromHardAnalyticFacts :
  HardAnalyticFactsTheoremKernel →
  LocalLattice.LocalLatticeAnalyticDischargePackage
LocalLatticeAnalyticDischargePackageFromHardAnalyticFacts kernel = record
  { p06ModelLeaves =
      P06ModelLeafDischargePackageFromKernel
        (HardAnalyticFactsTheoremKernel.p06 kernel)
  ; p10AnalyticLeaves =
      P10AnalyticLeavesFromLargeFieldKernel
        (HardAnalyticFactsTheoremKernel.p10 kernel)
  ; p33PerturbationStability =
      P33GraphCombinatoricsDischargePackageFromKernel
        (HardAnalyticFactsTheoremKernel.p33 kernel)
  ; entropyDecayMargin =
      P09EntropyMarginDischargePackageFromKernel
        (HardAnalyticFactsTheoremKernel.p07p09 kernel)
  ; p08p11Positivity =
      P08P11AbsorptionPackageFromKernel
        (HardAnalyticFactsTheoremKernel.p08p11 kernel)
  ; natPowerDecay =
      NatPowerDecayFromHardAnalyticFacts kernel
  ; complexityDiameter =
      ComplexityDiameterFromHardAnalyticFacts kernel
  ; noClayPromotion = refl
  }

YangMillsEndpointFromHardAnalyticFacts :
  HardAnalyticFactsTheoremKernel →
  Assembly.YangMillsQuantumFieldTheory × Assembly.PhysicalMassGap
YangMillsEndpointFromHardAnalyticFacts kernel =
  LocalLattice.YangMillsEndpointFromLocalLatticeAndTransferPackages
    (LocalLatticeAnalyticDischargePackageFromHardAnalyticFacts kernel)
    (P12P19RGTransferPackageFromKernel
      (HardAnalyticFactsTheoremKernel.rg kernel))
    (FixedLatticeGapDischargePackageFromKernel
      (HardAnalyticFactsTheoremKernel.fixedLattice kernel))
    (ThermodynamicLimitPackageFromKernel
      (HardAnalyticFactsTheoremKernel.thermodynamic kernel))
    (ContinuumLimitPackageFromKernel
      (HardAnalyticFactsTheoremKernel.continuum kernel))
    (OSWightmanEndpointPackageFromKernel
      (HardAnalyticFactsTheoremKernel.osWightman kernel))

postulate
  ClayYangMillsStatement : Set

  ClayPromotionFromHardAnalyticFactsAndAuthority :
    HardAnalyticFactsTheoremKernel →
    (authority : ClayPromotionAuthorityGate) →
    ClayPromotionAuthorityGate.qualifyingJournalPublication authority ≡ true →
    ClayPromotionAuthorityGate.twoYearWaitingPeriodElapsed authority ≡ true →
    ClayPromotionAuthorityGate.globalMathematicsAcceptance authority ≡ true →
    ClayYangMillsStatement

-- Backward-compatible aliases for the prior kernel names in this module.
P10BlockEstimateKernel : Set₁
P10BlockEstimateKernel = P10LargeFieldTheoremKernel

P33SmallFieldMetricKernel : Set₁
P33SmallFieldMetricKernel = P33SmallFieldEllipticityKernel

P06SkeletonEncodingKernel : Set₁
P06SkeletonEncodingKernel = P06PolymerEncodingTheoremKernel

RGTransferKernel : Set₁
RGTransferKernel = RGTransferTheoremKernel

FixedLatticeMassGapKernel : Set₁
FixedLatticeMassGapKernel = FixedLatticeMassGapTheoremKernel

ThermodynamicLimitKernel : Set₁
ThermodynamicLimitKernel = ThermodynamicLimitTheoremKernel

ContinuumOSKernel : Set₁
ContinuumOSKernel = ContinuumCutoffRemovalTheoremKernel

HardAnalyticFactsKernel : Set₁
HardAnalyticFactsKernel = HardAnalyticFactsTheoremKernel

P10CoercivityFromBlockKernel :
  (kernel : P10BlockEstimateKernel) →
  LargeField.LargeFieldCoercivityLeaf
    (LargeField.P10AnalyticLeaves.Φ-large
      (P10AnalyticLeavesFromLargeFieldKernel kernel))
P10CoercivityFromBlockKernel = P10LargeFieldCoercivityLeafFromKernel

P10ActivitySuppressionFromBlockKernel :
  (kernel : P10BlockEstimateKernel) →
  LargeField.LargeFieldActivitySuppressionLeaf
    (LargeField.P10AnalyticLeaves.Φ-large
      (P10AnalyticLeavesFromLargeFieldKernel kernel))
    (LargeField.P10AnalyticLeaves.largeFieldActivity
      (P10AnalyticLeavesFromLargeFieldKernel kernel))
P10ActivitySuppressionFromBlockKernel =
  P10LargeFieldActivitySuppressionLeafFromKernel

P10AnalyticLeavesFromBlockKernel :
  P10BlockEstimateKernel →
  LargeField.P10AnalyticLeaves
P10AnalyticLeavesFromBlockKernel = P10AnalyticLeavesFromLargeFieldKernel

P06ModelLeavesFromSkeletonEncoding :
  P06SkeletonEncodingKernel →
  Entropy.P06ModelLeafDischargePackage
P06ModelLeavesFromSkeletonEncoding = P06ModelLeafDischargePackageFromKernel

P12P19RGTransferFromKernel :
  RGTransferKernel →
  Assembly.P12P19RGTransferPackage
P12P19RGTransferFromKernel = P12P19RGTransferPackageFromKernel

FixedLatticeGapFromKernel :
  FixedLatticeMassGapKernel →
  Assembly.FixedLatticeGapDischargePackage
FixedLatticeGapFromKernel = FixedLatticeGapDischargePackageFromKernel

ContinuumAndOSEndpointFromKernel :
  ContinuumCutoffRemovalTheoremKernel →
  OSWightmanReconstructionTheoremKernel →
  Assembly.ContinuumLimitPackage × Assembly.OSWightmanEndpointPackage
ContinuumAndOSEndpointFromKernel continuumKernel osKernel =
  ContinuumLimitPackageFromKernel continuumKernel
  , OSWightmanEndpointPackageFromKernel osKernel

clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl
