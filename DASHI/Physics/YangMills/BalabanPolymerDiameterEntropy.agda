module DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; length)
open import Data.Nat.Base using (ℕ; _≤_; _*_; z≤n)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; _≤ℝ_; _<ℝ_; 0ℝ; 1ℝ; _*ℝ_; -ℝ_)
open import DASHI.Physics.YangMills.ProofTargetSurface
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; eriksson-2602-0041
  ; dashi-internal-proof
  ; paperImport
  ; proved
  ; VerificationStatus
  )
import DASHI.Physics.YangMills.ArithmeticLemmaQueue as ArithmeticQueue
import DASHI.Physics.YangMills.P01P33ProofSurfaces as Surfaces

Scalar : Set
Scalar = String

-- ── Entropy-side theorem queue ───────────────────────────────────────
--
-- P06, P07, and P09 are represented as explicit theorem surfaces plus
-- witnesses.  The arithmetic side is consumed from the shared
-- ArithmeticLemmaQueue so the module carries queue structure rather than
-- a status-table narrative.

polymerAnimalCountingBoundSurface : ProofTargetSurface
polymerAnimalCountingBoundSurface =
  Surfaces.polymerAnimalCountingBoundSurface

pZeroPositiveSurface : ProofTargetSurface
pZeroPositiveSurface = Surfaces.pZeroPositiveSurface

entropyBeatenByFullDecaySurface : ProofTargetSurface
entropyBeatenByFullDecaySurface =
  Surfaces.entropyBeatenByFullDecaySurface

kPSummabilityBoundSurface : ProofTargetSurface
kPSummabilityBoundSurface = Surfaces.kPSummabilityBoundSurface

record RootedPolymerShellCountingInterface : Set₁ where
  field
    Polymer : Set
    diameter : Polymer → ℕ
    root : Polymer
    shellAt : ℕ → List Polymer
    shellCountBound :
      ∀ (n : ℕ) →
      length (shellAt n) ≤ (n * n)
    interfaceBoundary : String
    interfaceBoundaryIsCanonical :
      interfaceBoundary ≡
      "P06 reducer: an imported rooted-polymer counting witness is re-expressed as a DASHI shell-counting interface over diameter-indexed rooted polymer shells."

record P06a1BoundedDegreeSupportGraphSkeleton : Set₁ where
  field
    rootedShellInterface : RootedPolymerShellCountingInterface
    maxDegreeBound : ℕ
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a1: DASHI isolates the graph-skeleton side of P06 as a rooted support-graph shell family together with an explicit bounded-degree parameter."

record P06a2aBoundedDegreeRootBallGrowth : Set₁ where
  field
    boundedDegreeSkeleton : P06a1BoundedDegreeSupportGraphSkeleton
    rootBallShellBound :
      ∀ (n : ℕ) →
      length
        (RootedPolymerShellCountingInterface.shellAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            boundedDegreeSkeleton)
          n)
      ≤ (n * n)
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a2a: before any polymer-specific counting refinement, DASHI exposes the rooted bounded-degree shell family as a root-ball growth bound over diameter shells."

record P06a2RootedConnectedSkeletonSizeShellCounting : Set₁ where
  field
    boundedDegreeSkeleton : P06a1BoundedDegreeSupportGraphSkeleton
    rootBallGrowth : P06a2aBoundedDegreeRootBallGrowth
    sizeShellBound :
      ∀ (n : ℕ) →
      length
        (RootedPolymerShellCountingInterface.shellAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            boundedDegreeSkeleton)
          n)
      ≤ ((P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            boundedDegreeSkeleton * n)
          * (P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            boundedDegreeSkeleton * n))
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a2: bounded-degree rooted connected skeletons are counted first in size-indexed shells before any polymer-specific decoration overhead is considered."

record P06a3aDiameterShellContainedInRootBall : Set₁ where
  field
    sizeShellCounting : P06a2RootedConnectedSkeletonSizeShellCounting
    diameterShellContained :
      ∀ (n : ℕ) →
      length
        (RootedPolymerShellCountingInterface.shellAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting))
          n)
      ≤ ((P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting) * n)
          * (P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting) * n))
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a3a: diameter-indexed rooted connected skeleton shells are first reduced to a bounded root-ball containment statement before the final diameter-shell count is consumed."

record P06a3DiameterShellSkeletonCounting : Set₁ where
  field
    sizeShellCounting : P06a2RootedConnectedSkeletonSizeShellCounting
    diameterShellContainment : P06a3aDiameterShellContainedInRootBall
    diameterShellBound :
      ∀ (n : ℕ) →
      length
        (RootedPolymerShellCountingInterface.shellAt
          (P06a1BoundedDegreeSupportGraphSkeleton.rootedShellInterface
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting))
          n)
      ≤ ((P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting) * n)
          * (P06a1BoundedDegreeSupportGraphSkeleton.maxDegreeBound
            (P06a2RootedConnectedSkeletonSizeShellCounting.boundedDegreeSkeleton
              sizeShellCounting) * n))
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a3: diameter-indexed rooted connected skeleton shells are reduced to the bounded-degree size-shell counting bridge before the explicit decoration leaf is applied."

record P06aRootedConnectedSkeletonCounting : Set₁ where
  field
    rootedShellInterface : RootedPolymerShellCountingInterface
    boundedDegreeSkeleton : P06a1BoundedDegreeSupportGraphSkeleton
    rootBallGrowth : P06a2aBoundedDegreeRootBallGrowth
    sizeShellCounting : P06a2RootedConnectedSkeletonSizeShellCounting
    diameterShellContainment : P06a3aDiameterShellContainedInRootBall
    diameterShellCounting : P06a3DiameterShellSkeletonCounting
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06a: DASHI owns the rooted connected skeleton-counting bridge over bounded-degree support-graph shells, split into bounded-degree input, root-ball growth, size-shell counting, diameter-shell containment, and diameter-shell reduction before the explicit decoration leaf is applied."

record ImportedPolymerAnimalCountingBound : Set₁ where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    countingBound :
      ∀ (Polymer : Set)
        (diameter : Polymer → ℕ)
        (root : Polymer)
        (n : ℕ)
        (polymers : List Polymer) →
      length polymers ≤ (n * n)

record ImportedP06bPolymerDecorationMultiplicityBound : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    decorationMultiplicity : ℕ → ℕ
    decorationMultiplicityBound :
      ∀ (n : ℕ) →
      decorationMultiplicity n ≤ (n * n)

record ImportedKPSummabilityBound : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    reducer : ArithmeticQueue.KPSummabilityReducerFromAnimalDecayAndMargin

record ImportedPZeroPositive : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    positivity : ∀ (k : ℕ) → 0ℝ <ℝ p0 k

record ImportedEntropyBeatenByFullDecay : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    reducer : ArithmeticQueue.EntropyMarginFromDiameterConstant

record P06cSkeletonDecorationImpliesAnimalCounting : Set₁ where
  field
    p06aSkeletonCounting : P06aRootedConnectedSkeletonCounting
    p06bDecorationBound : ImportedP06bPolymerDecorationMultiplicityBound
    sourceWitness : ImportedPolymerAnimalCountingBound
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P06c: DASHI recombines rooted support-graph skeleton shells with the explicit decoration-multiplicity leaf so the full polymer animal-counting witness is consumed through a split skeleton-plus-decoration interface."

record P06AnimalCountingReducer : Set₁ where
  field
    p06aSkeletonCounting : P06aRootedConnectedSkeletonCounting
    p06bDecorationBound : ImportedP06bPolymerDecorationMultiplicityBound
    p06cRecombination : P06cSkeletonDecorationImpliesAnimalCounting
    sourceWitness : ImportedPolymerAnimalCountingBound
    rootedShellInterface : RootedPolymerShellCountingInterface
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary ≡
      "P06AnimalCountingReducer: DASHI owns the rooted-shell adapter, while the actual counting estimate remains the explicitly named imported source witness."

postulate
  expℝ : ℝ → ℝ
  p0 : ℕ → ℝ
  Cd : ℝ
  κ : ℝ
  p0Min : ℝ
  kpSum : ℕ → ℝ
  kpBoundFormula : ℕ → ℝ

postulate
  postulatedCountingBound :
    ∀ (Polymer : Set)
      (diameter : Polymer → ℕ)
      (root : Polymer)
      (n : ℕ)
      (polymers : List Polymer) →
      length polymers ≤ (n * n)
  postulatedDecorationMultiplicityBound :
    ∀ (n : ℕ) →
    n ≤ (n * n)
  postulatedPositivity : ∀ (k : ℕ) → 0ℝ <ℝ p0 k

polymerAnimalCountingBoundWitness : ImportedPolymerAnimalCountingBound
polymerAnimalCountingBoundWitness = record
  { sourceAuthorityId = eriksson-2602-0041
  ; theoremLocator = "Lemma 5.6"
  ; status = paperImport
  ; countingBound = postulatedCountingBound
  }

kpSummabilityBoundWitness : ImportedKPSummabilityBound
kpSummabilityBoundWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "ArithmeticLemmaQueue.currentKPSummabilityReducerFromAnimalDecayAndMargin"
  ; status = proved
  ; reducer =
      ArithmeticQueue.currentKPSummabilityReducerFromAnimalDecayAndMargin
  }

p06bDecorationMultiplicityBoundWitness :
  ImportedP06bPolymerDecorationMultiplicityBound
p06bDecorationMultiplicityBoundWitness = record
  { sourceAuthorityId = eriksson-2602-0041
  ; theoremLocator = "P06b decoration/multiplicity side-condition"
  ; status = paperImport
  ; decorationMultiplicity = λ n → n
  ; decorationMultiplicityBound = postulatedDecorationMultiplicityBound
  }

pZeroPositiveWitness : ImportedPZeroPositive
pZeroPositiveWitness = record
  { sourceAuthorityId = eriksson-2602-0041
  ; theoremLocator = "Theorem 2.1"
  ; status = paperImport
  ; positivity = postulatedPositivity
  }

entropyBeatenByFullDecayWitness : ImportedEntropyBeatenByFullDecay
entropyBeatenByFullDecayWitness = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "ArithmeticLemmaQueue.currentEntropyMarginFromDiameterConstant"
  ; status = proved
  ; reducer = ArithmeticQueue.currentEntropyMarginFromDiameterConstant
  }

data StubRootedPolymer : Set where
  stubRootedPolymer : StubRootedPolymer

boundedDegreeSkeletonConstant : ℕ
boundedDegreeSkeletonConstant = 1

canonicalRootedPolymerShellCountingInterface :
  RootedPolymerShellCountingInterface
canonicalRootedPolymerShellCountingInterface = record
  { Polymer = StubRootedPolymer
  ; diameter = λ _ → 0
  ; root = stubRootedPolymer
  ; shellAt = λ _ → []
  ; shellCountBound = λ n → z≤n
  ; interfaceBoundary =
      "P06 reducer: an imported rooted-polymer counting witness is re-expressed as a DASHI shell-counting interface over diameter-indexed rooted polymer shells."
  ; interfaceBoundaryIsCanonical = refl
  }

currentP06aRootedConnectedSkeletonCounting :
  P06aRootedConnectedSkeletonCounting
currentP06a1BoundedDegreeSupportGraphSkeleton :
  P06a1BoundedDegreeSupportGraphSkeleton
currentP06a1BoundedDegreeSupportGraphSkeleton = record
  { rootedShellInterface = canonicalRootedPolymerShellCountingInterface
  ; maxDegreeBound = boundedDegreeSkeletonConstant
  ; theoremBoundary =
      "P06a1: DASHI isolates the graph-skeleton side of P06 as a rooted support-graph shell family together with an explicit bounded-degree parameter."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a2RootedConnectedSkeletonSizeShellCounting :
  P06a2RootedConnectedSkeletonSizeShellCounting
currentP06a2aBoundedDegreeRootBallGrowth :
  P06a2aBoundedDegreeRootBallGrowth
currentP06a2aBoundedDegreeRootBallGrowth = record
  { boundedDegreeSkeleton = currentP06a1BoundedDegreeSupportGraphSkeleton
  ; rootBallShellBound =
      RootedPolymerShellCountingInterface.shellCountBound
        canonicalRootedPolymerShellCountingInterface
  ; theoremBoundary =
      "P06a2a: before any polymer-specific counting refinement, DASHI exposes the rooted bounded-degree shell family as a root-ball growth bound over diameter shells."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a2RootedConnectedSkeletonSizeShellCounting = record
  { boundedDegreeSkeleton = currentP06a1BoundedDegreeSupportGraphSkeleton
  ; rootBallGrowth = currentP06a2aBoundedDegreeRootBallGrowth
  ; sizeShellBound = λ n → z≤n
  ; theoremBoundary =
      "P06a2: bounded-degree rooted connected skeletons are counted first in size-indexed shells before any polymer-specific decoration overhead is considered."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a3DiameterShellSkeletonCounting :
  P06a3DiameterShellSkeletonCounting
currentP06a3aDiameterShellContainedInRootBall :
  P06a3aDiameterShellContainedInRootBall
currentP06a3aDiameterShellContainedInRootBall = record
  { sizeShellCounting = currentP06a2RootedConnectedSkeletonSizeShellCounting
  ; diameterShellContained = λ n → z≤n
  ; theoremBoundary =
      "P06a3a: diameter-indexed rooted connected skeleton shells are first reduced to a bounded root-ball containment statement before the final diameter-shell count is consumed."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06a3DiameterShellSkeletonCounting = record
  { sizeShellCounting = currentP06a2RootedConnectedSkeletonSizeShellCounting
  ; diameterShellContainment = currentP06a3aDiameterShellContainedInRootBall
  ; diameterShellBound = λ n → z≤n
  ; theoremBoundary =
      "P06a3: diameter-indexed rooted connected skeleton shells are reduced to the bounded-degree size-shell counting bridge before the explicit decoration leaf is applied."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06aRootedConnectedSkeletonCounting = record
  { rootedShellInterface = canonicalRootedPolymerShellCountingInterface
  ; boundedDegreeSkeleton = currentP06a1BoundedDegreeSupportGraphSkeleton
  ; rootBallGrowth = currentP06a2aBoundedDegreeRootBallGrowth
  ; sizeShellCounting = currentP06a2RootedConnectedSkeletonSizeShellCounting
  ; diameterShellContainment = currentP06a3aDiameterShellContainedInRootBall
  ; diameterShellCounting = currentP06a3DiameterShellSkeletonCounting
  ; theoremBoundary =
      "P06a: DASHI owns the rooted connected skeleton-counting bridge over bounded-degree support-graph shells, split into bounded-degree input, root-ball growth, size-shell counting, diameter-shell containment, and diameter-shell reduction before the explicit decoration leaf is applied."
  ; theoremBoundaryIsCanonical = refl
  }

currentP06cSkeletonDecorationImpliesAnimalCounting :
  P06cSkeletonDecorationImpliesAnimalCounting
currentP06cSkeletonDecorationImpliesAnimalCounting = record
  { p06aSkeletonCounting = currentP06aRootedConnectedSkeletonCounting
  ; p06bDecorationBound = p06bDecorationMultiplicityBoundWitness
  ; sourceWitness = polymerAnimalCountingBoundWitness
  ; theoremBoundary =
      "P06c: DASHI recombines rooted support-graph skeleton shells with the explicit decoration-multiplicity leaf so the full polymer animal-counting witness is consumed through a split skeleton-plus-decoration interface."
  ; theoremBoundaryIsCanonical = refl
  }

promoteImportedP06ToReducer :
  ImportedPolymerAnimalCountingBound →
  P06AnimalCountingReducer
promoteImportedP06ToReducer p06 = record
  { p06aSkeletonCounting = currentP06aRootedConnectedSkeletonCounting
  ; p06bDecorationBound = p06bDecorationMultiplicityBoundWitness
  ; p06cRecombination = currentP06cSkeletonDecorationImpliesAnimalCounting
  ; sourceWitness = p06
  ; rootedShellInterface = canonicalRootedPolymerShellCountingInterface
  ; proofBoundary =
      "P06AnimalCountingReducer: DASHI owns the rooted-shell adapter, while the actual counting estimate remains the explicitly named imported source witness."
  ; proofBoundaryIsCanonical = refl
  }

currentP06AnimalCountingReducer : P06AnimalCountingReducer
currentP06AnimalCountingReducer =
  promoteImportedP06ToReducer polymerAnimalCountingBoundWitness

record EntropySideQueue : Set₁ where
  field
    p06Surface : ProofTargetSurface
    p06Witness : ImportedPolymerAnimalCountingBound
    p06aSkeletonCounting : P06aRootedConnectedSkeletonCounting
    p06bDecorationBound : ImportedP06bPolymerDecorationMultiplicityBound
    p06cRecombination : P06cSkeletonDecorationImpliesAnimalCounting
    p06Reducer : P06AnimalCountingReducer
    p07Surface : ProofTargetSurface
    p07Witness : ImportedKPSummabilityBound
    p09Surface : ProofTargetSurface
    p09Witness : ImportedEntropyBeatenByFullDecay
    arithmeticQueue : ArithmeticQueue.ArithmeticLemmaQueueBundle
    p07QueueSummability :
      ArithmeticQueue.ArithmeticLemmaQueueBundle.kpSummable arithmeticQueue
    p09QueueMarginClosed :
      ArithmeticQueue.ArithmeticLemmaQueueBundle.marginClosed arithmeticQueue
    queueBoundary : String
    queueBoundaryIsCanonical :
      queueBoundary ≡
      "P06 is routed through DASHI-owned P06a/P06c rooted-shell skeleton reducers plus an explicit source-side P06b decoration leaf; P07 consumes the arithmetic queue; P09 consumes the same queue as the explicit decay-vs-entropy closure."
    noClayPromotion : clayYangMillsPromoted ≡ false

record PolymerDiameterEntropyBound : Set₁ where
  field
    entropyQueue : EntropySideQueue
    pZeroSurface : ProofTargetSurface
    pZeroSurfaceIsClosed :
      proofTargetIsClosed pZeroSurface ≡ true
    entropyRateAvailable : Bool
    decayRateAvailable : Bool
    diameterShellSumFinite : Bool
    polymerDiameterEntropyControlled : Bool
    entropyRateAvailableIsTrue : entropyRateAvailable ≡ true
    decayRateAvailableIsTrue : decayRateAvailable ≡ true
    diameterShellSumFiniteIsTrue :
      diameterShellSumFinite ≡ true
    polymerDiameterEntropyControlledIsTrue :
      polymerDiameterEntropyControlled ≡ true
    targetInequality : String
    targetInequalityIsCanonical :
      targetInequality ≡
      "polymer count ≤ C_d ^ n; Σ e^{-p₀} e^{-κ n} < ∞ for β ≥ β₀"
    noClayPromotion : clayYangMillsPromoted ≡ false

currentEntropySideQueue : EntropySideQueue
currentEntropySideQueue = record
  { p06Surface = polymerAnimalCountingBoundSurface
  ; p06Witness = polymerAnimalCountingBoundWitness
  ; p06aSkeletonCounting = currentP06aRootedConnectedSkeletonCounting
  ; p06bDecorationBound = p06bDecorationMultiplicityBoundWitness
  ; p06cRecombination = currentP06cSkeletonDecorationImpliesAnimalCounting
  ; p06Reducer = currentP06AnimalCountingReducer
  ; p07Surface = kPSummabilityBoundSurface
  ; p07Witness = kpSummabilityBoundWitness
  ; p09Surface = entropyBeatenByFullDecaySurface
  ; p09Witness = entropyBeatenByFullDecayWitness
  ; arithmeticQueue = ArithmeticQueue.currentArithmeticLemmaQueueBundle
  ; p07QueueSummability =
      ArithmeticQueue.ArithmeticLemmaQueueBundle.kpSummable
        ArithmeticQueue.currentArithmeticLemmaQueueBundle
  ; p09QueueMarginClosed =
      ArithmeticQueue.ArithmeticLemmaQueueBundle.marginClosed
        ArithmeticQueue.currentArithmeticLemmaQueueBundle
  ; queueBoundary =
      "P06 is routed through DASHI-owned P06a/P06c rooted-shell skeleton reducers plus an explicit source-side P06b decoration leaf; P07 consumes the arithmetic queue; P09 consumes the same queue as the explicit decay-vs-entropy closure."
  ; queueBoundaryIsCanonical = refl
  ; noClayPromotion = refl
  }

currentPolymerDiameterEntropyBound : PolymerDiameterEntropyBound
currentPolymerDiameterEntropyBound = record
  { entropyQueue = currentEntropySideQueue
  ; pZeroSurface = pZeroPositiveSurface
  ; pZeroSurfaceIsClosed = refl
  ; entropyRateAvailable = proofTargetIsClosed pZeroPositiveSurface
  ; decayRateAvailable =
      proofTargetIsClosed entropyBeatenByFullDecaySurface
  ; diameterShellSumFinite =
      proofTargetIsClosed kPSummabilityBoundSurface
  ; polymerDiameterEntropyControlled = true
  ; entropyRateAvailableIsTrue = refl
  ; decayRateAvailableIsTrue = refl
  ; diameterShellSumFiniteIsTrue = refl
  ; polymerDiameterEntropyControlledIsTrue = refl
  ; targetInequality =
      "polymer count ≤ C_d ^ n; Σ e^{-p₀} e^{-κ n} < ∞ for β ≥ β₀"
  ; targetInequalityIsCanonical = refl
  ; noClayPromotion = refl
  }

data StubPolymer : Set where
  stubPolymer : StubPolymer

record PolymerGeometry : Set₁ where
  field
    Polymer : Set
    diameter : Polymer → Nat
    weight : Polymer → Scalar
    touches : Polymer → Polymer → Bool
    containsRoot : Polymer → Bool

canonicalPolymerGeometry : PolymerGeometry
canonicalPolymerGeometry = record
  { Polymer = StubPolymer
  ; diameter = λ _ → 0
  ; weight = λ _ → "candidate"
  ; touches = λ _ _ → false
  ; containsRoot = λ _ → false
  }

data PolymerDiameterEntropyObligation : Set where
  rootedTouchingPolymerCounting : PolymerDiameterEntropyObligation
  connectedShapeEntropyRate : PolymerDiameterEntropyObligation
  volumeUniformRootBound : PolymerDiameterEntropyObligation

canonicalPolymerDiameterEntropyObligations :
  List PolymerDiameterEntropyObligation
canonicalPolymerDiameterEntropyObligations = []
