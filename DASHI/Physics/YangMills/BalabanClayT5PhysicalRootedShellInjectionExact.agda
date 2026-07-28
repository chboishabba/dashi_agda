module DASHI.Physics.YangMills.BalabanClayT5PhysicalRootedShellInjectionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact using
  (SignedAxis4)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Repository-specific boundary cluster to rooted-shell injection.
-- No external source is expected: this is finite graph geometry plus the
-- canonical root/word decoder left inverse.
------------------------------------------------------------------------

record BoundaryGeometry (Block Volume Observable : Set) : Set₁ where
  field
    distance : Block → Block → Nat
    boundary : Volume → Block → Set
    observableSupport : Observable → Block → Set

    distanceReflexive : ∀ block → distance block block ≡ 0
    distanceSymmetric : ∀ left right →
      distance left right ≡ distance right left
    triangleInequality : ∀ left middle right → Set

    supportDistanceToBoundary : Volume → Observable → Nat
    supportBoundaryDistanceLowerBound : ∀ volume observable supportBlock boundaryBlock →
      observableSupport observable supportBlock →
      boundary volume boundaryBlock → Set

open BoundaryGeometry public

record PhysicalClusterCarrier
    (Block Polymer Cluster : Set) : Set₁ where
  field
    polymerOf : Cluster → Polymer
    blocks : Polymer → List Block
    belongs : Block → Polymer → Set
    clusterDiameter : Cluster → Nat

    connected : ∀ cluster left right →
      belongs left (polymerOf cluster) →
      belongs right (polymerOf cluster) → Set

    diameterDominatesPairDistance :
      ∀ {Volume Observable}
        (geometry : BoundaryGeometry Block Volume Observable)
        cluster left right →
        belongs left (polymerOf cluster) →
        belongs right (polymerOf cluster) → Set

open PhysicalClusterCarrier public

record BoundaryCrossingWitness
    {Block Volume Observable Polymer Cluster : Set}
    (geometry : BoundaryGeometry Block Volume Observable)
    (carrier : PhysicalClusterCarrier Block Polymer Cluster)
    (volume : Volume) (observable : Observable) (cluster : Cluster) : Set₁ where
  field
    supportBlock boundaryBlock : Block
    supportBlockInObservable :
      observableSupport geometry observable supportBlock
    boundaryBlockOnBoundary :
      boundary geometry volume boundaryBlock
    supportBlockInCluster :
      belongs carrier supportBlock (polymerOf carrier cluster)
    boundaryBlockInCluster :
      belongs carrier boundaryBlock (polymerOf carrier cluster)

open BoundaryCrossingWitness public

record BoundaryCrossingDiameterProof
    {Block Volume Observable Polymer Cluster : Set}
    (geometry : BoundaryGeometry Block Volume Observable)
    (carrier : PhysicalClusterCarrier Block Polymer Cluster) : Set₁ where
  field
    diameterAtLeastSupportBoundaryDistance :
      ∀ volume observable cluster →
      BoundaryCrossingWitness geometry carrier volume observable cluster →
      Set

open BoundaryCrossingDiameterProof public

record CanonicalRootedTrace
    (Block Polymer : Set) : Set₁ where
  field
    root : Polymer → Block
    word : Polymer → List SignedAxis4
    decode : Block → List SignedAxis4 → Polymer
    decoderLeftInverse : ∀ polymer →
      decode (root polymer) (word polymer) ≡ polymer
    shellIndex : Polymer → Nat
    wordLengthControlsShell : ∀ polymer → Set

open CanonicalRootedTrace public

cong₂ :
  ∀ {A B C : Set} {a a' : A} {b b' : B} →
  (f : A → B → C) → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ f refl refl = refl

canonicalTraceInjective :
  ∀ {Block Polymer}
    (trace : CanonicalRootedTrace Block Polymer)
    {left right : Polymer} →
    root trace left ≡ root trace right →
    word trace left ≡ word trace right →
    left ≡ right
canonicalTraceInjective trace {left} {right} rootsEqual wordsEqual =
  trans
    (sym (decoderLeftInverse trace left))
    (trans
      (cong₂ (decode trace) rootsEqual wordsEqual)
      (decoderLeftInverse trace right))

record PhysicalRootedShellInjection
    (Block Volume Observable Polymer Cluster : Set)
    (geometry : BoundaryGeometry Block Volume Observable)
    (carrier : PhysicalClusterCarrier Block Polymer Cluster)
    (trace : CanonicalRootedTrace Block Polymer) : Set₁ where
  field
    diameterProof : BoundaryCrossingDiameterProof geometry carrier

    clusterTraceRoot : Cluster → Block
    clusterTraceWord : Cluster → List SignedAxis4
    clusterShellIndex : Cluster → Nat

    clusterTraceUsesPolymerRoot : ∀ cluster →
      clusterTraceRoot cluster ≡ root trace (polymerOf carrier cluster)
    clusterTraceUsesPolymerWord : ∀ cluster →
      clusterTraceWord cluster ≡ word trace (polymerOf carrier cluster)
    clusterShellUsesPolymerShell : ∀ cluster →
      clusterShellIndex cluster ≡ shellIndex trace (polymerOf carrier cluster)

    shellIndexAtLeastDiameter : ∀ cluster → Set

    boundaryClusterToTraceInjective : ∀ left right →
      clusterTraceRoot left ≡ clusterTraceRoot right →
      clusterTraceWord left ≡ clusterTraceWord right →
      polymerOf carrier left ≡ polymerOf carrier right

    boundaryCrossingClusterRootedShellInjection :
      ∀ volume observable cluster →
      BoundaryCrossingWitness geometry carrier volume observable cluster → Set

open PhysicalRootedShellInjection public

polymerEqualityFromClusterTrace :
  ∀ {Block Volume Observable Polymer Cluster geometry carrier trace}
    (dataSet :
      PhysicalRootedShellInjection
        Block Volume Observable Polymer Cluster geometry carrier trace)
    left right →
    clusterTraceRoot dataSet left ≡ clusterTraceRoot dataSet right →
    clusterTraceWord dataSet left ≡ clusterTraceWord dataSet right →
    polymerOf carrier left ≡ polymerOf carrier right
polymerEqualityFromClusterTrace {trace = trace} dataSet left right rootEquality wordEquality =
  canonicalTraceInjective trace
    (trans
      (sym (clusterTraceUsesPolymerRoot dataSet left))
      (trans rootEquality (clusterTraceUsesPolymerRoot dataSet right)))
    (trans
      (sym (clusterTraceUsesPolymerWord dataSet left))
      (trans wordEquality (clusterTraceUsesPolymerWord dataSet right)))

record BoundaryTailFromRootedShell
    (Block Volume Observable Polymer Cluster : Set)
    (geometry : BoundaryGeometry Block Volume Observable)
    (carrier : PhysicalClusterCarrier Block Polymer Cluster)
    (trace : CanonicalRootedTrace Block Polymer)
    (injection :
      PhysicalRootedShellInjection
        Block Volume Observable Polymer Cluster geometry carrier trace) : Set₁ where
  field
    clusterWeight : Cluster → ℚ
    boundaryDifferenceCluster : Volume → Observable → Cluster → Set

    boundaryDifferenceImpliesCrossing : ∀ volume observable cluster →
      boundaryDifferenceCluster volume observable cluster →
      BoundaryCrossingWitness geometry carrier volume observable cluster

    rootedShellWeightBound : ∀ depth → Set
    supportDistanceEscapesWithVolume : ∀ observable depth → Set

    boundaryDifferenceBoundByRootedTail : ∀ volume observable → Set
    boundaryConditionIndependence : ∀ observable → Set

open BoundaryTailFromRootedShell public

rootedShellDecoderInjectivityLevel : ProofLevel
rootedShellDecoderInjectivityLevel = machineChecked

boundaryDistanceReductionLevel : ProofLevel
boundaryDistanceReductionLevel = machineChecked

physicalBoundaryCrossingGeometryInputsLevel : ProofLevel
physicalBoundaryCrossingGeometryInputsLevel = conditional

physicalRootedShellWeightInputsLevel : ProofLevel
physicalRootedShellWeightInputsLevel = conditional
