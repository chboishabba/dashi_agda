module DASHI.Geometry.HypervoxelAdicYoungFibonacciBridge where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)

record HypervoxelCarrier : Set₁ where
  field
    Cell Scale State : Set
    refine : Cell → Scale → Cell
    localState : Cell → State

open HypervoxelCarrier public

record AdicChart (p : Nat) : Set₁ where
  field
    Point Digit : Set
    valuation : Point → Nat
    residue : Point → Digit
    parent : Point → Point
    sameBallAt : Nat → Point → Point → Bool

open AdicChart public

record BTBraid {p : Nat} (A : AdicChart p) : Set₁ where
  field
    Strand : Set
    source target : Strand → AdicChart.Point A
    compose : Strand → Strand → Strand
    inverse : Strand → Strand
    valuationStep : Strand → Nat

open BTBraid public

data YoungFibonacciLetter : Set where
  one two : YoungFibonacciLetter

record YoungFibonacciGraph : Set₁ where
  field
    Vertex Edge : Set
    grade : Vertex → Nat
    source target : Edge → Vertex
    letter : Edge → YoungFibonacciLetter

open YoungFibonacciGraph public

decimalBase : Nat
decimalBase = 10

record TenAdicYoungFibonacciShadow
  (A : AdicChart decimalBase)
  (G : YoungFibonacciGraph) : Set₁ where
  field
    projectPoint : AdicChart.Point A → YoungFibonacciGraph.Vertex G
    projectStep : Σ (AdicChart.Point A) (λ _ → AdicChart.Point A) → YoungFibonacciGraph.Edge G
    gradeTracksValuation :
      (x : AdicChart.Point A) →
      YoungFibonacciGraph.grade G (projectPoint x) ≡ AdicChart.valuation A x

open TenAdicYoungFibonacciShadow public

data BridgeRelation : Set where
  projectedShadow embeddedChart definitionalIdentity : BridgeRelation

record HypervoxelAdicYoungFibonacciBridge
  (H : HypervoxelCarrier)
  (A : AdicChart decimalBase)
  (B : BTBraid A)
  (G : YoungFibonacciGraph)
  (S : TenAdicYoungFibonacciShadow A G) : Set₁ where
  field
    chartCell : HypervoxelCarrier.Cell H → AdicChart.Point A
    strandForRefine : HypervoxelCarrier.Cell H → HypervoxelCarrier.Scale H → BTBraid.Strand B
    strandStartsAtCell :
      (c : HypervoxelCarrier.Cell H) → (s : HypervoxelCarrier.Scale H) →
      BTBraid.source B (strandForRefine c s) ≡ chartCell c
    strandEndsAtRefinement :
      (c : HypervoxelCarrier.Cell H) → (s : HypervoxelCarrier.Scale H) →
      BTBraid.target B (strandForRefine c s) ≡ chartCell (HypervoxelCarrier.refine H c s)
    relation : BridgeRelation
    relation-is-projection : relation ≡ projectedShadow

open HypervoxelAdicYoungFibonacciBridge public

projectedBridge :
  ∀ {H A B G S}
  → (chartCell : HypervoxelCarrier.Cell H → AdicChart.Point A)
  → (strandForRefine : HypervoxelCarrier.Cell H → HypervoxelCarrier.Scale H → BTBraid.Strand B)
  → ((c : HypervoxelCarrier.Cell H) → (s : HypervoxelCarrier.Scale H) →
      BTBraid.source B (strandForRefine c s) ≡ chartCell c)
  → ((c : HypervoxelCarrier.Cell H) → (s : HypervoxelCarrier.Scale H) →
      BTBraid.target B (strandForRefine c s) ≡ chartCell (HypervoxelCarrier.refine H c s))
  → HypervoxelAdicYoungFibonacciBridge H A B G S
projectedBridge chartCell strandForRefine starts ends = record
  { chartCell = chartCell
  ; strandForRefine = strandForRefine
  ; strandStartsAtCell = starts
  ; strandEndsAtRefinement = ends
  ; relation = projectedShadow
  ; relation-is-projection = refl
  }

bridge-not-asserted-as-identity :
  ∀ {H A B G S} →
  (bridge : HypervoxelAdicYoungFibonacciBridge H A B G S) →
  HypervoxelAdicYoungFibonacciBridge.relation bridge ≡ projectedShadow
bridge-not-asserted-as-identity bridge =
  HypervoxelAdicYoungFibonacciBridge.relation-is-projection bridge
