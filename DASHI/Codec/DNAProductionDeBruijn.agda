module DASHI.Codec.DNAProductionDeBruijn where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Codec.DNAFirstFormalism using (Base)
open import DASHI.Codec.DNAProductionConstraints using
  ( ProductionState; initialState; legal?; IsTrue; step )
open import DASHI.Codec.DNAProductionChoices using
  ( legalBases; branchCount; length )

Vertex : Set
Vertex = ProductionState

record Edge (source : Vertex) (label : Base) (target : Vertex) : Set where
  constructor edge
  field
    legal : IsTrue (legal? source label)
    targetIsStep : target ≡ step source label
open Edge public

canonicalEdge :
  ∀ {s b} → IsTrue (legal? s b) → Edge s b (step s b)
canonicalEdge proof = edge proof refl

edge-target-determined :
  ∀ {s b t} → Edge s b t → t ≡ step s b
edge-target-determined e = targetIsStep e

infixr 5 _∷ʷ_
data LabelledWalk : Vertex → List Base → Vertex → Set where
  done : ∀ {s} → LabelledWalk s [] s
  _∷ʷ_ :
    ∀ {s b u bs t} →
    Edge s b u →
    LabelledWalk u bs t →
    LabelledWalk s (b ∷ bs) t

record Reachable (target : Vertex) : Set where
  constructor reachable
  field
    labels : List Base
    path : LabelledWalk initialState labels target
open Reachable public

outLabels : Vertex → List Base
outLabels = legalBases

outDegree : Vertex → Nat
outDegree s = length (outLabels s)

branchCount-is-outDegree : ∀ s → branchCount s ≡ outDegree s
branchCount-is-outDegree s = refl

record ProductionDeBruijnReceipt : Set where
  field
    vertex : Set
    initial : vertex
    outgoingLabels : vertex → List Base
    degree : vertex → Nat
    branchDegreeAgreement : ∀ s → branchCount s ≡ degree s

productionDeBruijnReceipt : ProductionDeBruijnReceipt
productionDeBruijnReceipt = record
  { vertex = Vertex
  ; initial = initialState
  ; outgoingLabels = outLabels
  ; degree = outDegree
  ; branchDegreeAgreement = branchCount-is-outDegree
  }
