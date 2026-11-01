module DASHI.Examples.ConcreteInstances where

-- Minimal concrete witnesses for the parameterised bridge records.
-- These are toy models: finite/constant structures that satisfy the
-- required equalities without using postulates or metas.

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_ ; _+_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Properties using (≤-refl)

open import DASHI.Algebra.Clifford.UniversalProperty
open import DASHI.Algebra.Quantum.SpinFromEvenClifford
open import DASHI.Algebra.Quantum.UVFiniteness
open import DASHI.Geometry.Signature31AndDim3
open import DASHI.Quantum.AgreementDepth
open import DASHI.Quantum.AnomalyFreedom
open import DASHI.Quantum.Stone using (StoneBundle)
open import DASHI.Algebra.ConstraintAlgebraClosure using (ConstraintClosureBundle)
open import DASHI.Quantum.Stone using (StoneConsequences)
open import DASHI.Algebra.ConstraintAlgebraClosureTests renaming (DiracClosure to DiracClosureType)

------------------------------------------------------------------------
-- Clifford algebra toy instance
------------------------------------------------------------------------

toyCliffordData : CliffordData
toyCliffordData = record
  { V = Nat
  ; ℚ = Nat
  ; Q = λ _ → 0
  ; two = 2
  ; _*ℚ_ = _*_
  ; TAlg = Nat
  ; inj = λ v → v
  ; _·_ = λ _ _ → 0
  ; 1# = 0
  ; Ideal = ⊤
  ; I = tt
  ; Cl = Nat
  ; π = λ x → x
  ; _∙_ = λ _ _ → 0
  ; _+_ = _+_
  ; 1c = 0
  ; ι = λ v → v
  ; _•_ = λ q c → q * c
  ; cliff-rel = λ _ → refl
  ; ⟪_,_⟫ = λ _ _ → 0
  ; orth = λ _ _ → ⊤
  }

toyCliffordAxioms : CliffordAxioms toyCliffordData
toyCliffordAxioms = record
  { orth-anticomm = λ _ _ _ → refl }

-- Universal property witness: identity lift suffices because inj = id.
toyCliffordUP : CliffordUP toyCliffordData
toyCliffordUP = record
  { universal = λ ιA _∘_ 1A _•A_ _ →
      (λ t → ιA t) , (λ _ → refl) }

------------------------------------------------------------------------
-- Spin double cover toy instance
------------------------------------------------------------------------

toySpinData : SpinData
toySpinData = record
  { SO = λ _ _ → ⊤
  ; Cl⁰ = ⊤
  ; Spin = ⊤
  ; toSO = λ _ → tt
  ; kernel±1 = ⊤
  ; identitySO = tt
  }

toySpinCover : SpinDoubleCover toySpinData
toySpinCover =
  spinDoubleCover-witness toySpinData
    (λ _ → ⊤)
    (λ _ _ _ → tt)
    (λ g → tt , refl)

------------------------------------------------------------------------
-- UV finiteness toy instance
------------------------------------------------------------------------

toyUVBounded : UVBounded
toyUVBounded = record
  { L = Nat
  ; dimH = λ _ → 0
  ; bound = λ _ → 0
  ; dimH≤bound = λ _ → ≤-refl
  }

toyUVFinite : UVFinite toyUVBounded
toyUVFinite = uvFiniteness toyUVBounded

------------------------------------------------------------------------
-- Signature (3,1) and dim=3 toy instance
------------------------------------------------------------------------

toyLorentzData : LorentzData
toyLorentzData = record
  { QuadraticForm = ⊤
  ; Signature = Nat
  ; sig31 = 4
  ; sig = λ _ → 4
  ; Cone = ⊤
  ; coneOf = λ _ → tt
  }

toyCausalAxioms : CausalAxioms toyLorentzData
toyCausalAxioms = record
  { isotropy = λ _ → ⊤
  ; finiteSpeed = λ _ → ⊤
  ; convex = λ _ → ⊤
  ; nondeg = λ _ → ⊤
  ; cone-determines-Q = λ _ _ _ → refl
  }

toySignatureUniqueness : SignatureUniqueness toyCausalAxioms
toySignatureUniqueness _ _ _ _ _ = refl

toyDim3Witness : Dim3Witness toyLorentzData
toyDim3Witness = record { dim3 = ⊤ }

toyLorentzClosure : LorentzDimClosure toyCausalAxioms
toyLorentzClosure = mkLorentzDimClosure toyCausalAxioms toySignatureUniqueness toyDim3Witness

------------------------------------------------------------------------
-- Anomaly bundle helper: zero anomalies
------------------------------------------------------------------------

makeZeroAnomalyBundle :
  ∀ {Tow HS} ->
  StoneBundle Tow HS ->
  AgreementDepthBundle ->
  ConstraintClosureBundle ->
  AnomalyBundle Tow HS
makeZeroAnomalyBundle st agr con =
  record
    { stone = st
    ; agreement = agr
    ; constraint = con
    ; anomalyCarrier = Nat
    ; zero = 0
    ; cubic = 0
    ; mixed = 0
    ; cancel-cubic = refl
    ; cancel-mixed = refl
    }
