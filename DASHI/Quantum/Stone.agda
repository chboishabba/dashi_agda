module DASHI.Quantum.Stone where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (Σ; _,_; _×_)

open import DASHI.Unifier using (ℝ; HilbertSpace; Tower; WaveLift; _+ℝ_; _-ℝ_ ; _≤ℝ_; _<ℝ_; maxℝ; toℝ)

absDiff : ℝ → ℝ → ℝ
absDiff x y = maxℝ (x -ℝ y) (y -ℝ x)

record StoneSelfAdjoint (HS : HilbertSpace) (K : HilbertSpace.H HS → HilbertSpace.H HS) : Set where
  open HilbertSpace HS public
  field
    symmetric :
      ∀ x y → ⟨ K x , y ⟩ ≡ ⟨ x , K y ⟩

record StoneGroup {Tow : Tower} {HS : HilbertSpace} (lift : WaveLift Tow HS) : Set₁ where
  field
    identity :
      ∀ x → WaveLift.U lift (toℝ 0) x ≡ x
    composition :
      ∀ s t x →
      WaveLift.U lift (s +ℝ t) x ≡ WaveLift.U lift s (WaveLift.U lift t x)

record StoneContinuity {S : Set} (U : ℝ → S → S) (dist : S → S → ℝ) : Set₁ where
  field
    continuity :
      ∀ x (ε : ℝ) →
      toℝ 0 <ℝ ε →
      Σ ℝ (λ δ →
        (toℝ 0 <ℝ δ)
        × (∀ {s t : ℝ} →
           absDiff s t <ℝ δ →
           dist (U s x) (U t x) <ℝ ε))

record StoneBundle (Tow : Tower) (HS : HilbertSpace) : Set₁ where
  open HilbertSpace HS public
  field
    lift : WaveLift Tow HS
    generator : H → H
    distance : H → H → ℝ
    self-adjoint : StoneSelfAdjoint HS generator
    stone-group : StoneGroup lift
    strong-continuity : StoneContinuity (WaveLift.U lift) distance

stone-unitary
  : ∀ {Tow HS}
  → StoneBundle Tow HS
  → ℝ → HilbertSpace.H HS → HilbertSpace.H HS
stone-unitary bundle = WaveLift.U (StoneBundle.lift bundle)

stone-distance
  : ∀ {Tow HS} (bundle : StoneBundle Tow HS)
  → HilbertSpace.H HS → HilbertSpace.H HS → ℝ
stone-distance bundle = StoneBundle.distance bundle

record StoneConsequences {Tow : Tower} {HS : HilbertSpace} (bundle : StoneBundle Tow HS) : Set₁ where
  field
    stone-group : StoneGroup (StoneBundle.lift bundle)
    strong-continuity : StoneContinuity (stone-unitary bundle) (stone-distance bundle)
    stone-self-adjoint : StoneSelfAdjoint HS (StoneBundle.generator bundle)

Stone-theorem
  : ∀ {Tow HS} (bundle : StoneBundle Tow HS)
  → StoneConsequences bundle
Stone-theorem bundle =
  record
    { stone-group = StoneBundle.stone-group bundle
    ; strong-continuity = StoneBundle.strong-continuity bundle
    ; stone-self-adjoint = StoneBundle.self-adjoint bundle
    }
