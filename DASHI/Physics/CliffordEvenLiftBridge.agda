module DASHI.Physics.CliffordEvenLiftBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool)
open import Data.Product using (Σ; _,_)
open import DASHI.Physics.ContractionQuadraticBridge as CQ

record Clifford (V : Set) (Scalar : Set) : Set₂ where
  field
    Q : V → Scalar
    Cl : Set
    mul : Cl → Cl → Cl
    one : Cl
    scalar : Scalar → Cl
    embed : V → Cl
    cliffordSquare :
      ∀ v →
        mul (embed v) (embed v) ≡ scalar (Q v)

pairedWord :
  ∀ {V Scalar : Set} →
  (Cℓ : Clifford V Scalar) → V → V → Clifford.Cl Cℓ
pairedWord Cℓ v w =
  Clifford.mul Cℓ
    (Clifford.embed Cℓ v)
    (Clifford.embed Cℓ w)

record Quadratic⇒Clifford : Set₂ where
  field
    build : (out : CQ.QuadraticOutput) → Clifford (CQ.V out) (CQ.Scalar out)
    quadraticCompatibility :
      ∀ out v →
        Clifford.Q (build out) v ≡ CQ.Q out v

record CliffordGrading (Cl : Set) : Set₁ where
  field
    parity : Cl → Bool
    evenClosedMul : Set
    oneEven : Set

record EvenSubalgebra (Cl : Set) : Set₁ where
  field
    Even : Set
    incl : Even → Cl
    closed : Set

record WaveLift (State Cl : Set) : Set₁ where
  field
    lift : State → Cl

record WaveLiftIntoEven {V Scalar : Set}
  (Cℓ : Clifford V Scalar) : Set₂ where
  field
    State : Set
    grading : CliffordGrading (Clifford.Cl Cℓ)
    Even : EvenSubalgebra (Clifford.Cl Cℓ)
    waveLift : WaveLift State (Clifford.Cl Cℓ)
    landsInEven :
      ∀ s →
      Σ (EvenSubalgebra.Even Even)
        (λ e → WaveLift.lift waveLift s ≡ EvenSubalgebra.incl Even e)

record WaveLift⇒Even : Set₂ where
  field
    build : ∀ {V Scalar} → (Cℓ : Clifford V Scalar) → WaveLiftIntoEven Cℓ
