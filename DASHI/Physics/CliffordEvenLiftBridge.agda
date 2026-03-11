module DASHI.Physics.CliffordEvenLiftBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool)
open import Data.Product using (Σ; _,_)
open import DASHI.Physics.ContractionQuadraticBridge as CQ
open import DASHI.Physics.Core as Core
open import DASHI.Physics.DecimationToClifford as D2C

record Clifford (V : Set) (Scalar : Set) : Set₂ where
  field
    quadratic : Core.Quadratic V
    decimation : D2C.DecimationAlgebra V
    relations :
      D2C.CliffordRelations V quadratic decimation
    universal :
      D2C.UniversalClifford V quadratic
    mul : D2C.UniversalClifford.Cl universal →
          D2C.UniversalClifford.Cl universal →
          D2C.UniversalClifford.Cl universal
    pairedWord : V → V → D2C.UniversalClifford.Cl universal

  Cl : Set
  Cl = D2C.UniversalClifford.Cl universal

  embed : V → Cl
  embed = D2C.UniversalClifford.embed universal

record Quadratic⇒Clifford : Set₂ where
  field
    build : (out : CQ.QuadraticOutput) → Clifford (CQ.V out) (CQ.Scalar out)

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
