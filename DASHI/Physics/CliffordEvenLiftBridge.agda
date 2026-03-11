module DASHI.Physics.CliffordEvenLiftBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
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

  Cl : Set
  Cl = D2C.UniversalClifford.Cl universal

  embed : V → Cl
  embed = D2C.UniversalClifford.embed universal

record Quadratic⇒Clifford : Set₂ where
  field
    build : (out : CQ.QuadraticOutput) → Clifford (CQ.V out) (CQ.Scalar out)

record EvenSubalgebra (Cl : Set) : Set₁ where
  field
    evenSubalg : Core.EvenSubalg Cl

  Even : Set
  Even = Core.EvenSubalg.Even evenSubalg

  incl : Even → Cl
  incl = Core.EvenSubalg.inc evenSubalg

record WaveLift⇒Even : Set₂ where
  field
    buildEven : ∀ {V Scalar} → (Cℓ : Clifford V Scalar) → EvenSubalgebra (Clifford.Cl Cℓ)
