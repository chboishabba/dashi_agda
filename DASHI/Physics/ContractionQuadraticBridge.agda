module DASHI.Physics.ContractionQuadraticBridge where

open import Agda.Builtin.Equality using (_≡_)
open import Ultrametric as UMetric
open import Contraction as Contr using (StrictContraction)

record LyapunovWitness (V : Set) (Scalar : Set) (Q : V → Scalar) : Set₁ where
  field
    potential : V → Scalar
    potentialMatchesQuadratic : ∀ v → potential v ≡ Q v

record UniqueUpToScaleWitness (V : Set) (Scalar : Set) (Q : V → Scalar) : Set₁ where
  field
    referenceQuadratic : V → Scalar
    normalized : ∀ v → Q v ≡ referenceQuadratic v

-- Abstract quadratic output forced by contraction.
record QuadraticOutput : Set₁ where
  field
    V : Set
    Scalar : Set
    B : V → V → Scalar
    Q : V → Scalar
    Q-def : ∀ v → Q v ≡ B v v
    lyapunovWitness : LyapunovWitness V Scalar Q
    uniqueUpToScaleWitness : UniqueUpToScaleWitness V Scalar Q

open QuadraticOutput public

-- Bridge: strict contraction implies a quadratic output.
record Contraction⇒Quadratic
  {S : Set}
  (U : UMetric.Ultrametric S)
  (T : S → S)
  : Set₁ where
  field
    sc : StrictContraction U T
    out : QuadraticOutput

open Contraction⇒Quadratic public
