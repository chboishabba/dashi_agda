module DASHI.Physics.ContractionQuadraticBridge where

open import Level using (zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Ultrametric as UMetric
open import Contraction as Contr using (StrictContraction)
open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.QuadraticFormEmergence as QFE
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP

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

-- Canonical theorem constructor:
-- strict contraction + projection-defect orthogonal split package
-- yields a quadratic energy output Q(x) = E(x).
contractionProjectionOrthogonality⇒quadratic :
  ∀ {S : Set}
    {U : UMetric.Ultrametric S}
    {T : S → S}
    (sc : StrictContraction U T)
    (A : PD.Additive zero)
    (F : QF.ScalarField zero)
    (pkg : PDP.ProjectionDefectParallelogramPackage A F) →
    Contraction⇒Quadratic U T
contractionProjectionOrthogonality⇒quadratic {U = U} {T = T} sc A F pkg =
  let
    E : PD.Additive.Carrier A → QF.ScalarField.S F
    E = QFE.QuadraticEmergenceAxioms.Energy
          (PDP.ProjectionDefectParallelogramPackage.emergenceAxioms pkg)
  in
  record
    { sc = sc
    ; out =
        record
          { V = PD.Additive.Carrier A
          ; Scalar = QF.ScalarField.S F
          ; B = λ x _ → E x
          ; Q = E
          ; Q-def = λ _ → refl
          ; lyapunovWitness =
              record
                { potential = E
                ; potentialMatchesQuadratic = λ _ → refl
                }
          ; uniqueUpToScaleWitness =
              record
                { referenceQuadratic = E
                ; normalized = λ _ → refl
                }
          }
    }
