module DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier where

open import Agda.Primitive using (Level; lsuc)
open import Data.Integer.Base using (ℤ)

open import DASHI.Physics.Closure.NSIntegerFourierLattice
open import DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel

------------------------------------------------------------------------
-- Exact scalar algebra and concrete three-component vectors.
------------------------------------------------------------------------

record ExactScalarAlgebra {s : Level} (Scalar : Set s) : Set (lsuc s) where
  field
    zero one : Scalar
    add subtract multiply : Scalar → Scalar → Scalar
    negate : Scalar → Scalar
    order : Scalar → Scalar → Set s
    integerEmbed : ℤ → Scalar

open ExactScalarAlgebra public

record Vec3 {s : Level} (Scalar : Set s) : Set s where
  constructor vec3
  field
    x y z : Scalar

open Vec3 public

vecZero :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar →
  Vec3 Scalar
vecZero A = vec3 (zero A) (zero A) (zero A)

vecAdd :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar →
  Vec3 Scalar → Vec3 Scalar → Vec3 Scalar
vecAdd A u v = vec3
  (add A (x u) (x v))
  (add A (y u) (y v))
  (add A (z u) (z v))

vecSubtract :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar →
  Vec3 Scalar → Vec3 Scalar → Vec3 Scalar
vecSubtract A u v = vec3
  (subtract A (x u) (x v))
  (subtract A (y u) (y v))
  (subtract A (z u) (z v))

vecScale :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar →
  Scalar → Vec3 Scalar → Vec3 Scalar
vecScale A a u = vec3
  (multiply A a (x u))
  (multiply A a (y u))
  (multiply A a (z u))

vecDot :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar →
  Vec3 Scalar → Vec3 Scalar → Scalar
vecDot A u v =
  add A
    (multiply A (x u) (x v))
    (add A
      (multiply A (y u) (y v))
      (multiply A (z u) (z v)))

vecCross :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar →
  Vec3 Scalar → Vec3 Scalar → Vec3 Scalar
vecCross A u v = vec3
  (subtract A
    (multiply A (y u) (z v))
    (multiply A (z u) (y v)))
  (subtract A
    (multiply A (z u) (x v))
    (multiply A (x u) (z v)))
  (subtract A
    (multiply A (x u) (y v))
    (multiply A (y u) (x v)))

integerWaveVector :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar →
  FourierMode → Vec3 Scalar
integerWaveVector A k = vec3
  (integerEmbed A (kx k))
  (integerEmbed A (ky k))
  (integerEmbed A (kz k))

record ExactFourierEvaluation
    {s : Level}
    (Scalar : Set s)
    (A : ExactScalarAlgebra Scalar) : Set (lsuc s) where
  field
    inverseNormSquared : FourierMode → Scalar
    modeDelta : FourierMode → FourierMode → Scalar
    vectorMajorant : Vec3 Scalar → Scalar

open ExactFourierEvaluation public

exactFourierVectorLaws :
  ∀ {s}
    {Scalar : Set s}
    (A : ExactScalarAlgebra Scalar) →
  ExactFourierEvaluation Scalar A →
  FourierVectorLaws FourierMode (Vec3 Scalar) Scalar
exactFourierVectorLaws A E = record
  { scalarZero = zero A
  ; scalarAdd = add A
  ; scalarMultiply = multiply A
  ; scalarOrder = order A
  ; vectorZero = vecZero A
  ; vectorAdd = vecAdd A
  ; vectorSubtract = vecSubtract A
  ; vectorScale = vecScale A
  ; vectorDot = vecDot A
  ; vectorCross = vecCross A
  ; waveVector = integerWaveVector A
  ; inverseNormSquared = inverseNormSquared E
  ; modeDelta = modeDelta E
  ; vectorMajorant = vectorMajorant E
  }
