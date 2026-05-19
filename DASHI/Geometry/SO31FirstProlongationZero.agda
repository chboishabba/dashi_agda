module DASHI.Geometry.SO31FirstProlongationZero where

open import Agda.Primitive using (Level; Setω; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

------------------------------------------------------------------------
-- Matrix-free SO(3,1) first prolongation algebra.
--
-- A first-prolongation element can be represented abstractly by lowered
-- coefficients T i j k.  The torsion-free/prolongation slot is symmetric in
-- the last two indices, while the so(3,1) metric-preserving slot is skew in
-- the first two lowered indices.  These two laws force T to be zero by the
-- standard cyclic argument.  No real matrices or coordinates are used here.

data SO31Index : Set where
  time : SO31Index
  space-x : SO31Index
  space-y : SO31Index
  space-z : SO31Index

so31IndexList : List SO31Index
so31IndexList =
  time ∷ space-x ∷ space-y ∷ space-z ∷ []

record ZeroNegAlgebra (ℓ : Level) : Set (lsuc ℓ) where
  field
    Value :
      Set ℓ

    zero :
      Value

    neg :
      Value →
      Value

    neg-involutive :
      (x : Value) →
      neg (neg x) ≡ x

    self-negative-zero :
      {x : Value} →
      x ≡ neg x →
      x ≡ zero

record SO31FirstProlongationTensor
    {ℓ : Level}
    (A : ZeroNegAlgebra ℓ)
    : Set ℓ where
  open ZeroNegAlgebra A

  field
    coeff :
      SO31Index →
      SO31Index →
      SO31Index →
      Value

    lastPairSymmetric :
      (i j k : SO31Index) →
      coeff i j k
      ≡
      coeff i k j

    metricSkewLowered :
      (i j k : SO31Index) →
      coeff i j k
      ≡
      neg (coeff j i k)

so31FirstProlongationSelfNegative :
  {ℓ : Level} →
  {A : ZeroNegAlgebra ℓ} →
  (T : SO31FirstProlongationTensor A) →
  (i j k : SO31Index) →
  SO31FirstProlongationTensor.coeff T i j k
  ≡
  ZeroNegAlgebra.neg A (SO31FirstProlongationTensor.coeff T i j k)
so31FirstProlongationSelfNegative {A = A} T i j k =
  let
    open ZeroNegAlgebra A
    open SO31FirstProlongationTensor T
  in
  trans
    (lastPairSymmetric i j k)
    (trans
      (metricSkewLowered i k j)
      (trans
        (cong neg (lastPairSymmetric k i j))
        (trans
          (cong neg (metricSkewLowered k j i))
          (trans
            (neg-involutive (coeff j k i))
            (trans
              (lastPairSymmetric j k i)
              (metricSkewLowered j i k))))))

so31FirstProlongationZero :
  {ℓ : Level} →
  {A : ZeroNegAlgebra ℓ} →
  (T : SO31FirstProlongationTensor A) →
  (i j k : SO31Index) →
  SO31FirstProlongationTensor.coeff T i j k
  ≡
  ZeroNegAlgebra.zero A
so31FirstProlongationZero {A = A} T i j k =
  ZeroNegAlgebra.self-negative-zero A
    (so31FirstProlongationSelfNegative T i j k)

record SO31AbstractIndexCyclicComputation
    {ℓ : Level}
    (A : ZeroNegAlgebra ℓ)
    (T : SO31FirstProlongationTensor A)
    (i j k : SO31Index)
    : Set ℓ where
  open ZeroNegAlgebra A

  field
    loweredCoefficient :
      Value

    loweredCoefficient-v :
      loweredCoefficient
      ≡
      SO31FirstProlongationTensor.coeff T i j k

    cyclicSelfNegative :
      SO31FirstProlongationTensor.coeff T i j k
      ≡
      neg (SO31FirstProlongationTensor.coeff T i j k)

    forcedZero :
      SO31FirstProlongationTensor.coeff T i j k
      ≡
      zero

    matrixPrimitiveUsed :
      Bool

    matrixPrimitiveUsed-v :
      matrixPrimitiveUsed ≡ false

open SO31AbstractIndexCyclicComputation public

canonicalSO31AbstractIndexCyclicComputation :
  {ℓ : Level} →
  {A : ZeroNegAlgebra ℓ} →
  (T : SO31FirstProlongationTensor A) →
  (i j k : SO31Index) →
  SO31AbstractIndexCyclicComputation A T i j k
canonicalSO31AbstractIndexCyclicComputation {A = A} T i j k =
  record
    { loweredCoefficient =
        SO31FirstProlongationTensor.coeff T i j k
    ; loweredCoefficient-v =
        refl
    ; cyclicSelfNegative =
        so31FirstProlongationSelfNegative T i j k
    ; forcedZero =
        so31FirstProlongationZero T i j k
    ; matrixPrimitiveUsed =
        false
    ; matrixPrimitiveUsed-v =
        refl
    }

record SO31FirstProlongationZeroEvidence : Setω where
  field
    finiteIndexShape :
      String

    finiteIndexShape-v :
      finiteIndexShape
      ≡
      "four-abstract-Lorentz-indices-time-space-x-space-y-space-z"

    loweredTensorShape :
      String

    loweredTensorShape-v :
      loweredTensorShape
      ≡
      "T-i-j-k-last-pair-symmetric-and-first-pair-metric-skew"

    theoremName :
      String

    theoremName-v :
      theoremName
      ≡
      "so31FirstProlongationZero"

    cyclicComputationName :
      String

    cyclicComputationName-v :
      cyclicComputationName
      ≡
      "canonicalSO31AbstractIndexCyclicComputation"

    abstractIndexArgument :
      String

    abstractIndexArgument-v :
      abstractIndexArgument
      ≡
      "last-pair-symmetry-and-first-pair-metric-skew-cyclically-force-each-lowered-coefficient-to-be-self-negative"

    matrixPrimitiveUsed :
      Bool

    matrixPrimitiveUsed-v :
      matrixPrimitiveUsed ≡ false

    proofAvailable :
      Bool

    proofAvailable-v :
      proofAvailable ≡ true

    algebraicTheorem :
      {ℓ : Level} →
      {A : ZeroNegAlgebra ℓ} →
      (T : SO31FirstProlongationTensor A) →
      (i j k : SO31Index) →
      SO31FirstProlongationTensor.coeff T i j k
      ≡
      ZeroNegAlgebra.zero A

    cyclicComputation :
      {ℓ : Level} →
      {A : ZeroNegAlgebra ℓ} →
      (T : SO31FirstProlongationTensor A) →
      (i j k : SO31Index) →
      SO31AbstractIndexCyclicComputation A T i j k

open SO31FirstProlongationZeroEvidence public

canonicalSO31FirstProlongationZeroEvidence :
  SO31FirstProlongationZeroEvidence
canonicalSO31FirstProlongationZeroEvidence =
  record
    { finiteIndexShape =
        "four-abstract-Lorentz-indices-time-space-x-space-y-space-z"
    ; finiteIndexShape-v =
        refl
    ; loweredTensorShape =
        "T-i-j-k-last-pair-symmetric-and-first-pair-metric-skew"
    ; loweredTensorShape-v =
        refl
    ; theoremName =
        "so31FirstProlongationZero"
    ; theoremName-v =
        refl
    ; cyclicComputationName =
        "canonicalSO31AbstractIndexCyclicComputation"
    ; cyclicComputationName-v =
        refl
    ; abstractIndexArgument =
        "last-pair-symmetry-and-first-pair-metric-skew-cyclically-force-each-lowered-coefficient-to-be-self-negative"
    ; abstractIndexArgument-v =
        refl
    ; matrixPrimitiveUsed =
        false
    ; matrixPrimitiveUsed-v =
        refl
    ; proofAvailable =
        true
    ; proofAvailable-v =
        refl
    ; algebraicTheorem =
        so31FirstProlongationZero
    ; cyclicComputation =
        canonicalSO31AbstractIndexCyclicComputation
    }
