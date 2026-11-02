module DASHI.ComputerScience.QwenputerOneHotDeltaMatrixRefinementExact where

-- Mathematical source: Delta-rule fast-weight update.
-- Imanol Schlag, Kazuki Irie and Jürgen Schmidhuber (ICML 2021),
-- "Linear Transformers Are Secretly Fast Weight Programmers".
-- Qwenputer deployment motivation: Divyansh Agrawal (2026),
-- https://github.com/divagr18/qwenputer/blob/main/docs/q35.md
-- This is DASHI's exact abstract single-head algebraic refinement.
-- The operations and identities are supplied by a carrier witness.
-- This does NOT establish BF16/FP32 exactness of emitted Qwen weights.

open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.ComputerScience.QwenputerGatedDeltaArchitectureExact as RAM

record DeltaScalar : Set₁ where
  constructor deltaScalar
  field
    Scalar : Set
    zero : Scalar
    add : Scalar → Scalar → Scalar
    subtract : Scalar → Scalar → Scalar
    addZeroRight : (old : Scalar) → add old zero ≡ old
    replaceByDifference :
      (old new : Scalar) → add old (subtract new old) ≡ new
open DeltaScalar public

-- The Gated DeltaNet expression with alpha = beta = 1, a one-hot key
-- k_i, and per-column stored values S_{i,c}:
-- S'_{i,c} = S_{i,c} + k_i (v_c - S_{a,c}).
-- k_i is either one or zero. We implement its exact discrete action as
-- an explicit selected-address branch, not as floating-point arithmetic.

Matrix : DeltaScalar → Set → Set
Matrix D Column = RAM.Location → Column → Scalar D

Vector : DeltaScalar → Set → Set
Vector D Column = Column → Scalar D

oneHotMatrixUpdate :
  (D : DeltaScalar) {Column : Set} →
  Matrix D Column → RAM.Location → Vector D Column →
  Matrix D Column
oneHotMatrixUpdate D matrix selected value queried col
  with RAM.sameLocation selected queried
... | true =
  add D (matrix queried col) (subtract D (value col) (matrix queried col))
... | false =
  add D (matrix queried col) (zero D)

matrixSelectedOverwrite :
  (D : DeltaScalar) {Column : Set}
  (matrix : Matrix D Column) (address : RAM.Location)
  (value : Vector D Column) (col : Column) →
  oneHotMatrixUpdate D matrix address value address col ≡ value col
matrixSelectedOverwrite D matrix address value col
  rewrite RAM.sameLocationRefl address =
  replaceByDifference D (matrix address col) (value col)

matrixOtherPreserved :
  (D : DeltaScalar) {Column : Set}
  (matrix : Matrix D Column) (selected queried : RAM.Location)
  (value : Vector D Column) (col : Column) →
  RAM.sameLocation selected queried ≡ false →
  oneHotMatrixUpdate D matrix selected value queried col ≡
    matrix queried col
matrixOtherPreserved D matrix selected queried value col different
  rewrite different = addZeroRight D (matrix queried col)

matrixDataCannotChangeRegister :
  (D : DeltaScalar) {Column : Set}
  (matrix : Matrix D Column) (dataRow regRow : RAM.Row)
  (value : Vector D Column) (col : Column) →
  oneHotMatrixUpdate D matrix
    (RAM.location RAM.dataHead dataRow) value
    (RAM.location RAM.registerHead regRow) col
  ≡ matrix (RAM.location RAM.registerHead regRow) col
matrixDataCannotChangeRegister D matrix dataRow regRow value col =
  matrixOtherPreserved D matrix
    (RAM.location RAM.dataHead dataRow)
    (RAM.location RAM.registerHead regRow) value col
    (RAM.dataAndRegisterAreDifferent dataRow regRow)

-- A finite Boolean-XOR carrier independently instantiates the two
-- abstract difference identities, without any postulate.
-- It is a modular-two model, NOT the arithmetic of the real bf16 heads.
xor : Bool → Bool → Bool
xor false b = b
xor true false = true
xor true true = false

xorZero : (a : Bool) → xor a false ≡ a
xorZero false = refl
xorZero true = refl

xorReplaces :
  (old new : Bool) → xor old (xor new old) ≡ new
xorReplaces false false = refl
xorReplaces false true = refl
xorReplaces true false = refl
xorReplaces true true = refl

boolDeltaScalar : DeltaScalar
boolDeltaScalar =
  deltaScalar Bool false xor xor xorZero xorReplaces

boolOneHotSelected :
  {Column : Set} (matrix : Matrix boolDeltaScalar Column)
  (address : RAM.Location) (value : Vector boolDeltaScalar Column)
  (col : Column) →
  oneHotMatrixUpdate boolDeltaScalar matrix address value address col
    ≡ value col
boolOneHotSelected = matrixSelectedOverwrite boolDeltaScalar

-- Pointwise refinement with the existing scalar RAM owner. Because both
-- representations use exact branch selection, the result requires only
-- algebraic laws and a concrete read-after-write theorem.
refineMatrixWrite :
  (D : DeltaScalar) {Column : Set}
  (matrix : Matrix D Column) (selected : RAM.Location)
  (value : Vector D Column) (queried : RAM.Location) (col : Column) →
  oneHotMatrixUpdate D matrix selected value queried col
    ≡ RAM.writeRam
      (λ address → matrix address col) selected (value col) queried
refineMatrixWrite D matrix selected value queried col
  with RAM.sameLocation selected queried
... | true =
  replaceByDifference D (matrix queried col) (value col)
... | false =
  addZeroRight D (matrix queried col)

record NumericProofBoundary : Set where
  constructor numericProofBoundary
  field
    abstractDeltaAlgebraProved : Bool
    concreteModTwoInstanceProved : Bool
    realBF16CarrierInstantiated : Bool
    emittedQwenGDNWeightsVerified : Bool

numericBoundary : NumericProofBoundary
numericBoundary = numericProofBoundary true true false false
