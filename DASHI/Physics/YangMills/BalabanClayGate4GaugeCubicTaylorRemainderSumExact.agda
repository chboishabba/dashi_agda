module DASHI.Physics.YangMills.BalabanClayGate4GaugeCubicTaylorRemainderSumExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Finite assembly of local cubic Taylor remainders.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Field Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Once the gauge-chart analysis supplies one uniform local bound
--
--   ||R_B|| <= (M_3/6) eta^3,
--
-- the polymer remainder is bounded by the number of owned cells times that
-- local budget. This finite summation is proved here rather than retained as
-- part of the Yang--Mills analytic input.
------------------------------------------------------------------------

record OrderedAdditiveNorm (Bound : Set) : Set₁ where
  field
    zero : Bound
    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

open OrderedAdditiveNorm public

finiteSum :
  ∀ {Bound} → OrderedAdditiveNorm Bound → List Bound → Bound
finiteSum algebra [] = zero algebra
finiteSum algebra (value ∷ values) =
  add algebra value (finiteSum algebra values)

natScale :
  ∀ {Bound} → OrderedAdditiveNorm Bound → Bound → Nat → Bound
natScale algebra value zero = zero algebra
natScale algebra value (suc count) =
  add algebra value (natScale algebra value count)

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ values) = suc (length values)

finitePointwiseBound :
  ∀ {Index Bound}
    (algebra : OrderedAdditiveNorm Bound)
    (indices : List Index)
    lower →
  (upper : Bound) →
  (∀ index → LessEqual algebra (lower index) upper) →
  LessEqual algebra
    (finiteSum algebra (mapList lower indices))
    (natScale algebra upper (length indices))
finitePointwiseBound algebra [] lower upper pointwise =
  reflexive algebra (zero algebra)
finitePointwiseBound algebra (index ∷ indices) lower upper pointwise =
  addMonotone algebra
    (pointwise index)
    (finitePointwiseBound algebra indices lower upper pointwise)

record GaugeCubicTaylorRemainderData
    (Cell Bound : Set) : Set₁ where
  field
    algebra : OrderedAdditiveNorm Bound
    ownedCells : List Cell
    localRemainderNorm : Cell → Bound
    localCubicBudget : Bound

    localCubicEstimate : ∀ cell →
      LessEqual algebra (localRemainderNorm cell) localCubicBudget

open GaugeCubicTaylorRemainderData public

polymerTaylorRemainderNorm :
  ∀ {Cell Bound} → GaugeCubicTaylorRemainderData Cell Bound → Bound
polymerTaylorRemainderNorm dataSet =
  finiteSum (algebra dataSet)
    (mapList (localRemainderNorm dataSet) (ownedCells dataSet))

polymerTaylorRemainderBelowCellCountBudget :
  ∀ {Cell Bound}
    (dataSet : GaugeCubicTaylorRemainderData Cell Bound) →
  LessEqual (algebra dataSet)
    (polymerTaylorRemainderNorm dataSet)
    (natScale (algebra dataSet)
      (localCubicBudget dataSet) (length (ownedCells dataSet)))
polymerTaylorRemainderBelowCellCountBudget dataSet =
  finitePointwiseBound (algebra dataSet)
    (ownedCells dataSet) (localRemainderNorm dataSet)
    (localCubicBudget dataSet) (localCubicEstimate dataSet)

gaugeCubicTaylorFiniteAssemblyLevel : ProofLevel
gaugeCubicTaylorFiniteAssemblyLevel = machineChecked

physicalGaugeLocalThirdDerivativeInputsLevel : ProofLevel
physicalGaugeLocalThirdDerivativeInputsLevel = conditional
