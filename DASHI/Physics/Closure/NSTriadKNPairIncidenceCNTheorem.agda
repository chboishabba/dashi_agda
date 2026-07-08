module DASHI.Physics.Closure.NSTriadKNPairIncidenceCNTheorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_; z≤n)

import DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound
  as WeightedSchur
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix
  as CrossMatrix
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using (Shell)
open import DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound
  using ( NSTriadKNWeightedSchurProductBoundModel
        ; operatorNorm
        ; operatorNormTarget
        )

------------------------------------------------------------------------
-- Exact scripted pair-incidence C/N operator theorem surface.
--
-- This is the first theorem after the global weighted Schur product bound:
--
--   R_N(w_N) * C_N(w_N) <= C^2 / N^2
--     => ||L_FT,script^N||_op <= C / N.

record NSTriadKNPairIncidenceCNTheoremModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    weightedSchurModel :
      NSTriadKNWeightedSchurProductBoundModel {ℓS} {ℓE} {ℓV} {ℓR}

    pairIncidenceOperatorCNBound :
      (N : Shell (WeightedSchur.weightedDecompositionModel weightedSchurModel)) ->
      CrossMatrix._≤_ (WeightedSchur.profileMatrixModel weightedSchurModel)
        (operatorNorm weightedSchurModel N)
        (operatorNormTarget weightedSchurModel N)

open NSTriadKNPairIncidenceCNTheoremModel public

cnDecompositionModel :
  ∀ {ℓS ℓE ℓV ℓR} ->
  NSTriadKNPairIncidenceCNTheoremModel {ℓS} {ℓE} {ℓV} {ℓR} ->
  _
cnDecompositionModel m =
  WeightedSchur.weightedDecompositionModel (weightedSchurModel m)

weightedSchurImpliesOperatorCN :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNPairIncidenceCNTheoremModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  (N : Shell (cnDecompositionModel m)) ->
  CrossMatrix._≤_ (WeightedSchur.profileMatrixModel (weightedSchurModel m))
    (operatorNorm (weightedSchurModel m) N)
    (operatorNormTarget (weightedSchurModel m) N)
weightedSchurImpliesOperatorCN m =
  pairIncidenceOperatorCNBound m

------------------------------------------------------------------------
-- Norm-regime audit surfaces.
--
-- The weighted Schur theorem naturally controls a weighted operator norm.
-- Any later use as an unweighted C/N theorem must pass through an explicit
-- norm-transfer witness rather than silently changing norm regimes.

record WeightedOperatorCNBound : Set₁ where
  field
    weightedOperatorBoundWitness : Set

record UnweightedOperatorCNBound : Set₁ where
  field
    unweightedOperatorBoundWitness : Set

record WeightNormEquivalence : Set₁ where
  field
    weightedToUnweightedWitness : Set

record PairIncidenceNormTransfer : Set₁ where
  field
    weightedBound : WeightedOperatorCNBound
    normEquivalence : WeightNormEquivalence
    unweightedBound : UnweightedOperatorCNBound

------------------------------------------------------------------------
-- Proof-derived gate definitions.

pairIncidenceCNTheoremClosed : Bool
pairIncidenceCNTheoremClosed with WeightedSchur.weightedSchurProductBoundClosed
... | true = true
... | false = false

pairIncidenceCNTheoremClosedIsTrue :
  pairIncidenceCNTheoremClosed ≡ true
pairIncidenceCNTheoremClosedIsTrue with WeightedSchur.weightedSchurProductBoundClosedIsTrue
... | refl = refl

------------------------------------------------------------------------
-- Upstream operator witness surface.
--
-- Blocker 2 needs the actual pair-incidence operator and weak quadratic form
-- carried at the same theorem boundary as PairIncidence C/N. The current Stage
-- 3 files close only an operator-norm receipt; they do not yet expose the
-- operator, the pairing, or the quadratic form that the weak-error lane must
-- control. This record is the minimal witness package needed to make that
-- operator concrete.

record PairIncidenceOperatorWitness
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkPairIncidenceOperatorWitness
  field
    pairIncidenceCNWitness :
      pairIncidenceCNTheoremClosed ≡ true

    pairIncidenceOperator :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex

    absWeakPairing :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex →
      Nat

    absQuadraticForm :
      ResidueNorm.Carrier residueNormModel shellIndex → Nat

    weakQuadraticFormConstant : Nat

    absQuadraticFormDef :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      absQuadraticForm x
        ≡
        absWeakPairing (pairIncidenceOperator x) x

    operatorNormControlsQuadratic :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      absQuadraticForm x
        ≤
        weakQuadraticFormConstant
          * ResidueNorm.weakNormSquared residueNormModel shellIndex x

    witnessClosed : Bool

------------------------------------------------------------------------
-- Exact next Blocker 2A target.
--
-- The active weak-quadratic-form consumer currently works at shellIndex = 1.
-- This alias names the first real missing object on the live chain:
--
--   PairIncidence C/N receipt
--     + concrete operator/pairing/quadratic-form witness at shell 1
--     => weak quadratic-form control target.
--
-- The current repo still exposes only receipt/readout authority for the exact
-- scripted operator, not a typed inhabitant of this witness. Keep the gate
-- fail-closed until the operator object itself is constructed.

UnitShellPairIncidenceOperatorWitnessTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) → Set₁
UnitShellPairIncidenceOperatorWitnessTarget residueNormModel =
  PairIncidenceOperatorWitness residueNormModel (suc zero)

modelUnitShellPairIncidenceOperatorWitness :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  UnitShellPairIncidenceOperatorWitnessTarget residueNormModel
modelUnitShellPairIncidenceOperatorWitness residueNormModel =
  mkPairIncidenceOperatorWitness
    pairIncidenceCNTheoremClosedIsTrue
    (λ x → x)
    (λ x y → zero)
    (λ x → zero)
    zero
    (λ x → refl)
    (λ x → z≤n)
    false

unitShellPairIncidenceOperatorWitness :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  UnitShellPairIncidenceOperatorWitnessTarget residueNormModel
unitShellPairIncidenceOperatorWitness =
  modelUnitShellPairIncidenceOperatorWitness

------------------------------------------------------------------------
-- The live missing object is not the model witness above, but an actual
-- witness for the exact Stage 3 operator controlled by weighted Schur.
-- Keep that requirement explicit and fail-closed.

record Stage3PairIncidenceOperatorWitness
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkStage3PairIncidenceOperatorWitness
  field
    weightedSchurWitness :
      WeightedSchur.WeightedSchurOperatorWitness residueNormModel shellIndex

    operatorWitness :
      PairIncidenceOperatorWitness residueNormModel shellIndex

    sameOperatorAsWeightedSchur :
      PairIncidenceOperatorWitness.pairIncidenceOperator operatorWitness
        ≡
        WeightedSchur.WeightedSchurOperatorWitness.weightedSchurOperator
          weightedSchurWitness

open Stage3PairIncidenceOperatorWitness public

stage3ToPairIncidenceOperatorWitness :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  {shellIndex : Nat} →
  Stage3PairIncidenceOperatorWitness residueNormModel shellIndex →
  PairIncidenceOperatorWitness residueNormModel shellIndex
stage3ToPairIncidenceOperatorWitness =
  Stage3PairIncidenceOperatorWitness.operatorWitness

ActualUnitShellPairIncidenceOperatorWitnessTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) → Set₁
ActualUnitShellPairIncidenceOperatorWitnessTarget residueNormModel =
  Stage3PairIncidenceOperatorWitness residueNormModel (suc zero)

pairIncidenceOperatorWitnessClosed : Bool
pairIncidenceOperatorWitnessClosed = false

pairIncidenceOperatorWitnessClosedIsFalse :
  pairIncidenceOperatorWitnessClosed ≡ false
pairIncidenceOperatorWitnessClosedIsFalse = refl

actualUnitShellPairIncidenceOperatorWitnessClosed : Bool
actualUnitShellPairIncidenceOperatorWitnessClosed =
  WeightedSchur.actualUnitShellWeightedSchurOperatorWitnessClosed

actualUnitShellPairIncidenceOperatorWitnessClosedIsFalse :
  actualUnitShellPairIncidenceOperatorWitnessClosed ≡ false
actualUnitShellPairIncidenceOperatorWitnessClosedIsFalse = refl

actualPairIncidenceOperatorExposed : Bool
actualPairIncidenceOperatorExposed =
  WeightedSchur.actualUnitShellWeightedSchurOperatorWitnessClosed

actualPairIncidenceOperatorExposedIsFalse :
  actualPairIncidenceOperatorExposed ≡ false
actualPairIncidenceOperatorExposedIsFalse = refl

unitShellWitnessMatchesStage3OperatorClosed : Bool
unitShellWitnessMatchesStage3OperatorClosed =
  WeightedSchur.actualUnitShellWeightedSchurOperatorWitnessClosed

unitShellWitnessMatchesStage3OperatorClosedIsFalse :
  unitShellWitnessMatchesStage3OperatorClosed ≡ false
unitShellWitnessMatchesStage3OperatorClosedIsFalse = refl
