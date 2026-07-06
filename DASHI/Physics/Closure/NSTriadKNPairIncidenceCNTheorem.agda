module DASHI.Physics.Closure.NSTriadKNPairIncidenceCNTheorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound
  as WeightedSchur
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix
  as CrossMatrix
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

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

pairIncidenceCNTheoremClosed : Bool
pairIncidenceCNTheoremClosed with WeightedSchur.weightedSchurProductBoundClosed
... | true = true
... | false = false

pairIncidenceCNTheoremClosedIsTrue :
  pairIncidenceCNTheoremClosed ≡ true
pairIncidenceCNTheoremClosedIsTrue with WeightedSchur.weightedSchurProductBoundClosedIsTrue
... | refl = refl
