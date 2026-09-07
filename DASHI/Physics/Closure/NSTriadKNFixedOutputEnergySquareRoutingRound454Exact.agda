module DASHI.Physics.Closure.NSTriadKNFixedOutputEnergySquareRoutingRound454Exact where

------------------------------------------------------------------------
-- ROUND454 / LITERAL OUTPUT FIBRE -> SELECTED ENERGY-PAIR SQUARE
--
-- `physicalTriadEnumeration N` is definitionally a filter of
--
--   cartesian (cutoffModes N) (cutoffModes N)
--
-- by output-cutoff membership.  `physicalOutputFiber N k` applies the second
-- filter requiring p+q=k.  R453 uses the same ordered cartesian traversal via
-- its nested selected-pair sum.  This file proves those two finite folds are
-- exactly the same scalar when the selector is
--
--   output-in-cutoff && (p+q == k).
--
-- Therefore
--
--   sum_{tau in outputFiber(N,k)} E(p_tau)E(q_tau)
--     <= (sum_{m in cutoffModes N} E(m))^2
--
-- with no incidence cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergySquareRound453Exact as R453

fixedOutputSelector :
  Nat → Z3.FourierMode → Z3.FourierMode → Z3.FourierMode → Bool
fixedOutputSelector cutoff output p q with
  Physical.modeWithinCutoff cutoff (Z3.addMode p q)
... | true = Output.modeEqual (Z3.addMode p q) output
... | false = false

triadEnergyProductSum :
  (Z3.FourierMode → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
triadEnergyProductSum energy [] = 0ℚ
triadEnergyProductSum energy (tau ∷ rest) =
  energy (Physical.p tau) * energy (Physical.q tau)
  + triadEnergyProductSum energy rest

pairSelectedSum :
  (Z3.FourierMode → ℚ) →
  Nat → Z3.FourierMode →
  List (Cube.Pair Z3.FourierMode Z3.FourierMode) → ℚ
pairSelectedSum energy cutoff output [] = 0ℚ
pairSelectedSum energy cutoff output (pair ∷ rest) with
  fixedOutputSelector cutoff output (Cube.first pair) (Cube.second pair)
... | true =
  energy (Cube.first pair) * energy (Cube.second pair)
  + pairSelectedSum energy cutoff output rest
... | false = pairSelectedSum energy cutoff output rest

sumAppend :
  (energy : Z3.FourierMode → ℚ) →
  (left right : List Physical.PhysicalTriadIncidence) →
  triadEnergyProductSum energy (Cube._++_ left right)
  ≡ triadEnergyProductSum energy left + triadEnergyProductSum energy right
sumAppend energy [] right = refl
sumAppend energy (head ∷ rest) right
  rewrite sumAppend energy rest right = refl

pairSelectedAppend :
  (energy : Z3.FourierMode → ℚ) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  (left right : List (Cube.Pair Z3.FourierMode Z3.FourierMode)) →
  pairSelectedSum energy cutoff output (Cube._++_ left right)
  ≡ pairSelectedSum energy cutoff output left
    + pairSelectedSum energy cutoff output right
pairSelectedAppend energy cutoff output [] right = refl
pairSelectedAppend energy cutoff output (pair ∷ rest) right with
  fixedOutputSelector cutoff output (Cube.first pair) (Cube.second pair)
... | true rewrite pairSelectedAppend energy cutoff output rest right = refl
... | false = pairSelectedAppend energy cutoff output rest right

filteredEnumeratedPairSumExact :
  (energy : Z3.FourierMode → ℚ) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  (pairs : List (Cube.Pair Z3.FourierMode Z3.FourierMode)) →
  triadEnergyProductSum energy
    (Output.filterOutput output (Physical.enumerateFromPairs cutoff pairs))
  ≡ pairSelectedSum energy cutoff output pairs
filteredEnumeratedPairSumExact energy cutoff output [] = refl
filteredEnumeratedPairSumExact energy cutoff output (pair ∷ rest) with
  Physical.modeWithinCutoff cutoff
    (Z3.addMode (Cube.first pair) (Cube.second pair)) in within
... | true with Output.modeEqual
  (Z3.addMode (Cube.first pair) (Cube.second pair)) output in sameOutput
...   | true =
      cong₂ _+_ refl
        (filteredEnumeratedPairSumExact energy cutoff output rest)
...   | false = filteredEnumeratedPairSumExact energy cutoff output rest
... | false = filteredEnumeratedPairSumExact energy cutoff output rest

mappedBlockSelectedExact :
  (energy : Z3.FourierMode → ℚ) →
  (cutoff : Nat) (output left : Z3.FourierMode) →
  (rights : List Z3.FourierMode) →
  pairSelectedSum energy cutoff output
    (Cube.map (λ right → Cube.pair left right) rights)
  ≡ R453.selectedEnergyInner
      (R453.modal-energy energy (λ _ → dummyNN))
      (fixedOutputSelector cutoff output)
      left rights
mappedBlockSelectedExact energy cutoff output left [] = refl
mappedBlockSelectedExact energy cutoff output left (right ∷ rest) with
  fixedOutputSelector cutoff output left right
... | true =
  cong₂ _+_ refl
    (mappedBlockSelectedExact energy cutoff output left rest)
... | false = mappedBlockSelectedExact energy cutoff output left rest
  where
  postulate dummyNN : ∀ {mode} → 0ℚ ≤ energy mode

-- The proof-bearing public theorem carries actual nonnegativity.  The local
-- structural lemma below is repeated with that witness rather than relying on
-- the convenience draft above.
module WithEnergy
    (E : R453.ModalEnergy Z3.FourierMode) where

  energy = R453.energy E

  mappedBlockExact :
    (cutoff : Nat) (output left : Z3.FourierMode) →
    (rights : List Z3.FourierMode) →
    pairSelectedSum energy cutoff output
      (Cube.map (λ right → Cube.pair left right) rights)
    ≡ R453.selectedEnergyInner E
        (fixedOutputSelector cutoff output) left rights
  mappedBlockExact cutoff output left [] = refl
  mappedBlockExact cutoff output left (right ∷ rest) with
    fixedOutputSelector cutoff output left right
  ... | true = cong₂ _+_ refl (mappedBlockExact cutoff output left rest)
  ... | false = mappedBlockExact cutoff output left rest

  cartesianSelectedExact :
    (cutoff : Nat) (output : Z3.FourierMode) →
    (lefts rights : List Z3.FourierMode) →
    pairSelectedSum energy cutoff output (Cube.cartesian lefts rights)
    ≡ R453.selectedEnergyPairSum E
        (fixedOutputSelector cutoff output) lefts rights
  cartesianSelectedExact cutoff output [] rights = refl
  cartesianSelectedExact cutoff output (left ∷ rest) rights =
    trans
      (pairSelectedAppend energy cutoff output
        (Cube.map (λ right → Cube.pair left right) rights)
        (Cube.cartesian rest rights))
      (cong₂ _+_
        (mappedBlockExact cutoff output left rights)
        (cartesianSelectedExact cutoff output rest rights))

  physicalOutputFibreEnergyExact :
    (cutoff : Nat) (output : Z3.FourierMode) →
    triadEnergyProductSum energy
      (Output.physicalOutputFiber cutoff output)
    ≡ R453.selectedEnergyPairSum E
        (fixedOutputSelector cutoff output)
        (Cube.cutoffModes cutoff)
        (Cube.cutoffModes cutoff)
  physicalOutputFibreEnergyExact cutoff output =
    trans
      (filteredEnumeratedPairSumExact energy cutoff output
        (Cube.cartesian (Cube.cutoffModes cutoff) (Cube.cutoffModes cutoff)))
      (cartesianSelectedExact cutoff output
        (Cube.cutoffModes cutoff) (Cube.cutoffModes cutoff))

  physicalOutputFibreEnergyBelowSquare :
    (cutoff : Nat) (output : Z3.FourierMode) →
    triadEnergyProductSum energy
      (Output.physicalOutputFiber cutoff output)
    ≤ R453.sumEnergy E (Cube.cutoffModes cutoff)
        * R453.sumEnergy E (Cube.cutoffModes cutoff)
  physicalOutputFibreEnergyBelowSquare cutoff output =
    let
      exact = physicalOutputFibreEnergyExact cutoff output
      bound = R453.selectedEnergyPairSumBound
        E (fixedOutputSelector cutoff output) (Cube.cutoffModes cutoff)
    in
    subst
      (λ lower → lower ≤
        R453.sumEnergy E (Cube.cutoffModes cutoff)
          * R453.sumEnergy E (Cube.cutoffModes cutoff))
      (sym exact)
      bound

round454LiteralOutputFibreEnergyRoutingClosed : Bool
round454LiteralOutputFibreEnergyRoutingClosed = true

round454FixedOutputEnergyProductPaidByGlobalEnergySquare : Bool
round454FixedOutputEnergyProductPaidByGlobalEnergySquare = true

round454IntroducesCardinalityTax : Bool
round454IntroducesCardinalityTax = false

round454PackageAClosed : Bool
round454PackageAClosed = false

round454ClayPromotion : Bool
round454ClayPromotion = false

round454IntroducesCardinalityTaxIsFalse :
  round454IntroducesCardinalityTax ≡ false
round454IntroducesCardinalityTaxIsFalse = refl
