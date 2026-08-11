module DASHI.Physics.Closure.NSTriadKNF4PairNormalizationRound39Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Round 38 exposed the last F4 normalization seam.  The repository's stored
-- `orderedPair` coefficient is *not* the conventional half-symmetrisation:
-- it is literally
--
--   Pair(tau) = Ordered(tau) + Ordered(swap tau).
--
-- Therefore the tempting pointwise statement Pair=Ordered on a diagonal
-- field is false in this convention: at a swap-fixed incidence Pair=2 Ordered.
--
-- This module resolves the factor exactly instead of hiding it.  Define
--
--   NormalizedPair = (1/2) Pair.
--
-- Then:
--
-- * at every swap-fixed incidence, NormalizedPair = Ordered;
-- * over the complete duplicate-free physical enumeration,
--
--     (1/2) sum Pair = sum Ordered,
--
--   because swap is an exact permutation (Round 38);
-- * hence the normalized pair fold vanishes whenever the already-proved raw
--   ordered incidence fold vanishes.
--
-- The remaining F4 theorem is now purely same-object: determine whether the
-- literal projected convection/energy pairing is represented by the raw
-- ordered fold or by this half-normalized pair fold under the chosen shell
-- enumeration.  No additional combinatorial cancellation is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as KFree
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as Round38

F : C3.RealField _
F = Round38.F

half : ℚ
half = Int.+ 1 / 2

swapFixedWhenInputsEqual :
  ∀ tau →
  Physical.p tau ≡ Physical.q tau →
  Symmetry.swapTriad tau ≡ tau
swapFixedWhenInputsEqual tau inputsEqual =
  KFree.physicalIncidenceExtPQ
    (Symmetry.swapTriad tau) tau
    (sym inputsEqual)
    inputsEqual

normalizedPairPower :
  (E : C3.IntegerEmbedding F) →
  C3.ModeInverseSquare F E →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) →
  ℚ
normalizedPairPower E I tau velocity =
  half * Round38.orderedPairPower E I tau velocity

swapFixedStoredPairIsDoubleOrdered :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.p tau ≡ Physical.q tau →
  Round38.orderedPairPower E I tau velocity
  ≡ Round38.orderedPower E I tau velocity
    + Round38.orderedPower E I tau velocity
swapFixedStoredPairIsDoubleOrdered E I tau velocity inputsEqual =
  trans
    (Round38.orderedPairPowerIsOrderedPlusSwap E I tau velocity)
    (cong
      (Round38.orderedPower E I tau velocity +_)
      (cong
        (λ selected → Round38.orderedPower E I selected velocity)
        (swapFixedWhenInputsEqual tau inputsEqual)))

normalizedPairEqualsOrderedAtSwapFixedIncidence :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.p tau ≡ Physical.q tau →
  normalizedPairPower E I tau velocity
  ≡ Round38.orderedPower E I tau velocity
normalizedPairEqualsOrderedAtSwapFixedIncidence
    E I tau velocity inputsEqual =
  trans
    (cong
      (half *_)
      (swapFixedStoredPairIsDoubleOrdered
        E I tau velocity inputsEqual))
    (solve (Round38.orderedPower E I tau velocity ∷ []))

normalizedPairFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → C3.Complex3 F) →
  Nat → ℚ
normalizedPairFold E I velocity cutoff =
  half * Round38.pairFold E I velocity
    (Physical.physicalTriadEnumeration cutoff)

normalizedPairFoldEqualsOrderedFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  normalizedPairFold E I velocity cutoff
  ≡ Round38.orderedFold E I velocity
      (Physical.physicalTriadEnumeration cutoff)
normalizedPairFoldEqualsOrderedFold E I velocity cutoff =
  let
    ordered = Round38.orderedFold E I velocity
      (Physical.physicalTriadEnumeration cutoff)
  in
  trans
    (cong
      (half *_)
      (Round38.pairFoldIsDoubleOrderedOnEnumeration
        E I velocity cutoff))
    (solve (ordered ∷ []))

normalizedPairFoldZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (cutoff : Nat) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  normalizedPairFold E I velocity cutoff ≡ 0ℚ
normalizedPairFoldZero E I cutoff velocity reality divergenceFree =
  trans
    (normalizedPairFoldEqualsOrderedFold E I velocity cutoff)
    (Round38.literalOrderedGalerkinIncidencePowerZero
      E I cutoff velocity reality divergenceFree)

f4PairNormalizationClosed : Bool
f4PairNormalizationClosed = true

storedOrderedPairHasNoHalfFactor : Bool
storedOrderedPairHasNoHalfFactor = true

literalConvectionPairingNormalizationIdentified : Bool
literalConvectionPairingNormalizationIdentified = false

f4PairNormalizationClosedIsTrue :
  f4PairNormalizationClosed ≡ true
f4PairNormalizationClosedIsTrue = refl

storedOrderedPairHasNoHalfFactorIsTrue :
  storedOrderedPairHasNoHalfFactor ≡ true
storedOrderedPairHasNoHalfFactorIsTrue = refl
