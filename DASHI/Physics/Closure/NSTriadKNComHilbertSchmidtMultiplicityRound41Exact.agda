module DASHI.Physics.Closure.NSTriadKNComHilbertSchmidtMultiplicityRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Roger A. Horn; Charles R. Johnson.
-- Title: "Matrix Analysis", second edition.
-- Cambridge University Press, 2013.
-- DOI: 10.1017/CBO9781139020411.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- DASHI CONTRIBUTION
--
-- The Round-40/41 one-channel reduction makes a Hilbert--Schmidt estimate an
-- attractive possible shortcut because operator norm is bounded by finite
-- Hilbert--Schmidt norm.  The shortcut is useful only if channel multiplicity
-- does not destroy cutoff uniformity.
--
-- This module installs the exact falsification gate.  If every retained
-- channel contributes at least a nonnegative floor f_i to its squared channel
-- mass h_i, then
--
--   sum_i f_i <= sum_i h_i = HS^2.
--
-- Consequently any proposed cutoff-uniform Hilbert--Schmidt bound must also
-- uniformly bound the accumulated multiplicity floor.  Adding a new channel
-- with a positive floor increases that compulsory mass by at least the chosen
-- witness.  No finite-rank/HS shortcut is accepted merely because every fixed
-- Galerkin matrix has finite rank.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

record HSChannelCell : Set where
  field
    channelSquare compulsoryFloor : ℚ
    channelSquareNonnegative : 0ℚ ≤ channelSquare
    compulsoryFloorNonnegative : 0ℚ ≤ compulsoryFloor
    compulsoryFloorBelowChannelSquare : compulsoryFloor ≤ channelSquare

open HSChannelCell public

hilbertSchmidtMass compulsoryMultiplicityFloor : List HSChannelCell → ℚ
hilbertSchmidtMass [] = 0ℚ
hilbertSchmidtMass (cell ∷ rest) =
  channelSquare cell + hilbertSchmidtMass rest

compulsoryMultiplicityFloor [] = 0ℚ
compulsoryMultiplicityFloor (cell ∷ rest) =
  compulsoryFloor cell + compulsoryMultiplicityFloor rest

multiplicityFloorBelowHilbertSchmidtMass :
  ∀ cells →
  compulsoryMultiplicityFloor cells ≤ hilbertSchmidtMass cells
multiplicityFloorBelowHilbertSchmidtMass [] = ℚP.≤-refl
multiplicityFloorBelowHilbertSchmidtMass (cell ∷ rest) =
  ℚP.+-mono-≤
    (compulsoryFloorBelowChannelSquare cell)
    (multiplicityFloorBelowHilbertSchmidtMass rest)

record CutoffUniformHSBudget (cells : List HSChannelCell) : Set where
  field
    uniformBudget : ℚ
    hilbertSchmidtBelowUniformBudget :
      hilbertSchmidtMass cells ≤ uniformBudget

open CutoffUniformHSBudget public

uniformHSBudgetForcesMultiplicityBudget :
  ∀ {cells} →
  (budget : CutoffUniformHSBudget cells) →
  compulsoryMultiplicityFloor cells ≤ uniformBudget budget
uniformHSBudgetForcesMultiplicityBudget {cells} budget =
  ℚP.≤-trans
    (multiplicityFloorBelowHilbertSchmidtMass cells)
    (hilbertSchmidtBelowUniformBudget budget)

addingChannelAddsCompulsoryFloorExactly :
  ∀ cell rest →
  compulsoryMultiplicityFloor (cell ∷ rest)
  ≡ compulsoryFloor cell + compulsoryMultiplicityFloor rest
addingChannelAddsCompulsoryFloorExactly cell rest = refl

record PositiveAddedChannel (cell : HSChannelCell) : Set where
  field
    positiveWitness : ℚ
    positiveWitnessBelowFloor : positiveWitness ≤ compulsoryFloor cell
    positiveWitnessNonnegative : 0ℚ ≤ positiveWitness

open PositiveAddedChannel public

addingPositiveChannelForcesAtLeastWitnessIncrease :
  ∀ {cell rest}
    (witness : PositiveAddedChannel cell) →
  positiveWitness witness + compulsoryMultiplicityFloor rest
  ≤ compulsoryMultiplicityFloor (cell ∷ rest)
addingPositiveChannelForcesAtLeastWitnessIncrease {cell} {rest} witness =
  ℚP.+-mono-≤
    (positiveWitnessBelowFloor witness)
    ℚP.≤-refl

comHilbertSchmidtMultiplicityGateClosed : Bool
comHilbertSchmidtMultiplicityGateClosed = true

physicalComHilbertSchmidtCutoffUniformConstructed : Bool
physicalComHilbertSchmidtCutoffUniformConstructed = false

comHilbertSchmidtMultiplicityGateClosedIsTrue :
  comHilbertSchmidtMultiplicityGateClosed ≡ true
comHilbertSchmidtMultiplicityGateClosedIsTrue = refl
