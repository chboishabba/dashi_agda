module DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCompanionGramLedgerRound378Exact where

------------------------------------------------------------------------
-- ROUND378 / EXACT GLOBAL R227 COMPANION = CELL MASS + SIGNED GRAM DEBT
--
-- R180 owns the exact ledger on any finite vector list. R227's physical
-- companion is a finite output sum of squared norms of R224 folds of the same
-- R226 quadratic-kernel cells. The two folds are definitionally the same
-- recursion after mapping the cell function over the literal output fibre.
--
-- Therefore the global R227 companion admits an exact signed decomposition
-- before any estimate:
--
--   Q_companion(N,t) = globalCellMass(N,t) + globalGramDebt(N,t).
--
-- This is finite algebra only. It introduces no positivity assumption on the
-- Gram debt and no cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (map)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCompanionMassRound226Exact as R226
import DASHI.Physics.Closure.NSTriadKNMixedHelicityGlobalCompanionRound227Exact as R227
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180

F : C3.RealField _
F = Rational.rationalRealField

quadraticCells :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence →
  List (C3.Complex3 F)
quadraticCells E S velocity = map (R226.quadraticKernelCell E S velocity)

sumQuadraticCellsIsFold :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  R180.sumCells (quadraticCells E S velocity items)
  ≡ R224.foldVector (R226.quadraticKernelCell E S velocity) items
sumQuadraticCellsIsFold E S velocity [] = refl
sumQuadraticCellsIsFold E S velocity (tau ∷ rest) =
  cong (C3.complex3Add (R226.quadraticKernelCell E S velocity tau))
    (sumQuadraticCellsIsFold E S velocity rest)

outputCells :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Nat → Z3.FourierMode → List (C3.Complex3 F)
outputCells E S velocity cutoff output =
  quadraticCells E S velocity (Output.physicalOutputFiber cutoff output)

outputCellMass :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Nat → Z3.FourierMode → ℚ
outputCellMass E S velocity cutoff output =
  R180.cellMassSum (outputCells E S velocity cutoff output)

outputGramDebt :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Nat → Z3.FourierMode → ℚ
outputGramDebt E S velocity cutoff output =
  R180.gramDebt (outputCells E S velocity cutoff output)

outputCompanionGramLedger :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  R227.companionOutputMass E S velocity cutoff output
  ≡ outputCellMass E S velocity cutoff output
      + outputGramDebt E S velocity cutoff output
outputCompanionGramLedger E S velocity cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    cells = outputCells E S velocity cutoff output
    sameSum = sumQuadraticCellsIsFold E S velocity items
  in
  trans
    (cong L2.complex3NormSquared (sym sameSum))
    (R180.finiteFibreGramLedger cells)

globalCellMass :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Nat → List Z3.FourierMode → ℚ
globalCellMass E S velocity cutoff =
  R227.mapSum (outputCellMass E S velocity cutoff)

globalGramDebt :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Nat → List Z3.FourierMode → ℚ
globalGramDebt E S velocity cutoff =
  R227.mapSum (outputGramDebt E S velocity cutoff)

globalCompanionGramLedger :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (outputs : List Z3.FourierMode) →
  R227.globalCompanionMass E S velocity cutoff outputs
  ≡ globalCellMass E S velocity cutoff outputs
      + globalGramDebt E S velocity cutoff outputs
globalCompanionGramLedger E S velocity cutoff [] = solve []
globalCompanionGramLedger E S velocity cutoff (output ∷ outputs)
  rewrite outputCompanionGramLedger E S velocity cutoff output
        | globalCompanionGramLedger E S velocity cutoff outputs =
  solve
    ( outputCellMass E S velocity cutoff output
    ∷ outputGramDebt E S velocity cutoff output
    ∷ globalCellMass E S velocity cutoff outputs
    ∷ globalGramDebt E S velocity cutoff outputs
    ∷ [])

round378LiteralOutputFibreUsed : Bool
round378LiteralOutputFibreUsed = true

round378R227AndR180CellFoldsIdentifiedExactly : Bool
round378R227AndR180CellFoldsIdentifiedExactly = true

round378GlobalCompanionGramLedgerClosed : Bool
round378GlobalCompanionGramLedgerClosed = true

round378GramDebtKeptSigned : Bool
round378GramDebtKeptSigned = true

round378CardinalityFactorIntroduced : Bool
round378CardinalityFactorIntroduced = false

round378GlobalCompanionGramLedgerClosedIsTrue :
  round378GlobalCompanionGramLedgerClosed ≡ true
round378GlobalCompanionGramLedgerClosedIsTrue = refl
