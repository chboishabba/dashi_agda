module DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact where

------------------------------------------------------------------------
-- ROUND181 / PARTNER-BLOCK GRAM LEDGER
--
-- The physical output fibre already has an exact partner involution.  The
-- important order of operations is therefore
--
--   pair first -> replace each pair by its commutator cell -> sum pairs.
--
-- This file proves the generic Hilbert-algebra bookkeeping behind that move.
-- For a finite list of partner blocks (u_i,v_i),
--
--   ||sum_i (u_i+v_i)||^2
--     = sum_i (||u_i||^2+||v_i||^2)
--       + internalPartnerDebt
--       + betweenPartnerDebt.
--
-- Equivalently, after the exact partner identity has been used, all internal
-- pair interference is already contained in ||u_i+v_i||^2.  The ONLY global
-- obstruction left is the Gram debt BETWEEN partner-compressed cells.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180

F = R179.F

record CellPair : Set where
  constructor cell-pair
  field
    left right : C3.Complex3 F

open CellPair public

pairCell : CellPair → C3.Complex3 F
pairCell pair = C3.complex3Add (left pair) (right pair)

pairCells : List CellPair → List (C3.Complex3 F)
pairCells [] = []
pairCells (pair ∷ pairs) = pairCell pair ∷ pairCells pairs

individualPairMass : CellPair → ℚ
individualPairMass pair =
  L2.complex3NormSquared (left pair)
  + L2.complex3NormSquared (right pair)

internalPairDebt : CellPair → ℚ
internalPairDebt pair =
  R179.two * R179.realHermitianCross (left pair) (right pair)

individualMassSum : List CellPair → ℚ
individualMassSum [] = 0ℚ
individualMassSum (pair ∷ pairs) =
  individualPairMass pair + individualMassSum pairs

internalPartnerDebt : List CellPair → ℚ
internalPartnerDebt [] = 0ℚ
internalPartnerDebt (pair ∷ pairs) =
  internalPairDebt pair + internalPartnerDebt pairs

pairMassIdentity :
  (pair : CellPair) →
  L2.complex3NormSquared (pairCell pair)
  ≡ individualPairMass pair + internalPairDebt pair
pairMassIdentity pair = R179.complex3Polarization (left pair) (right pair)

pairCellMassSumIdentity :
  (pairs : List CellPair) →
  R180.cellMassSum (pairCells pairs)
  ≡ individualMassSum pairs + internalPartnerDebt pairs
pairCellMassSumIdentity [] = refl
pairCellMassSumIdentity (pair ∷ pairs)
  rewrite pairMassIdentity pair
        | pairCellMassSumIdentity pairs =
  solve
    ( individualPairMass pair
    ∷ internalPairDebt pair
    ∷ individualMassSum pairs
    ∷ internalPartnerDebt pairs
    ∷ [])

betweenPartnerDebt : List CellPair → ℚ
betweenPartnerDebt pairs = R180.gramDebt (pairCells pairs)

partnerBlockGramLedger :
  (pairs : List CellPair) →
  L2.complex3NormSquared (R180.sumCells (pairCells pairs))
  ≡ individualMassSum pairs
    + internalPartnerDebt pairs
    + betweenPartnerDebt pairs
partnerBlockGramLedger pairs
  rewrite R180.finiteFibreGramLedger (pairCells pairs)
        | pairCellMassSumIdentity pairs =
  solve
    ( individualMassSum pairs
    ∷ internalPartnerDebt pairs
    ∷ betweenPartnerDebt pairs
    ∷ [])

-- This is the cleaner form for the physical application: after partner
-- compression, forget the two raw cells entirely and keep only their exact
-- commutator sum.  The global price is then precisely the between-block debt.
compressedPartnerGramLedger :
  (pairs : List CellPair) →
  L2.complex3NormSquared (R180.sumCells (pairCells pairs))
  ≡ R180.cellMassSum (pairCells pairs) + betweenPartnerDebt pairs
compressedPartnerGramLedger pairs = R180.finiteFibreGramLedger (pairCells pairs)

round181PartnerInternalDebtSeparated : Bool
round181PartnerInternalDebtSeparated = true

round181OnlyBetweenPartnerGramDebtRemainsAfterCompression : Bool
round181OnlyBetweenPartnerGramDebtRemainsAfterCompression = true

round181PhysicalBetweenPartnerPaymentClosed : Bool
round181PhysicalBetweenPartnerPaymentClosed = false

round181PackageAClosed : Bool
round181PackageAClosed = false

round181ClayPromotion : Bool
round181ClayPromotion = false
