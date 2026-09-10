module DASHI.Physics.Closure.NSTriadKNSpectatorWeightedAmplitudeGramLedgerBidiExact where

------------------------------------------------------------------------
-- SPECTATOR-WEIGHTED MIXED AMPLITUDE -> EXACT GRAM LEDGER
--
-- R544 owns the literal spectator-weighted mixed-helicity amplitude cell.
-- R180 owns the exact finite identity
--
--   ||sum cells||^2 = cellMassSum cells + gramDebt cells.
--
-- This owner does only the same-object weld.  No estimate, modulus, shell
-- count, or cardinality factor is inserted.  In particular, the weighted
-- amplitude problem is reduced to:
--   (a) positive weighted cell mass, and
--   (b) signed weighted Gram debt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleCellAmplitudeFoldRound544Exact as R544

F : C3.RealField _
F = Rational.rationalRealField

module Ledger
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Spec = R541.Spectator physicalSystem S

  weightedAmplitudeCell :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    C3.Complex3 F
  weightedAmplitudeCell beta =
    let module A = R544.Fold physicalSystem S (Spec.spectatorWeight beta)
    in A.amplitude

  weightedAmplitudeCells :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence →
    List (C3.Complex3 F)
  weightedAmplitudeCells beta items = map (weightedAmplitudeCell beta) items

  sumCellsIsFold :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R180.sumCells (weightedAmplitudeCells beta items)
    ≡ R224.foldVector (weightedAmplitudeCell beta) items
  sumCellsIsFold beta [] = refl
  sumCellsIsFold beta (tau ∷ rest) =
    cong (C3.complex3Add (weightedAmplitudeCell beta tau))
      (sumCellsIsFold beta rest)

  exactWeightedAmplitudeGramLedger :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    L2.complex3NormSquared (R224.foldVector (weightedAmplitudeCell beta) items)
    ≡ R180.cellMassSum (weightedAmplitudeCells beta items)
      + R180.gramDebt (weightedAmplitudeCells beta items)
  exactWeightedAmplitudeGramLedger beta items =
    trans
      (cong L2.complex3NormSquared
        (symEq (sumCellsIsFold beta items)))
      (R180.finiteFibreGramLedger (weightedAmplitudeCells beta items))
    where
    symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    symEq refl = refl

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

weightedAmplitudeExactGramLedgerClosed : Bool
weightedAmplitudeExactGramLedgerClosed = true

weightedAmplitudeCellMassMajorantClosed : Bool
weightedAmplitudeCellMassMajorantClosed = false

weightedAmplitudeGramDebtPaid : Bool
weightedAmplitudeGramDebtPaid = false

weightedAmplitudeCardinalityTaxIntroduced : Bool
weightedAmplitudeCardinalityTaxIntroduced = false

clayPromotion : Bool
clayPromotion = false
