module DASHI.Physics.Closure.NSTriadKNCompanionDebtDoubleMixedCarrierRound386Exact where

------------------------------------------------------------------------
-- ROUND386 / BIDI CARRIER CORRECTION: R378 DEBT -> DOUBLE-MIXED CELLS
--
-- The literal R378 Gram debt is built from R226.quadraticKernelCell, whereas
-- R380/R382 differentiate the plus-minus mixed cell.  The two are NOT
-- pointwise equal; the four-times plus-minus identity appears only after the
-- fixed-output swap sum.  Therefore the temporal weld must not silently replace
-- the R378 cell carrier by the plus-minus carrier.
--
-- R225 does provide the exact pointwise carrier relation
--
--   i * quadraticKernelCell(tau) = doubleMixedCell(tau).
--
-- Multiplying every cell by i preserves the real Hermitian pair Gram scalar.
-- Hence it preserves the entire recursive R180 Gram debt.  Combining these two
-- facts identifies the literal R378 output debt exactly with the R180 debt of
-- the pointwise double-mixed cells.  This is the correct temporal carrier for
-- the next tangent aggregation step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNGramDebtPairExpansionRound383Exact as R383
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCompanionGramLedgerRound378Exact as R378

F : C3.RealField _
F = Rational.rationalRealField

iScale : C3.Complex3 F → C3.Complex3 F
iScale value = C3.complex3Scale (C3.complexI F) value

pairGramIScaleBoth :
  (left right : C3.Complex3 F) →
  R383.pairGram (iScale left) (iScale right) ≡ R383.pairGram left right
pairGramIScaleBoth
    (C3.complex3
      (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci))
    (C3.complex3
      (C3.complex dr di) (C3.complex er ei) (C3.complex fr fi)) =
  solve (ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci ∷ dr ∷ di ∷ er ∷ ei ∷ fr ∷ fi ∷ [])

headPairSumIScale :
  (left : C3.Complex3 F) (rest : List (C3.Complex3 F)) →
  R383.headPairSum (iScale left) (map iScale rest)
  ≡ R383.headPairSum left rest
headPairSumIScale left [] = refl
headPairSumIScale left (right ∷ rest) =
  cong₂ _+_
    (pairGramIScaleBoth left right)
    (headPairSumIScale left rest)

allPairSumIScale :
  (cells : List (C3.Complex3 F)) →
  R383.allPairSum (map iScale cells) ≡ R383.allPairSum cells
allPairSumIScale [] = refl
allPairSumIScale (left ∷ rest) =
  cong₂ _+_
    (headPairSumIScale left rest)
    (allPairSumIScale rest)

gramDebtIScale :
  (cells : List (C3.Complex3 F)) →
  R180.gramDebt (map iScale cells) ≡ R180.gramDebt cells
gramDebtIScale cells =
  trans
    (R383.r180GramDebtIsAllPairSum (map iScale cells))
    (trans
      (allPairSumIScale cells)
      (sym (R383.r180GramDebtIsAllPairSum cells)))

mapPointwise :
  ∀ {A B : Set} (f g : A → B) →
  ((x : A) → f x ≡ g x) →
  (xs : List A) →
  map f xs ≡ map g xs
mapPointwise f g pointwise [] = refl
mapPointwise f g pointwise (x ∷ xs) =
  cong₂ _∷_ (pointwise x) (mapPointwise f g pointwise xs)

module OutputCarrier
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity) where

  iQuadraticCells : List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
  iQuadraticCells items = map (R225.iQuadraticKernelCell S velocity) items

  doubleMixedCells : List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
  doubleMixedCells items = map (R225.doubleMixedCell S velocity) items

  iQuadraticCellsAreIScaledQuadraticCells :
    (items : List Physical.PhysicalTriadIncidence) →
    iQuadraticCells items
    ≡ map iScale (R378.quadraticCells E S velocity items)
  iQuadraticCellsAreIScaledQuadraticCells [] = refl
  iQuadraticCellsAreIScaledQuadraticCells (tau ∷ rest) =
    cong
      (R225.iQuadraticKernelCell S velocity tau ∷_)
      (iQuadraticCellsAreIScaledQuadraticCells rest)

  iQuadraticCellsAreDoubleMixedCells :
    (items : List Physical.PhysicalTriadIncidence) →
    iQuadraticCells items ≡ doubleMixedCells items
  iQuadraticCellsAreDoubleMixedCells items =
    mapPointwise
      (R225.iQuadraticKernelCell S velocity)
      (R225.doubleMixedCell S velocity)
      (R225.iQuadraticKernelCellIsDoubleMixedCell P)
      items

  outputGramDebtIsDoubleMixedDebt :
    (cutoff : Nat) (output : Z3.FourierMode) →
    R378.outputGramDebt E S velocity cutoff output
    ≡ R180.gramDebt
        (doubleMixedCells (Output.physicalOutputFiber cutoff output))
  outputGramDebtIsDoubleMixedDebt cutoff output =
    let
      items = Output.physicalOutputFiber cutoff output
      quadratic = R378.quadraticCells E S velocity items
    in
    trans
      (sym (gramDebtIScale quadratic))
      (trans
        (cong R180.gramDebt
          (sym (iQuadraticCellsAreIScaledQuadraticCells items)))
        (cong R180.gramDebt (iQuadraticCellsAreDoubleMixedCells items)))

round386LiteralR378DebtCarrierIdentifiedAsDoubleMixed : Bool
round386LiteralR378DebtCarrierIdentifiedAsDoubleMixed = true

round386PlusMinusSubstitutionUsedPointwise : Bool
round386PlusMinusSubstitutionUsedPointwise = false

round386RemainingTemporalCellIsDoubleMixed : Bool
round386RemainingTemporalCellIsDoubleMixed = true

round386LiteralR378DebtCarrierIdentifiedAsDoubleMixedIsTrue :
  round386LiteralR378DebtCarrierIdentifiedAsDoubleMixed ≡ true
round386LiteralR378DebtCarrierIdentifiedAsDoubleMixedIsTrue = refl

round386PlusMinusSubstitutionUsedPointwiseIsFalse :
  round386PlusMinusSubstitutionUsedPointwise ≡ false
round386PlusMinusSubstitutionUsedPointwiseIsFalse = refl
