module DASHI.Analysis.RiemannAristotleLiteralPostSchurCellRound180WeldExact where

------------------------------------------------------------------------
-- G1 BIDI CLOSURE: LITERAL RH THREE-TAPER CELL -> ROUND180 EXACT C^3 CELL
--
-- Backward requirement:
--   the finite near-core consumer needs the exact Round180 Gram ledger.
--
-- Forward source shape:
--   after choosing three tapers and applying the deterministic Schur map, one
--   zero/reflection-pair contribution is a REAL three-coordinate response.
--
-- Round180 works on rational Complex3.  Therefore the literal common carrier is
-- the zero-imaginary subcarrier
--
--     (a0 , a1 , a2)
--       |-> ((a0,0) , (a1,0) , (a2,0)).
--
-- We do NOT claim an equivalence with every Complex3 cell.  We prove the exact
-- embedding/retraction required by the RH real three-taper response and build
-- the existing RH->Round180 adapter definitionally.  Hence its three carrier
-- identification receipts are refl, and Round180 supplies the Gram identity
-- with no new RH-specific Gram theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Analysis.RiemannAristotleFiniteNearNSGramAdapterExact as Adapter

F = R179.F

------------------------------------------------------------------------
-- Literal post-Schur RH cell: one real response coordinate per taper.
------------------------------------------------------------------------

record RHPostSchurCell : Set where
  constructor rh-post-schur-cell
  field
    taper0 taper1 taper2 : ℚ

open RHPostSchurCell public

toRound180Cell : RHPostSchurCell → C3.Complex3 F
toRound180Cell c =
  C3.complex3
    (C3.complex (taper0 c) 0ℚ)
    (C3.complex (taper1 c) 0ℚ)
    (C3.complex (taper2 c) 0ℚ)

-- Forget only the imaginary coordinates.  On the literal RH image this is an
-- exact retraction; no quotient or approximation is involved.
fromRound180RealCoordinates : C3.Complex3 F → RHPostSchurCell
fromRound180RealCoordinates c =
  rh-post-schur-cell
    (C3.real (C3.x c))
    (C3.real (C3.y c))
    (C3.real (C3.z c))

fromToRound180Cell :
  (c : RHPostSchurCell) →
  fromRound180RealCoordinates (toRound180Cell c) ≡ c
fromToRound180Cell (rh-post-schur-cell a b c) = refl

toRound180CellTaper0 :
  (c : RHPostSchurCell) → C3.real (C3.x (toRound180Cell c)) ≡ taper0 c
toRound180CellTaper0 c = refl

toRound180CellTaper1 :
  (c : RHPostSchurCell) → C3.real (C3.y (toRound180Cell c)) ≡ taper1 c
toRound180CellTaper1 c = refl

toRound180CellTaper2 :
  (c : RHPostSchurCell) → C3.real (C3.z (toRound180Cell c)) ≡ taper2 c
toRound180CellTaper2 c = refl

toRound180CellImaginary0 :
  (c : RHPostSchurCell) → C3.imaginary (C3.x (toRound180Cell c)) ≡ 0ℚ
toRound180CellImaginary0 c = refl

toRound180CellImaginary1 :
  (c : RHPostSchurCell) → C3.imaginary (C3.y (toRound180Cell c)) ≡ 0ℚ
toRound180CellImaginary1 c = refl

toRound180CellImaginary2 :
  (c : RHPostSchurCell) → C3.imaginary (C3.z (toRound180Cell c)) ≡ 0ℚ
toRound180CellImaginary2 c = refl

rhCellsToRound180 : List RHPostSchurCell → List (C3.Complex3 F)
rhCellsToRound180 = map toRound180Cell

------------------------------------------------------------------------
-- Definitional construction of the pre-existing RH/Round180 adapter.
--
-- The scalar fields are not separately guessed: they are DEFINED to be the
-- Round180 total norm, cell-mass sum and signed Gram debt of the literal mapped
-- RH cells.  Therefore all three identification fields are refl.
------------------------------------------------------------------------

literalNearToRound180Carrier :
  Nat → List RHPostSchurCell → Adapter.LiteralNearToRound180Carrier
literalNearToRound180Carrier J rhCells =
  let cells = rhCellsToRound180 rhCells
  in record
    { cutoff = J
    ; cells = cells
    ; nearSchurSq = L2.complex3NormSquared (R180.sumCells cells)
    ; diagonalMass = R180.cellMassSum cells
    ; twiceCrossMass = R180.gramDebt cells
    ; nearSchurSqIsRound180Total = refl
    ; diagonalMassIsRound180CellMass = refl
    ; twiceCrossMassIsRound180GramDebt = refl
    }

literalRHFiniteGramIdentity :
  (J : Nat) → (rhCells : List RHPostSchurCell) →
  Adapter.nearSchurSq (literalNearToRound180Carrier J rhCells)
  ≡ Adapter.diagonalMass (literalNearToRound180Carrier J rhCells)
    + Adapter.twiceCrossMass (literalNearToRound180Carrier J rhCells)
literalRHFiniteGramIdentity J rhCells =
  Adapter.round180ExactGramIdentityOnLiteralNear
    (literalNearToRound180Carrier J rhCells)

------------------------------------------------------------------------
-- G1 status boundary.
------------------------------------------------------------------------

record LiteralPostSchurRound180WeldBoundary : Set where
  constructor literal-post-schur-round180-weld-boundary
  field
    rhCellHasExactlyThreeRealCoordinates : Bool
    rhCellHasExactlyThreeRealCoordinatesIsTrue :
      rhCellHasExactlyThreeRealCoordinates ≡ true

    round180EmbeddingUsesZeroImaginaryCoordinates : Bool
    round180EmbeddingUsesZeroImaginaryCoordinatesIsTrue :
      round180EmbeddingUsesZeroImaginaryCoordinates ≡ true

    embeddingRetractsExactlyOnRHCells : Bool
    embeddingRetractsExactlyOnRHCellsIsTrue :
      embeddingRetractsExactlyOnRHCells ≡ true

    literalRHToRound180CarrierWeldClosed : Bool
    literalRHToRound180CarrierWeldClosedIsTrue :
      literalRHToRound180CarrierWeldClosed ≡ true

    round180GramIdentityNowAutomatic : Bool
    round180GramIdentityNowAutomaticIsTrue :
      round180GramIdentityNowAutomatic ≡ true

    signedRHGramDebtEstimateClosed : Bool
    signedRHGramDebtEstimateClosedIsFalse :
      signedRHGramDebtEstimateClosed ≡ false

canonicalLiteralPostSchurRound180WeldBoundary :
  LiteralPostSchurRound180WeldBoundary
canonicalLiteralPostSchurRound180WeldBoundary =
  literal-post-schur-round180-weld-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
