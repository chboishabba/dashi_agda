module DASHI.Analysis.RiemannAristotleFiniteNearNSGramAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Analysis.RiemannAristotleFiniteNearGramCancellationCompilerExact as RHGram

------------------------------------------------------------------------
-- BIDI CROSS-LANE REUSE
--
-- Round180 already owns the exact finite Gram telescope
--
--   ||sum cells||^2 = cellMassSum cells + gramDebt cells
--
-- on the repository's exact three-component carrier, with `gramDebt` retaining
-- all signed cross interactions.  Therefore RH does not need a new finite Gram
-- theorem if the literal three-taper post-Schur near contributions are welded to
-- this same exact carrier.
--
-- The only new RH-specific object here is that carrier identification.
------------------------------------------------------------------------

F = R179.F

record LiteralNearToRound180Carrier : Set where
  constructor literal-near-to-round180-carrier
  field
    cutoff : Nat
    cells : List (C3.Complex3 F)

    nearSchurSq diagonalMass twiceCrossMass : ℚ

    nearSchurSqIsRound180Total :
      nearSchurSq ≡ L2.complex3NormSquared (R180.sumCells cells)

    diagonalMassIsRound180CellMass :
      diagonalMass ≡ R180.cellMassSum cells

    twiceCrossMassIsRound180GramDebt :
      twiceCrossMass ≡ R180.gramDebt cells

open LiteralNearToRound180Carrier public

round180ExactGramIdentityOnLiteralNear :
  (d : LiteralNearToRound180Carrier) →
  nearSchurSq d ≡ diagonalMass d + twiceCrossMass d
round180ExactGramIdentityOnLiteralNear d
  rewrite nearSchurSqIsRound180Total d
        | diagonalMassIsRound180CellMass d
        | twiceCrossMassIsRound180GramDebt d =
  R180.finiteFibreGramLedger (cells d)

record LiteralNearRound180Budget : Set where
  constructor literal-near-round180-budget
  field
    carrier : LiteralNearToRound180Carrier
    diagonalBudget twiceCrossBudget : ℚ
    diagonalBound : diagonalMass carrier ≤ diagonalBudget
    signedGramDebtBound : twiceCrossMass carrier ≤ twiceCrossBudget

open LiteralNearRound180Budget public

compiledRHGramLedger :
  (d : LiteralNearRound180Budget) → RHGram.FiniteNearGramLedger
compiledRHGramLedger d =
  record
    { cutoff = LiteralNearToRound180Carrier.cutoff (carrier d)
    ; nearSchurSq = nearSchurSq (carrier d)
    ; diagonalMass = diagonalMass (carrier d)
    ; twiceCrossMass = twiceCrossMass (carrier d)
    ; exactGramIdentity = round180ExactGramIdentityOnLiteralNear (carrier d)
    ; diagonalBudget = diagonalBudget d
    ; twiceCrossBudget = twiceCrossBudget d
    ; diagonalBound = diagonalBound d
    ; signedCrossBound = signedGramDebtBound d
    }

round180NearSchurBound :
  (d : LiteralNearRound180Budget) →
  nearSchurSq (carrier d) ≤ diagonalBudget d + twiceCrossBudget d
round180NearSchurBound d = RHGram.nearSchurBound (compiledRHGramLedger d)

------------------------------------------------------------------------
-- Boundary: generic Gram algebra is closed; only the literal carrier weld and
-- the signed physical Gram-debt estimate remain.
------------------------------------------------------------------------

record FiniteNearNSGramAdapterBoundary : Set where
  constructor finite-near-ns-gram-adapter-boundary
  field
    round180ExactFiniteGramLedgerAlreadyClosed : Bool
    round180ExactFiniteGramLedgerAlreadyClosedIsTrue :
      round180ExactFiniteGramLedgerAlreadyClosed ≡ true

    rhToRound180CarrierAdapterClosed : Bool
    rhToRound180CarrierAdapterClosedIsTrue :
      rhToRound180CarrierAdapterClosed ≡ true

    literalRHPostSchurCellsIdentifiedWithRound180Carrier : Bool
    literalRHPostSchurCellsIdentifiedWithRound180CarrierIsFalse :
      literalRHPostSchurCellsIdentifiedWithRound180Carrier ≡ false

    signedRHGramDebtEstimateClosed : Bool
    signedRHGramDebtEstimateClosedIsFalse :
      signedRHGramDebtEstimateClosed ≡ false

canonicalFiniteNearNSGramAdapterBoundary : FiniteNearNSGramAdapterBoundary
canonicalFiniteNearNSGramAdapterBoundary =
  finite-near-ns-gram-adapter-boundary true refl true refl false refl false refl
