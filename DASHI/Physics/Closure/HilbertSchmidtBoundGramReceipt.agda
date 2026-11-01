module DASHI.Physics.Closure.HilbertSchmidtBoundGramReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GramOperatorNormComputationReceipt as Op

data HilbertSchmidtDiagnostic : Set where
  coarseFinePairCountGrows :
    HilbertSchmidtDiagnostic

  squareEntryWeightDoesNotCompensate :
    HilbertSchmidtDiagnostic

  dyadicTriadicHilbertSchmidtSumDiverges :
    HilbertSchmidtDiagnostic

  frameRouteClosedByUnboundedCrossBlock :
    HilbertSchmidtDiagnostic

canonicalHilbertSchmidtDiagnostics : List HilbertSchmidtDiagnostic
canonicalHilbertSchmidtDiagnostics =
  coarseFinePairCountGrows
  ∷ squareEntryWeightDoesNotCompensate
  ∷ dyadicTriadicHilbertSchmidtSumDiverges
  ∷ frameRouteClosedByUnboundedCrossBlock
  ∷ []

hilbertSchmidtStatement : String
hilbertSchmidtStatement =
  "The 2-3 coarse/fine cross block has divergent Hilbert-Schmidt envelope; the pure 2/3/5 Haar frame route is not rescued on L2_0."

record HilbertSchmidtBoundGramReceipt : Setω where
  field
    operatorNormReceipt :
      Op.GramOperatorNormComputationReceipt

    operatorNormTargetRecorded :
      Op.offDiagonalOperatorNormTargetRecorded operatorNormReceipt ≡ true

    diagnostics :
      List HilbertSchmidtDiagnostic

    diagnosticsAreCanonical :
      diagnostics ≡ canonicalHilbertSchmidtDiagnostics

    hilbertSchmidtNormGram23Diverges :
      Bool

    hilbertSchmidtNormGram23DivergesIsTrue :
      hilbertSchmidtNormGram23Diverges ≡ true

    operatorNormGram23Unbounded :
      Bool

    operatorNormGram23UnboundedIsTrue :
      operatorNormGram23Unbounded ≡ true

    restrictedFrameLowerBoundProved :
      Bool

    restrictedFrameLowerBoundProvedIsFalse :
      restrictedFrameLowerBoundProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ hilbertSchmidtStatement

open HilbertSchmidtBoundGramReceipt public

frameLowerBoundProved :
  HilbertSchmidtBoundGramReceipt →
  Bool
frameLowerBoundProved receipt =
  restrictedFrameLowerBoundProved receipt

canonicalHilbertSchmidtBoundGramReceipt :
  HilbertSchmidtBoundGramReceipt
canonicalHilbertSchmidtBoundGramReceipt =
  record
    { operatorNormReceipt =
        Op.canonicalGramOperatorNormComputationReceipt
    ; operatorNormTargetRecorded =
        refl
    ; diagnostics =
        canonicalHilbertSchmidtDiagnostics
    ; diagnosticsAreCanonical =
        refl
    ; hilbertSchmidtNormGram23Diverges =
        true
    ; hilbertSchmidtNormGram23DivergesIsTrue =
        refl
    ; operatorNormGram23Unbounded =
        true
    ; operatorNormGram23UnboundedIsTrue =
        refl
    ; restrictedFrameLowerBoundProved =
        false
    ; restrictedFrameLowerBoundProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        hilbertSchmidtStatement
    ; statementIsCanonical =
        refl
    }
