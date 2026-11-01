module DASHI.Physics.Closure.GramOperatorNormComputationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ZeroMeanSubspaceGramReceipt as Zero

data GramOperatorNormTerm : Set where
  dyadicTriadicCrossBlock :
    GramOperatorNormTerm

  dyadicPentadicCrossBlock :
    GramOperatorNormTerm

  triadicPentadicCrossBlock :
    GramOperatorNormTerm

  triangleInequalityUpperBound :
    GramOperatorNormTerm

canonicalGramOperatorNormTerms : List GramOperatorNormTerm
canonicalGramOperatorNormTerms =
  dyadicTriadicCrossBlock
  ∷ dyadicPentadicCrossBlock
  ∷ triadicPentadicCrossBlock
  ∷ triangleInequalityUpperBound
  ∷ []

gramOperatorNormStatement : String
gramOperatorNormStatement =
  "The restricted off-diagonal Gram operator decomposes into 2-3, 2-5, and 3-5 cross blocks; a direct operator norm bound is the decisive W2 target."

record GramOperatorNormComputationReceipt : Setω where
  field
    zeroMeanReceipt :
      Zero.ZeroMeanSubspaceGramReceipt

    zeroMeanEntriesUnchanged :
      Zero.zeroMeanDoesNotChangeGramEntries zeroMeanReceipt ≡ true

    terms :
      List GramOperatorNormTerm

    termsAreCanonical :
      terms ≡ canonicalGramOperatorNormTerms

    offDiagonalOperatorNormTargetRecorded :
      Bool

    offDiagonalOperatorNormTargetRecordedIsTrue :
      offDiagonalOperatorNormTargetRecorded ≡ true

    offDiagonalOperatorNormBoundProved :
      Bool

    offDiagonalOperatorNormBoundProvedIsFalse :
      offDiagonalOperatorNormBoundProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ gramOperatorNormStatement

open GramOperatorNormComputationReceipt public

canonicalGramOperatorNormComputationReceipt :
  GramOperatorNormComputationReceipt
canonicalGramOperatorNormComputationReceipt =
  record
    { zeroMeanReceipt =
        Zero.canonicalZeroMeanSubspaceGramReceipt
    ; zeroMeanEntriesUnchanged =
        refl
    ; terms =
        canonicalGramOperatorNormTerms
    ; termsAreCanonical =
        refl
    ; offDiagonalOperatorNormTargetRecorded =
        true
    ; offDiagonalOperatorNormTargetRecordedIsTrue =
        refl
    ; offDiagonalOperatorNormBoundProved =
        false
    ; offDiagonalOperatorNormBoundProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        gramOperatorNormStatement
    ; statementIsCanonical =
        refl
    }
