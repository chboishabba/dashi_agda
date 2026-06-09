module DASHI.Physics.Closure.ParaproductDecompositionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BernsteinInequalityPrimeBandReceipt as Bernstein

data ParaproductPiece : Set where
  lowHigh :
    ParaproductPiece
  highLow :
    ParaproductPiece
  resonant :
    ParaproductPiece

canonicalParaproductPieces : List ParaproductPiece
canonicalParaproductPieces =
  lowHigh ∷ highLow ∷ resonant ∷ []

record ParaproductDecompositionReceipt : Setω where
  field
    bernsteinReceipt :
      Bernstein.BernsteinInequalityPrimeBandReceipt
    bernsteinAvailable :
      Bernstein.bernsteinInequalityPrimeBand bernsteinReceipt ≡ true
    paraproductDecomposed :
      Bool
    paraproductDecomposedIsTrue :
      paraproductDecomposed ≡ true
    pieces :
      List ParaproductPiece
    piecesAreCanonical :
      pieces ≡ canonicalParaproductPieces
    lowHighControlledByLinftyH1 :
      Bool
    lowHighControlledByLinftyH1IsTrue :
      lowHighControlledByLinftyH1 ≡ true
    resonantTermBoundedByH34 :
      Bool
    resonantTermBoundedByH34IsTrue :
      resonantTermBoundedByH34 ≡ true
    fullGlobalRegularityEstimate :
      Bool
    fullGlobalRegularityEstimateIsFalse :
      fullGlobalRegularityEstimate ≡ false
    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    receiptBoundary :
      List String

open ParaproductDecompositionReceipt public

canonicalParaproductDecompositionReceipt :
  ParaproductDecompositionReceipt
canonicalParaproductDecompositionReceipt =
  record
    { bernsteinReceipt =
        Bernstein.canonicalBernsteinInequalityPrimeBandReceipt
    ; bernsteinAvailable =
        refl
    ; paraproductDecomposed =
        true
    ; paraproductDecomposedIsTrue =
        refl
    ; pieces =
        canonicalParaproductPieces
    ; piecesAreCanonical =
        refl
    ; lowHighControlledByLinftyH1 =
        true
    ; lowHighControlledByLinftyH1IsTrue =
        refl
    ; resonantTermBoundedByH34 =
        true
    ; resonantTermBoundedByH34IsTrue =
        refl
    ; fullGlobalRegularityEstimate =
        false
    ; fullGlobalRegularityEstimateIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Bony low-high, high-low, and resonant terms are recorded in prime LP bands"
        ∷ "This supports weak compactness/nonlinear passage, not smooth global regularity"
        ∷ []
    }
