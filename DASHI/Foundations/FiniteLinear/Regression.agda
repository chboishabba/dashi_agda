module DASHI.Foundations.FiniteLinear.Regression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.FiniteLinear.AntiDiagonalKernel as AntiDiagonal
import DASHI.Foundations.FiniteLinear.F3Subspace as Linear
import DASHI.Physics.Closure.NSTriadKNFiniteIncidenceSubspaceAdapter as NSAdapter

antiDiagonalKernelImageRegression :
  AntiDiagonal.sumZeroLine Linear.≈ₛ AntiDiagonal.antiDiagonalLine
antiDiagonalKernelImageRegression =
  AntiDiagonal.sumZeroIsAntiDiagonal

nsFiniteEdgeKernelImageRegression :
  AntiDiagonal.sumZeroLine Linear.≈ₛ AntiDiagonal.antiDiagonalLine
nsFiniteEdgeKernelImageRegression =
  NSAdapter.finitePairEdgeKernelImageEquality

physicalGramPromotionClosed :
  NSAdapter.pairIncidenceFoldEqualsPDEGramProvedHere
    NSAdapter.canonicalFiniteIncidenceGramAdapterStatus
  ≡ false
physicalGramPromotionClosed =
  NSAdapter.pairIncidenceFoldEqualsPDEGramProvedHereIsFalse
    NSAdapter.canonicalFiniteIncidenceGramAdapterStatus

focusedReceipts : List GenericReceipt.GenericReceipt
focusedReceipts =
  NSAdapter.finiteIncidenceGramAdapterReceipt
  ∷ []

allFocusedReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting focusedReceipts
allFocusedReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting focusedReceipts
