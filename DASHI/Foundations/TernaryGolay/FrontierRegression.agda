module DASHI.Foundations.TernaryGolay.FrontierRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat.Base using (_*_)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.FiniteLinear.AntiDiagonalKernel as AntiDiagonal
import DASHI.Foundations.FiniteLinear.F3Subspace as Linear
import DASHI.Foundations.TernaryGolay.CompleteWeightEnumerator as Complete
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as Explicit
import DASHI.Foundations.TernaryGolay.GolaySelfDualSubspace as GolaySubspace
import DASHI.Foundations.TernaryGolay.MathieuPresentationAction as Action
import DASHI.Foundations.TernaryGolay.MathieuSourceAtlas as MathieuSources
import DASHI.Foundations.TernaryGolay.MathieuStabilizerChain as Stabilizers
import DASHI.Foundations.TernaryGolay.PuncturedPerfectCode as Puncture
import DASHI.Foundations.TernaryGolay.SelfDualityFiniteBoundary as SelfDual

completeEnumeratorRegression :
  Complete.countComposition Complete.c633 Explicit.allCodewords ≡ 220
completeEnumeratorRegression = Complete.coefficient633

completeEnumeratorSumRegression :
  1 + 22 + 22 + 220 + 220 + 220 + 1 + 22 + 1 ≡ 729
completeEnumeratorSumRegression = Complete.completeCoefficientSum

puncturedMinimumWeightRegression :
  Puncture.countWeight11 5 Puncture.puncturedCodewords ≡ 132
puncturedMinimumWeightRegression = Puncture.puncturedWeight5

puncturedPackingRegression :
  729 * Puncture.radiusTwoErrorPatternCount
  ≡ Puncture.ambientWord11Count
puncturedPackingRegression = Puncture.spherePackingFillsAmbient

derivedDesignRegression :
  Puncture.derivedSteinerCheck ≡ true
derivedDesignRegression = Puncture.derivedSteinerS4511

selfOrthogonalityReadinessRegression :
  SelfDual.allCodewordsOrthogonalToGeneratorsCheck ≡ true
selfOrthogonalityReadinessRegression =
  SelfDual.allCodewordsOrthogonalToGenerators

concreteGolaySelfDualRegression :
  GolaySubspace.codeSubspace Linear.≈ₛ GolaySubspace.dualSubspace
concreteGolaySelfDualRegression = GolaySubspace.golaySelfDual

antiDiagonalKernelRegression :
  AntiDiagonal.sumZeroLine Linear.≈ₛ AntiDiagonal.antiDiagonalLine
antiDiagonalKernelRegression = AntiDiagonal.sumZeroIsAntiDiagonal

sDesignActionRegression :
  Action.sPreservesAllHexadsCheck ≡ true
sDesignActionRegression = Action.sPreservesAllHexads

tDesignActionRegression :
  Action.tPreservesAllHexadsCheck ≡ true
tDesignActionRegression = Action.tPreservesAllHexads

hexadOrbitRegression :
  Explicit.listCount Action.hexadOrbit ≡ 132
hexadOrbitRegression = Action.hexadOrbitCountIs132

signedLiftRegression :
  Action.liftTSquareIsCentralNegationCheck ≡ true
signedLiftRegression = Action.liftTSquareIsCentralNegation

pointStabilizerArithmeticRegression :
  12 * Stabilizers.m11PointStabilizerOrder ≡ Stabilizers.m12Order
pointStabilizerArithmeticRegression = Stabilizers.pointOrbitArithmetic

orderedPairStabilizerArithmeticRegression :
  11 * Stabilizers.orderedTwoPointStabilizerOrder
  ≡ Stabilizers.m11PointStabilizerOrder
orderedPairStabilizerArithmeticRegression =
  Stabilizers.orderedPairOrbitArithmetic

mathieuSourceCountRegression :
  MathieuSources.mathieuSupplementSourceCount ≡ 3
mathieuSourceCountRegression =
  MathieuSources.mathieuSupplementSourceCountIsThree

focusedReceipts : List GenericReceipt.GenericReceipt
focusedReceipts =
  MathieuSources.mathieuSourceAtlasReceipt
  ∷ Complete.completeWeightEnumeratorReceipt
  ∷ Puncture.puncturedPerfectCodeReceipt
  ∷ SelfDual.selfDualityFiniteBoundaryReceipt
  ∷ GolaySubspace.golaySelfDualSubspaceReceipt
  ∷ Action.mathieuFiniteActionReceipt
  ∷ Stabilizers.stabilizerChainReceipt
  ∷ []

allFocusedReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting focusedReceipts
allFocusedReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting focusedReceipts
