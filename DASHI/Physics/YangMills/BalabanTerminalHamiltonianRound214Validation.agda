{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanTerminalHamiltonianRound214Validation where

import DASHI.Physics.YangMills.BalabanFiniteMeasureWavefunctionL2BridgeRound205Exact as R205
import DASHI.Physics.YangMills.BalabanFiniteMeasureIBPWavefunctionSymmetryRound206Exact as R206
import DASHI.Physics.YangMills.BalabanNullQuotientHamiltonianDescentRound209Exact as R209
import DASHI.Physics.YangMills.BalabanMeasureNullCanonicalQuotientHamiltonianRound212Exact as R212
import DASHI.Physics.YangMills.BalabanWeakPairingSeparatesNullHamiltoniansRound213Exact as R213
import DASHI.Physics.YangMills.BalabanSymmetrySeparationNullDescentRound214Exact as R214

round205SameMeasureNullSemantics =
  R205.finiteMeasureWavefunctionNullSemanticsRound205Level

round206SelectedIBPSymmetry =
  R206.finiteMeasureIBPWavefunctionSymmetryRound206Level

round209GenericNullDescent =
  R209.nullQuotientHamiltonianDescentRound209Level

round212CanonicalNullQuotientHamiltonian =
  R212.measureNullCanonicalQuotientHamiltonianRound212Level

round213WeakPairingSeparationCompiler =
  R213.weakPairingDeterminesDescendedHamiltonianRound213Level

-- R214 removes null preservation as an independent physical theorem once the
-- SAME R205 pairing has both the R206 symmetry receipt and the R213 separation
-- receipt.
round214SymmetrySeparationNullDescent =
  R214.symmetrySeparationNullDescentRound214Level

round214NullPreservationNoLongerIndependent =
  R214.nullPreservationNoLongerIndependentRound214Level

-- Remaining same-object physical inputs.
round214LiteralBalabanMeasureSemantics =
  R214.literalBalabanMeasureSemanticsRound214Level

round214LiteralBalabanPairingSeparation =
  R214.literalBalabanPairingSeparationRound214Level

round214LiteralPhysicalYMIBPWeld =
  R214.literalPhysicalYMIBPWeldRound214Level
