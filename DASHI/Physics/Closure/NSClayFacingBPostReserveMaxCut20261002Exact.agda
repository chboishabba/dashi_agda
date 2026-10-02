module DASHI.Physics.Closure.NSClayFacingBPostReserveMaxCut20261002Exact where

------------------------------------------------------------------------
-- CLAY-FACING B / POST-R823-DECISION MAX-CUT
--
-- First settle the two-leaf R828-R832 decision gate.
--
-- If that gate produces the selected negative integral, R831 refutes the
-- universal R823 reserve inequality and the reserve route is frozen.  The
-- surviving internal positive proof route is then exactly:
--
--   B1 physical DFL shell extraction/local ED allocation
--   B2 DFL-DHH cutoff-uniform signed shell estimate
--   B3 DHH intra-shell signed L2 aggregation
--   B4 strict critical signed operator estimate theta < 1
--   B7 literal R406 same-object equality
--   Bcont periodic global continuation
--
-- Existing shell-fold/payment compilers are not counted as leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.NSTriadKNR650Rational345DecisionMaxCutRound832Exact as Decision
import DASHI.Physics.Closure.NSClayFacingBResearchCutExact as B
import DASHI.Physics.Closure.NSABCDConcentratedCompletionCutExact as Cut

data BPostReserveLeaf : Set where
  b1PhysicalDFLExtraction : BPostReserveLeaf
  b2DFLDHHSignedShellEstimate : BPostReserveLeaf
  b3DHHIntraShellSignedL2 : BPostReserveLeaf
  b4StrictCriticalSignedOperator : BPostReserveLeaf
  b7LiteralR406SameObject : BPostReserveLeaf
  bContinuation : BPostReserveLeaf

bPostReserveLeafClosed : BPostReserveLeaf → Bool
bPostReserveLeafClosed b1PhysicalDFLExtraction =
  B.bDFLPhysicalShellExtractionClosed
bPostReserveLeafClosed b2DFLDHHSignedShellEstimate =
  B.bDFLDHHPerShellSignedEstimateClosed
bPostReserveLeafClosed b3DHHIntraShellSignedL2 =
  B.bDHHIntraShellSignedL2Closed
bPostReserveLeafClosed b4StrictCriticalSignedOperator =
  B.bCriticalStrictSignedOperatorClosed
bPostReserveLeafClosed b7LiteralR406SameObject =
  B.bLiteralR406SameObjectClosed
bPostReserveLeafClosed bContinuation =
  Cut.bLiteralClayTheoremClosed

bPostReserveLeafCount : Nat
bPostReserveLeafCount = suc (suc (suc (suc (suc (suc zero)))))

decisionGateLeafCount : Nat
decisionGateLeafCount = Decision.decisionLeafCount

b1ShellCompilerAlreadyClosed : Bool
b1ShellCompilerAlreadyClosed = B.bB1ShellFoldCompilerClosed

b2FoldCompilerAlreadyClosed : Bool
b2FoldCompilerAlreadyClosed = B.bB2BipartiteFoldCompilerClosed

b3FoldCompilerAlreadyClosed : Bool
b3FoldCompilerAlreadyClosed = B.bB3ShellFoldCompilerClosed

b4CompilerAlreadyClosed : Bool
b4CompilerAlreadyClosed = B.bB4SignedOperatorCompilerClosed

b7CompilerAlreadyClosed : Bool
b7CompilerAlreadyClosed = B.bB7R406DecompositionCompilerClosed

genericAnalysisReimplementationRequired : Bool
genericAnalysisReimplementationRequired =
  B.bGenericAnalysisReimplementationRequired

postReserveLeafCountIsSix :
  bPostReserveLeafCount ≡ suc (suc (suc (suc (suc (suc zero)))))
postReserveLeafCountIsSix = refl

decisionGateLeafCountIsTwo :
  decisionGateLeafCount ≡ suc (suc zero)
decisionGateLeafCountIsTwo = Decision.decisionLeafCountIsTwo

genericAnalysisReimplementationRequiredIsFalse :
  genericAnalysisReimplementationRequired ≡ false
genericAnalysisReimplementationRequiredIsFalse = refl

clayPromotion : Bool
clayPromotion = false
