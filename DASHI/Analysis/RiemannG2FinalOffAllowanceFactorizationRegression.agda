module DASHI.Analysis.RiemannG2FinalOffAllowanceFactorizationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Analysis.RiemannAristotleRHFinalAllowanceLeafSchedulerExact as Final
import DASHI.Analysis.RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact as Split
import DASHI.Analysis.RiemannG2PoleQuotientOffAllowanceDirectCompilerExact as Direct

------------------------------------------------------------------------
-- Regression: the final Off payment stays open, but its joint near+far allowance
-- inequality is compiler output once an explicit intermediate far allowance is
-- supplied. This must not regress to either far-only cutoff choice or an opaque
-- combined-budget research leaf.
------------------------------------------------------------------------

finalOffLeafStillOpen :
  Final.finalLeafState Final.proveUniversalPoleQuotientOffAllowancePayment
    ≡ Final.open
finalOffLeafStillOpen = refl

intermediateAllowanceCompilerOwned :
  Split.PoleQuotientOffIntermediateAllowanceBoundary.olderRationalAllowancePatternGeneralisedToFinalCarrier
    Split.canonicalPoleQuotientOffIntermediateAllowanceBoundary ≡ true
intermediateAllowanceCompilerOwned = refl

noGlobalReflexivityAdded :
  Split.PoleQuotientOffIntermediateAllowanceBoundary.finalCarrierStrengthenedWithGlobalReflexivityAxiom
    Split.canonicalPoleQuotientOffIntermediateAllowanceBoundary ≡ false
noGlobalReflexivityAdded = refl

jointAllowanceFitNotOpaqueLeaf :
  Split.PoleQuotientOffIntermediateAllowanceBoundary.jointNearPlusFarAllowanceFitIsFreshOpaqueLeaf
    Split.canonicalPoleQuotientOffIntermediateAllowanceBoundary ≡ false
jointAllowanceFitNotOpaqueLeaf = refl

farTailStillNotFreshAnalysis :
  Split.PoleQuotientOffIntermediateAllowanceBoundary.farTailNeedsFreshAnalysis
    Split.canonicalPoleQuotientOffIntermediateAllowanceBoundary ≡ false
farTailStillNotFreshAnalysis = refl

commonCutoffStillRequired :
  Split.PoleQuotientOffIntermediateAllowanceBoundary.commonCutoffStillRequired
    Split.canonicalPoleQuotientOffIntermediateAllowanceBoundary ≡ true
commonCutoffStillRequired = refl

nearMustLeaveExplicitIntermediateAllowance :
  Split.PoleQuotientOffIntermediateAllowanceBoundary.phaseSensitiveNearPlusIntermediateAllowanceStillOpen
    Split.canonicalPoleQuotientOffIntermediateAllowanceBoundary ≡ true
nearMustLeaveExplicitIntermediateAllowance = refl

originalDirectCompilerStillCompilesFinalPayment :
  Direct.PoleQuotientOffAllowanceDirectCompilerBoundary.finalOffTargetAndAllowancePaymentCompile
    Direct.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ true
originalDirectCompilerStillCompilesFinalPayment = refl

finalOffPaymentStillUninhabitedByThisRegression :
  Split.PoleQuotientOffIntermediateAllowanceBoundary.finalOffAllowancePaymentClosed
    Split.canonicalPoleQuotientOffIntermediateAllowanceBoundary ≡ false
finalOffPaymentStillUninhabitedByThisRegression = refl

rhStillOpen :
  Split.PoleQuotientOffIntermediateAllowanceBoundary.rhDerived
    Split.canonicalPoleQuotientOffIntermediateAllowanceBoundary ≡ false
rhStillOpen = refl
