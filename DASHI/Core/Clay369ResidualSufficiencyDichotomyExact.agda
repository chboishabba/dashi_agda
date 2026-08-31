module DASHI.Core.Clay369ResidualSufficiencyDichotomyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Analysis.RiemannAristotleG2eDeterminantTaperKernelExact as G2e
import DASHI.Analysis.RiemannG2DeterminantConsumerQuotient369Exact as RH
import DASHI.Physics.Closure.NSCriticalConeResidualFibre369CrossPollinationExact as NS
import DASHI.Physics.YangMills.BalabanActiveSourceDiscriminator2026Exact as YMSource
import DASHI.Physics.YangMills.BalabanSourceResidualConsumerNonDescent369Exact as YM

------------------------------------------------------------------------
-- CLAY / 369 RESIDUAL-SUFFICIENCY DICHOTOMY
--
-- The 369/Monster work makes hidden fine structure salient, but the correct
-- consumer-indexed rule is not "always retain the residual".  The repository's
-- consumer-descent calculus gives a sharper dichotomy:
--
--   * if a declared consumer factors through a coarse observer, extra residual
--     coordinates are consumer-invisible at that stage;
--   * if equal coarse observations can produce different consumer outcomes,
--     the residual is genuinely required.
--
-- RH G2e currently exhibits the first shape after determinant scalarization.
-- NS critical-cone signed coherence and YM literal source readiness exhibit the
-- second shape in their current finite proof-search fixtures.
------------------------------------------------------------------------

rhDeterminantObserverIsConsumerSufficient :
  (A : G2e.DeterminantTaperAlgebra) ->
  (kernel : G2e.Scalar A) ->
  Descent.ConsumerSufficient
    (RH.determinantObserver A)
    (RH.fixedKernelConsumer A kernel)
rhDeterminantObserverIsConsumerSufficient =
  RH.determinantResponseSufficientForFixedKernel

nsCoarseShellResidualDoesNotDescend =
  NS.signedResidualCannotDescendThroughShellObserver

ymCoarseSourceNotSufficient :
  Descent.ConsumerSufficient YMSource.coarseSource YMSource.recoveryDecision -> ⊥
ymCoarseSourceNotSufficient =
  YM.coarseBalabanClaimNotSufficientForRecoveryDecision

record Clay369ResidualSufficiencyBoundary : Set where
  constructor clay369ResidualSufficiencyBoundary
  field
    fineResidualAlwaysRequired : Bool
    fineResidualAlwaysRequiredIsFalse : fineResidualAlwaysRequired ≡ false
    consumerSufficiencyCanLegitimatelyCollapseFineStructure : Bool
    consumerSufficiencyCanLegitimatelyCollapseFineStructureIsTrue :
      consumerSufficiencyCanLegitimatelyCollapseFineStructure ≡ true
    consumerNonDescentRequiresResidualRefinement : Bool
    consumerNonDescentRequiresResidualRefinementIsTrue :
      consumerNonDescentRequiresResidualRefinement ≡ true
    rhG2eCurrentlyHasExactScalarSufficiencyPattern : Bool
    rhG2eCurrentlyHasExactScalarSufficiencyPatternIsTrue :
      rhG2eCurrentlyHasExactScalarSufficiencyPattern ≡ true
    nsAndYmCurrentlyHaveResidualNonDescentPatterns : Bool
    nsAndYmCurrentlyHaveResidualNonDescentPatternsIsTrue :
      nsAndYmCurrentlyHaveResidualNonDescentPatterns ≡ true
    boundedReading : String

canonicalClay369ResidualSufficiencyBoundary :
  Clay369ResidualSufficiencyBoundary
canonicalClay369ResidualSufficiencyBoundary =
  clay369ResidualSufficiencyBoundary
    false refl
    true refl
    true refl
    true refl
    true refl
    "369 cross-pollination now has a bidirectional rule: retain fine residual structure exactly where the declared consumer fails to descend, but compress aggressively where an exact sufficient observer exists. RH G2e's determinant q is sufficient for the fixed pointwise zero kernel; NS shell geometry and YM coarse source labels are not sufficient for their signed/recovery consumers."
