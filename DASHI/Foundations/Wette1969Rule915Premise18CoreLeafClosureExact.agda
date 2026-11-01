module DASHI.Foundations.Wette1969Rule915Premise18CoreLeafClosureExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5 PREMISE 18: CORE LEAF -> D18
--
-- Printed p.145 gives premise 18 the outer form
--
--   L U1 (U3 -> (V1 V3 -> W3 V3)).
--
-- Rule 9.3.9 is exactly the historical currying rule
--
--   L (w ∧ u) v -> L w (u -> v).
--
-- Therefore one certified derivation of the uncurried core leaf
--
--   L ((U1 ∧ U3) ∧ V1V3) W3V3
--
-- yields premise 18 by two actual certified 9.3.9 steps.  This module executes
-- those two historical steps; it does not manufacture the core leaf.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915SourceExactScaffoldCutsetExact as Source
import DASHI.Foundations.Wette1969Rule915IndependentMajorTraceJoinExact as Join
import DASHI.Foundations.Wette1969Rule915Premise18ImplicationSpineExact as Spine
import DASHI.Foundations.Wette1969Rule939ImplicationIntroductionExact as Rule939
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record Premise18CoreLeafAttempt
    {initial : Context}
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters)
    (scaffold : Source.SourceExactScaffoldInputs initial firstSeven later) : Set₁ where
  constructor premise18CoreLeafAttempt
  field
    p145SpineRecovery : Spine.Premise18P145SpineRecovery later
    coreLeafTrace :
      Join.CertifiedMajorTrace
        (Source.sourceExactScaffoldTarget scaffold)
        (Spine.coreLeaf later)

open Premise18CoreLeafAttempt public

coreTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  Premise18CoreLeafAttempt firstSeven later scaffold → Context
coreTarget attempt =
  PCRA.runCertifiedTrace historicalSystem
    (Join.trace (coreLeafTrace attempt))

coreLeafAtTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise18CoreLeafAttempt firstSeven later scaffold) →
  Spine.coreLeaf later Finite.∈Context (coreTarget attempt)
coreLeafAtTarget attempt = Join.goalAtTarget (coreLeafTrace attempt)

firstRule939 :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise18CoreLeafAttempt firstSeven later scaffold) →
  PCRA.SelectedRuleApplication historicalSystem (coreTarget attempt)
firstRule939 {later = later} attempt =
  Rule939.selectRule939
    (coreTarget attempt)
    (Spine.firstUncurriedAntecedent later)
    (Spine.conditionAtV3 later)
    (Spine.inductionMarkAtV3 later)
    (coreLeafAtTarget attempt)

firstTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  Premise18CoreLeafAttempt firstSeven later scaffold → Context
firstTarget attempt = PCRA.applySelected historicalSystem (firstRule939 attempt)

firstUncurriedGoalAtTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise18CoreLeafAttempt firstSeven later scaffold) →
  Spine.firstUncurriedGoal later Finite.∈Context (firstTarget attempt)
firstUncurriedGoalAtTarget {later = later} attempt =
  Closure.certifiedConclusionAvailable (coreTarget attempt) (firstRule939 attempt)

secondRule939 :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise18CoreLeafAttempt firstSeven later scaffold) →
  PCRA.SelectedRuleApplication historicalSystem (firstTarget attempt)
secondRule939 {later = later} attempt =
  Rule939.selectRule939
    (firstTarget attempt)
    (Later.definitionPrerequisiteWord later)
    (Later.expansion17 later)
    (Rule939.implicationWord
      (Spine.conditionAtV3 later)
      (Spine.inductionMarkAtV3 later))
    (firstUncurriedGoalAtTarget attempt)

outerTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  Premise18CoreLeafAttempt firstSeven later scaffold → Context
outerTarget attempt = PCRA.applySelected historicalSystem (secondRule939 attempt)

outerFormulaAtTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise18CoreLeafAttempt firstSeven later scaffold) →
  Spine.premise18OuterFormula later Finite.∈Context (outerTarget attempt)
outerFormulaAtTarget {later = later} attempt =
  Closure.certifiedConclusionAvailable (firstTarget attempt) (secondRule939 attempt)

curryingSuffix :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise18CoreLeafAttempt firstSeven later scaffold) →
  PCRA.CertifiedRuleTrace historicalSystem (coreTarget attempt)
curryingSuffix attempt =
  PCRA.choose (firstRule939 attempt)
    (PCRA.choose (secondRule939 attempt) PCRA.done)

premise18Trace :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise18CoreLeafAttempt firstSeven later scaffold) →
  PCRA.CertifiedRuleTrace
    historicalSystem
    (Source.sourceExactScaffoldTarget scaffold)
premise18Trace attempt =
  PCRA.appendCertifiedTrace
    (Join.trace (coreLeafTrace attempt))
    (curryingSuffix attempt)

premise18AtTraceTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise18CoreLeafAttempt firstSeven later scaffold) →
  Later.premise18 later Finite.∈Context
    (PCRA.runCertifiedTrace historicalSystem (premise18Trace attempt))
premise18AtTraceTarget {later = later} attempt
  rewrite PCRA.runAppendCertifiedTrace
    (Join.trace (coreLeafTrace attempt))
    (curryingSuffix attempt)
  with Spine.premise18OuterFormulaMatchesTypedSlot
    later (p145SpineRecovery attempt)
... | refl = outerFormulaAtTarget attempt

coreLeafAttemptClosesPremise18 :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise18CoreLeafAttempt firstSeven later scaffold) →
  Join.CertifiedMajorTrace
    (Source.sourceExactScaffoldTarget scaffold)
    (Later.premise18 later)
coreLeafAttemptClosesPremise18 attempt =
  Join.certifiedMajorTrace
    (premise18Trace attempt)
    (premise18AtTraceTarget attempt)

record Wette1969Rule915Premise18CoreLeafClosureBoundary : Set where
  constructor wette1969Rule915Premise18CoreLeafClosureBoundary
  field
    certifiedCoreLeafClosesPremise18 : Bool
    certifiedCoreLeafClosesPremise18IsTrue :
      certifiedCoreLeafClosesPremise18 ≡ true
    closureUsesExactlyTwoExplicitRule939Steps : Bool
    closureUsesExactlyTwoExplicitRule939StepsIsTrue :
      closureUsesExactlyTwoExplicitRule939Steps ≡ true
    bothCurryingStepsAreProofCarryingHistoricalApplications : Bool
    bothCurryingStepsAreProofCarryingHistoricalApplicationsIsTrue :
      bothCurryingStepsAreProofCarryingHistoricalApplications ≡ true
    p145SpineIdentityIsUsedBeforeTypedPremise18Promotion : Bool
    p145SpineIdentityIsUsedBeforeTypedPremise18PromotionIsTrue :
      p145SpineIdentityIsUsedBeforeTypedPremise18Promotion ≡ true
    syntacticScaffoldAloneManufacturesCoreLeaf : Bool
    syntacticScaffoldAloneManufacturesCoreLeafIsFalse :
      syntacticScaffoldAloneManufacturesCoreLeaf ≡ false

canonicalWette1969Rule915Premise18CoreLeafClosureBoundary :
  Wette1969Rule915Premise18CoreLeafClosureBoundary
canonicalWette1969Rule915Premise18CoreLeafClosureBoundary =
  wette1969Rule915Premise18CoreLeafClosureBoundary
    true refl true refl true refl true refl false refl
