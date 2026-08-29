module DASHI.Foundations.Wette1969Rule915Premise27DirectionalClosureExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5 PREMISE 27: DIRECTIONAL LEAVES -> D27
--
-- The literal p.145 premise 27 is
--
--   L U1 ((V1 V3) -> (U6 -> ((U4 -> U5) ∧ (U5 -> U4)))).
--
-- Hence, after uncurrying the three antecedent layers, the only genuinely
-- mathematical leaves are the two directions
--
--   L H (U4 -> U5)     and     L H (U5 -> U4),
--
-- where H = ((U1 ∧ V1V3) ∧ U6).
--
-- Rule 9.3.5 combines those directions under the same antecedent, and two
-- actual 9.3.9 steps curry U6 and V1V3. This module executes that historical
-- suffix. It does not manufacture either directional leaf.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915CanonicalP145PremisesExact as P145
import DASHI.Foundations.Wette1969Rule915CanonicalP145TypedWeldExact as Weld
import DASHI.Foundations.Wette1969Rule915SourceExactScaffoldCutsetExact as Source
import DASHI.Foundations.Wette1969Rule915IndependentMajorTraceJoinExact as Join
import DASHI.Foundations.Wette1969Rule935ConjunctionExact as Rule935
import DASHI.Foundations.Wette1969Rule939ImplicationIntroductionExact as Rule939
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

conditionAtV3 : WordTerm
conditionAtV3 = P145.juxtapose P145.V1 P145.V3

leftDirection : WordTerm
leftDirection = P145.implication P145.U4 P145.U5

rightDirection : WordTerm
rightDirection = P145.implication P145.U5 P145.U4

directionPair : WordTerm
directionPair = P145.conjunction leftDirection rightDirection

firstAntecedent : WordTerm
firstAntecedent = P145.conjunction P145.U1 conditionAtV3

fullDirectionalAntecedent : WordTerm
fullDirectionalAntecedent = P145.conjunction firstAntecedent P145.U6

record Premise27DirectionalLeafAttempt
    {initial : Context}
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters)
    (scaffold : Source.SourceExactScaffoldInputs initial firstSeven later) : Set₁ where
  constructor premise27DirectionalLeafAttempt
  field
    canonicalFirstSevenIdentity : firstSeven ≡ Weld.canonicalFirstSeven
    canonicalLaterIdentity : later ≡ Weld.canonicalLater
    prefix :
      PCRA.CertifiedRuleTrace historicalSystem
        (Source.sourceExactScaffoldTarget scaffold)
    leftDirectionEvidence :
      Judgment.implies fullDirectionalAntecedent leftDirection Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem prefix)
    rightDirectionEvidence :
      Judgment.implies fullDirectionalAntecedent rightDirection Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem prefix)

open Premise27DirectionalLeafAttempt public

prefixTarget :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  Premise27DirectionalLeafAttempt firstSeven later scaffold → Context
prefixTarget attempt = PCRA.runCertifiedTrace historicalSystem (prefix attempt)

combineDirections :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise27DirectionalLeafAttempt firstSeven later scaffold) →
  PCRA.SelectedRuleApplication historicalSystem (prefixTarget attempt)
combineDirections attempt =
  Rule935.selectRule935
    (prefixTarget attempt)
    fullDirectionalAntecedent leftDirection rightDirection
    (leftDirectionEvidence attempt)
    (rightDirectionEvidence attempt)

combinedTarget :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  Premise27DirectionalLeafAttempt firstSeven later scaffold → Context
combinedTarget attempt = PCRA.applySelected historicalSystem (combineDirections attempt)

combinedEvidence :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise27DirectionalLeafAttempt firstSeven later scaffold) →
  Judgment.implies fullDirectionalAntecedent directionPair Finite.∈Context
    (combinedTarget attempt)
combinedEvidence attempt =
  Closure.certifiedConclusionAvailable (prefixTarget attempt) (combineDirections attempt)

curryU6 :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise27DirectionalLeafAttempt firstSeven later scaffold) →
  PCRA.SelectedRuleApplication historicalSystem (combinedTarget attempt)
curryU6 attempt =
  Rule939.selectRule939
    (combinedTarget attempt)
    firstAntecedent P145.U6 directionPair
    (combinedEvidence attempt)

u6Target :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  Premise27DirectionalLeafAttempt firstSeven later scaffold → Context
u6Target attempt = PCRA.applySelected historicalSystem (curryU6 attempt)

u6Evidence :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise27DirectionalLeafAttempt firstSeven later scaffold) →
  Judgment.implies firstAntecedent (P145.implication P145.U6 directionPair)
    Finite.∈Context (u6Target attempt)
u6Evidence attempt =
  Closure.certifiedConclusionAvailable (combinedTarget attempt) (curryU6 attempt)

curryCondition :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise27DirectionalLeafAttempt firstSeven later scaffold) →
  PCRA.SelectedRuleApplication historicalSystem (u6Target attempt)
curryCondition attempt =
  Rule939.selectRule939
    (u6Target attempt)
    P145.U1 conditionAtV3
    (P145.implication P145.U6 directionPair)
    (u6Evidence attempt)

finalTarget :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  Premise27DirectionalLeafAttempt firstSeven later scaffold → Context
finalTarget attempt = PCRA.applySelected historicalSystem (curryCondition attempt)

canonicalPremise27AtFinalTarget :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise27DirectionalLeafAttempt firstSeven later scaffold) →
  P145.p145Premise Critical.p27 Finite.∈Context (finalTarget attempt)
canonicalPremise27AtFinalTarget attempt =
  Closure.certifiedConclusionAvailable (u6Target attempt) (curryCondition attempt)

suffix :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise27DirectionalLeafAttempt firstSeven later scaffold) →
  PCRA.CertifiedRuleTrace historicalSystem (prefixTarget attempt)
suffix attempt =
  PCRA.choose (combineDirections attempt)
    (PCRA.choose (curryU6 attempt)
      (PCRA.choose (curryCondition attempt) PCRA.done))

premise27Trace :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise27DirectionalLeafAttempt firstSeven later scaffold) →
  PCRA.CertifiedRuleTrace historicalSystem
    (Source.sourceExactScaffoldTarget scaffold)
premise27Trace attempt = PCRA.appendCertifiedTrace (prefix attempt) (suffix attempt)

premise27AtTraceTarget :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise27DirectionalLeafAttempt firstSeven later scaffold) →
  Later.premise27 later Finite.∈Context
    (PCRA.runCertifiedTrace historicalSystem (premise27Trace attempt))
premise27AtTraceTarget {later = later} attempt
  rewrite PCRA.runAppendCertifiedTrace (prefix attempt) (suffix attempt)
  with canonicalFirstSevenIdentity attempt | canonicalLaterIdentity attempt
... | refl | refl = canonicalPremise27AtFinalTarget attempt

closePremise27 :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters}
  {scaffold : Source.SourceExactScaffoldInputs initial firstSeven later} →
  (attempt : Premise27DirectionalLeafAttempt firstSeven later scaffold) →
  Join.CertifiedMajorTrace
    (Source.sourceExactScaffoldTarget scaffold)
    (Later.premise27 later)
closePremise27 attempt =
  Join.certifiedMajorTrace (premise27Trace attempt) (premise27AtTraceTarget attempt)

record Wette1969Rule915Premise27DirectionalClosureBoundary : Set where
  constructor wette1969Rule915Premise27DirectionalClosureBoundary
  field
    exactP145Premise27ReducedToTwoDirectionalLeaves : Bool
    exactP145Premise27ReducedToTwoDirectionalLeavesIsTrue :
      exactP145Premise27ReducedToTwoDirectionalLeaves ≡ true
    closureUsesOneRule935AndTwoRule939Steps : Bool
    closureUsesOneRule935AndTwoRule939StepsIsTrue :
      closureUsesOneRule935AndTwoRule939Steps ≡ true
    directionalSuffixIsProofCarryingHistoricalTrace : Bool
    directionalSuffixIsProofCarryingHistoricalTraceIsTrue :
      directionalSuffixIsProofCarryingHistoricalTrace ≡ true
    closureManufacturesEitherDirectionalLeaf : Bool
    closureManufacturesEitherDirectionalLeafIsFalse :
      closureManufacturesEitherDirectionalLeaf ≡ false

canonicalWette1969Rule915Premise27DirectionalClosureBoundary :
  Wette1969Rule915Premise27DirectionalClosureBoundary
canonicalWette1969Rule915Premise27DirectionalClosureBoundary =
  wette1969Rule915Premise27DirectionalClosureBoundary
    true refl true refl true refl false refl
