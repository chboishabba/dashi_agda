module DASHI.Foundations.Wette1969Rule915Premise27DirectionalClosureExact where

open import DASHI.Core.Prelude
import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
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
conditionAtV3 = P145.juxtapose P145.V1 P145.V3
leftDirection = P145.implication P145.U4 P145.U5
rightDirection = P145.implication P145.U5 P145.U4
directionPair = P145.conjunction leftDirection rightDirection
firstAntecedent = P145.conjunction P145.U1 conditionAtV3
fullDirectionalAntecedent = P145.conjunction firstAntecedent P145.U6

record CanonicalPremise27DirectionalLeafAttempt {initial : Context}
    (scaffold : Source.SourceExactScaffoldInputs initial Weld.canonicalFirstSeven Weld.canonicalLater) : Set₁ where
  constructor canonicalPremise27DirectionalLeafAttempt
  field
    prefix : PCRA.CertifiedRuleTrace historicalSystem (Source.sourceExactScaffoldTarget scaffold)
    leftDirectionEvidence : Judgment.implies fullDirectionalAntecedent leftDirection Finite.∈Context (PCRA.runCertifiedTrace historicalSystem prefix)
    rightDirectionEvidence : Judgment.implies fullDirectionalAntecedent rightDirection Finite.∈Context (PCRA.runCertifiedTrace historicalSystem prefix)
open CanonicalPremise27DirectionalLeafAttempt public

prefixTarget attempt = PCRA.runCertifiedTrace historicalSystem (prefix attempt)
combineDirections attempt = Rule935.selectRule935 (prefixTarget attempt) fullDirectionalAntecedent leftDirection rightDirection (leftDirectionEvidence attempt) (rightDirectionEvidence attempt)
combinedTarget attempt = PCRA.applySelected historicalSystem (combineDirections attempt)
combinedEvidence attempt = Closure.certifiedConclusionAvailable (prefixTarget attempt) (combineDirections attempt)
curryU6 attempt = Rule939.selectRule939 (combinedTarget attempt) firstAntecedent P145.U6 directionPair (combinedEvidence attempt)
u6Target attempt = PCRA.applySelected historicalSystem (curryU6 attempt)
u6Evidence attempt = Closure.certifiedConclusionAvailable (combinedTarget attempt) (curryU6 attempt)
curryCondition attempt = Rule939.selectRule939 (u6Target attempt) P145.U1 conditionAtV3 (P145.implication P145.U6 directionPair) (u6Evidence attempt)
finalTarget attempt = PCRA.applySelected historicalSystem (curryCondition attempt)
canonicalPremise27AtFinalTarget attempt = Closure.certifiedConclusionAvailable (u6Target attempt) (curryCondition attempt)
suffix attempt = PCRA.choose (combineDirections attempt) (PCRA.choose (curryU6 attempt) (PCRA.choose (curryCondition attempt) PCRA.done))
premise27Trace attempt = PCRA.appendCertifiedTrace (prefix attempt) (suffix attempt)

premise27AtTraceTarget :
  {initial : Context}
  {scaffold : Source.SourceExactScaffoldInputs initial Weld.canonicalFirstSeven Weld.canonicalLater} →
  (attempt : CanonicalPremise27DirectionalLeafAttempt scaffold) →
  P145.p145Premise Critical.p27 Finite.∈Context (PCRA.runCertifiedTrace historicalSystem (premise27Trace attempt))
premise27AtTraceTarget attempt rewrite PCRA.runAppendCertifiedTrace (prefix attempt) (suffix attempt) = canonicalPremise27AtFinalTarget attempt

closeCanonicalPremise27 :
  {initial : Context}
  {scaffold : Source.SourceExactScaffoldInputs initial Weld.canonicalFirstSeven Weld.canonicalLater} →
  (attempt : CanonicalPremise27DirectionalLeafAttempt scaffold) →
  Join.CertifiedMajorTrace (Source.sourceExactScaffoldTarget scaffold) (P145.p145Premise Critical.p27)
closeCanonicalPremise27 attempt = Join.certifiedMajorTrace (premise27Trace attempt) (premise27AtTraceTarget attempt)

record Wette1969Rule915Premise27DirectionalClosureBoundary : Set where
  constructor wette1969Rule915Premise27DirectionalClosureBoundary
  field
    exactP145Premise27ReducedToTwoDirectionalLeaves : Bool
    exactP145Premise27ReducedToTwoDirectionalLeavesIsTrue : exactP145Premise27ReducedToTwoDirectionalLeaves ≡ true
    closureUsesOneRule935AndTwoRule939Steps : Bool
    closureUsesOneRule935AndTwoRule939StepsIsTrue : closureUsesOneRule935AndTwoRule939Steps ≡ true
    directionalSuffixIsProofCarryingHistoricalTrace : Bool
    directionalSuffixIsProofCarryingHistoricalTraceIsTrue : directionalSuffixIsProofCarryingHistoricalTrace ≡ true
    closureManufacturesEitherDirectionalLeaf : Bool
    closureManufacturesEitherDirectionalLeafIsFalse : closureManufacturesEitherDirectionalLeaf ≡ false
canonicalWette1969Rule915Premise27DirectionalClosureBoundary = wette1969Rule915Premise27DirectionalClosureBoundary true refl true refl true refl false refl
