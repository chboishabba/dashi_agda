module DASHI.Statistics.BinaryTestDecisionDirectionalEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Statistics.DirectionalEvidenceTritExact as Evidence

------------------------------------------------------------------------
-- BINARY TEST DECISION / TERNARY EVIDENCE SEPARATION
--
-- A binary statistical test has a two-element ACTION / DECISION alphabet:
-- reject the declared null, or fail to reject it.  That does not make the
-- underlying scientific proposition, world state, or evidential disposition
-- binary.  In particular, fail-to-reject is not an acceptance proof.
------------------------------------------------------------------------

data BinaryTestDecision : Set where
  rejectNull : BinaryTestDecision
  failToRejectNull : BinaryTestDecision

------------------------------------------------------------------------
-- The world-relative truth coordinate is kept separate from the test decision.
-- Error events are therefore expressible without identifying decisions with
-- truth.  We deliberately do not assign probabilities here; concrete statistical
-- calculi may attach alpha/beta/power semantics in adapters.
------------------------------------------------------------------------

record BinaryHypothesisSemantics (World : Set) : Set₁ where
  constructor binary-hypothesis-semantics
  field
    NullTrue : World → Set
    AlternativeTrue : World → Set

open BinaryHypothesisSemantics public

record BinaryTestRun (World Result : Set) : Set₁ where
  constructor binary-test-run
  field
    world : World
    result : Result
    decision : BinaryTestDecision

open BinaryTestRun public

record TypeIErrorWitness
    {World Result : Set}
    (truth : BinaryHypothesisSemantics World)
    (run : BinaryTestRun World Result) : Set where
  constructor type-i-error-witness
  field
    nullWasTrue : NullTrue truth (world run)
    rejectedNull : decision run ≡ rejectNull

open TypeIErrorWitness public

record TypeIIErrorWitness
    {World Result : Set}
    (truth : BinaryHypothesisSemantics World)
    (run : BinaryTestRun World Result) : Set where
  constructor type-ii-error-witness
  field
    alternativeWasTrue : AlternativeTrue truth (world run)
    failedToRejectNull : decision run ≡ failToRejectNull

open TypeIIErrorWitness public

------------------------------------------------------------------------
-- Directional interpretation is an additional compiler.  The same binary
-- decision may be evidentially positive, unresolved, or negative depending on
-- the declared hypothesis, effect region, calibration and design.
------------------------------------------------------------------------

record BinaryDecisionDirectionalInterpretation
    (Result Hypothesis : Set) : Set₁ where
  constructor binary-decision-directional-interpretation
  field
    semantics : Evidence.DirectionalEvidenceSemantics Result Hypothesis

    RejectSupportsPositive : Result → Hypothesis → Set
    RejectSupportsNegative : Result → Hypothesis → Set
    RejectUnderdetermined : Result → Hypothesis → Set

    FailSupportsPositive : Result → Hypothesis → Set
    FailSupportsNegative : Result → Hypothesis → Set
    FailUnderdetermined : Result → Hypothesis → Set

    rejectPositiveSound :
      ∀ {result hypothesis} → RejectSupportsPositive result hypothesis →
      Evidence.SupportsPositive semantics result hypothesis
    rejectNegativeSound :
      ∀ {result hypothesis} → RejectSupportsNegative result hypothesis →
      Evidence.SupportsNegative semantics result hypothesis
    rejectUnderdeterminedSound :
      ∀ {result hypothesis} → RejectUnderdetermined result hypothesis →
      Evidence.Underdetermined semantics result hypothesis

    failPositiveSound :
      ∀ {result hypothesis} → FailSupportsPositive result hypothesis →
      Evidence.SupportsPositive semantics result hypothesis
    failNegativeSound :
      ∀ {result hypothesis} → FailSupportsNegative result hypothesis →
      Evidence.SupportsNegative semantics result hypothesis
    failUnderdeterminedSound :
      ∀ {result hypothesis} → FailUnderdetermined result hypothesis →
      Evidence.Underdetermined semantics result hypothesis

open BinaryDecisionDirectionalInterpretation public

------------------------------------------------------------------------
-- Structural firewalls for the standard inferential mistakes.
------------------------------------------------------------------------

data FailToRejectMeansNullTruePermission : Set where

data RejectNullMeansAlternativeTruePermission : Set where

data BinaryDecisionMeansBinaryEvidencePermission : Set where

failToRejectDoesNotMeanNullTrue :
  FailToRejectMeansNullTruePermission → ⊥
failToRejectDoesNotMeanNullTrue ()

rejectNullDoesNotByItselfMeanAlternativeTrue :
  RejectNullMeansAlternativeTruePermission → ⊥
rejectNullDoesNotByItselfMeanAlternativeTrue ()

binaryDecisionDoesNotForceBinaryEvidence :
  BinaryDecisionMeansBinaryEvidencePermission → ⊥
binaryDecisionDoesNotForceBinaryEvidence ()

record BinaryTestDecisionBoundary : Set where
  constructor binary-test-decision-boundary
  field
    decisionAlphabetIsBinary : Bool
    worldTruthIsDefinitionallyTheDecision : Bool
    failToRejectIsAcceptanceProof : Bool
    rejectAutomaticallyProvesEveryAlternative : Bool
    evidentialDispositionMayNeedThreeStates : Bool
    typeIAndTypeIIErrorRemainExpressible : Bool

canonicalBinaryTestDecisionBoundary : BinaryTestDecisionBoundary
canonicalBinaryTestDecisionBoundary =
  binary-test-decision-boundary true false false false true true
