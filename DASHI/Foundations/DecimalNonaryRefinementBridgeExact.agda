module DASHI.Foundations.DecimalNonaryRefinementBridgeExact where

------------------------------------------------------------------------
-- RETROSPECTIVE DASHI FORMALISATION
--
-- This module formalises the supplied 10%-refinement notes as a finite exact
-- bridge into existing owners.  It deliberately distinguishes:
--
--   coarse stage identity
--   decimal refinement depth
--   normalized nonary occupancy/complement
--   branch accessibility
--   actual guarded stage transition.
--
-- It does NOT claim that a decimal metaphor causes the stage atlas, that the
-- 0..9 stage roles were historically derived from branching processes, or that
-- a finite arithmetic coincidence is an empirical mechanism.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import DASHI.Biology.JCoarseFineEvaluationFibreExact as JFibre
import DASHI.Core.CoarseFineBranchAccessibilityExact as Branch
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.StageValuationBundleAtlas as Stage

------------------------------------------------------------------------
-- A bounded decimal/nonary digit carrier avoids silently treating arbitrary
-- Nat values as members of the 0..9 stage chart.
------------------------------------------------------------------------

data Digit0To9 : Set where
  d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : Digit0To9

digitValue : Digit0To9 → Nat
digitValue d0 = 0
digitValue d1 = 1
digitValue d2 = 2
digitValue d3 = 3
digitValue d4 = 4
digitValue d5 = 5
digitValue d6 = 6
digitValue d7 = 7
digitValue d8 = 8
digitValue d9 = 9

nonaryComplement : Digit0To9 → Nat
nonaryComplement d0 = 9
nonaryComplement d1 = 8
nonaryComplement d2 = 7
nonaryComplement d3 = 6
nonaryComplement d4 = 5
nonaryComplement d5 = 4
nonaryComplement d6 = 3
nonaryComplement d7 = 2
nonaryComplement d8 = 1
nonaryComplement d9 = 0

occupancyPlusComplementIsNine :
  (digit : Digit0To9) →
  digitValue digit + nonaryComplement digit ≡ 9
occupancyPlusComplementIsNine d0 = refl
occupancyPlusComplementIsNine d1 = refl
occupancyPlusComplementIsNine d2 = refl
occupancyPlusComplementIsNine d3 = refl
occupancyPlusComplementIsNine d4 = refl
occupancyPlusComplementIsNine d5 = refl
occupancyPlusComplementIsNine d6 = refl
occupancyPlusComplementIsNine d7 = refl
occupancyPlusComplementIsNine d8 = refl
occupancyPlusComplementIsNine d9 = refl

hasMissingComplement : Digit0To9 → Bool
hasMissingComplement d9 = false
hasMissingComplement _ = true

nineHasNoMissingComplement : hasMissingComplement d9 ≡ false
nineHasNoMissingComplement = refl

fiveHasFourNinthsComplementNumerator : nonaryComplement d5 ≡ 4
fiveHasFourNinthsComplementNumerator = refl

------------------------------------------------------------------------
-- Exact cross-multiplied closed-form target identity.
--
-- The supplied limiting formula is L_N = 10N/9.  Rather than pretending that
-- Agda.Builtin.Nat contains real limits, we record the exact rational identity
-- by cross multiplication:
--
--   9 (N+1) = 10N + (9-N).
--
-- Thus the normalized gap to the next integer band has numerator 9-N over 9.
------------------------------------------------------------------------

refinementTargetNumerator : Digit0To9 → Nat
refinementTargetNumerator digit = 10 * digitValue digit

nextBandScaledNumerator : Digit0To9 → Nat
nextBandScaledNumerator digit = 9 * (digitValue digit + 1)

targetPlusGapIdentity :
  (digit : Digit0To9) →
  nextBandScaledNumerator digit
  ≡ refinementTargetNumerator digit + nonaryComplement digit
targetPlusGapIdentity d0 = refl
targetPlusGapIdentity d1 = refl
targetPlusGapIdentity d2 = refl
targetPlusGapIdentity d3 = refl
targetPlusGapIdentity d4 = refl
targetPlusGapIdentity d5 = refl
targetPlusGapIdentity d6 = refl
targetPlusGapIdentity d7 = refl
targetPlusGapIdentity d8 = refl
targetPlusGapIdentity d9 = refl

nineTargetCarriesExactly :
  nextBandScaledNumerator d9 ≡ refinementTargetNumerator d9
nineTargetCarriesExactly = refl

zeroSelfRefinementHasZeroTarget :
  refinementTargetNumerator d0 ≡ 0
zeroSelfRefinementHasZeroTarget = refl

------------------------------------------------------------------------
-- Finite decimal self-refinement.
--
-- repeatDigitNumerator N depth encodes
--
--   depth 0 : N
--   depth 1 : N.N
--   depth 2 : N.NN
--
-- as an integer numerator over 10^depth.  The coarse digit is stored
-- independently: fine depth therefore cannot definitionally change stage.
------------------------------------------------------------------------

pow10 : Nat → Nat
pow10 zero = 1
pow10 (suc depth) = 10 * pow10 depth

repeatDigitNumerator : Digit0To9 → Nat → Nat
repeatDigitNumerator digit zero = digitValue digit
repeatDigitNumerator digit (suc depth) =
  10 * repeatDigitNumerator digit depth + digitValue digit

record DecimalRefinementAddress : Set where
  constructor decimal-refinement-address
  field
    coarseDigit : Digit0To9
    refinementDepth : Nat
    scaledNumerator : Nat
    scaleDenominator : Nat
    numeratorExact :
      scaledNumerator ≡ repeatDigitNumerator coarseDigit refinementDepth
    denominatorExact :
      scaleDenominator ≡ pow10 refinementDepth

open DecimalRefinementAddress public

canonicalDecimalRefinement :
  Digit0To9 → Nat → DecimalRefinementAddress
canonicalDecimalRefinement digit depth =
  decimal-refinement-address
    digit
    depth
    (repeatDigitNumerator digit depth)
    (pow10 depth)
    refl
    refl

refinementPreservesCoarseDigit :
  (digit : Digit0To9) → (leftDepth rightDepth : Nat) →
  coarseDigit (canonicalDecimalRefinement digit leftDepth)
  ≡ coarseDigit (canonicalDecimalRefinement digit rightDepth)
refinementPreservesCoarseDigit digit leftDepth rightDepth = refl

fiveFirstRefinementIs55Tenths :
  scaledNumerator (canonicalDecimalRefinement d5 1) ≡ 55
fiveFirstRefinementIs55Tenths = refl

fiveSecondRefinementIs555Hundredths :
  scaledNumerator (canonicalDecimalRefinement d5 2) ≡ 555
fiveSecondRefinementIs555Hundredths = refl

nineFirstRefinementIs99Tenths :
  scaledNumerator (canonicalDecimalRefinement d9 1) ≡ 99
nineFirstRefinementIs99Tenths = refl

nineThirdRefinementIs9999Thousandths :
  scaledNumerator (canonicalDecimalRefinement d9 3) ≡ 9999
nineThirdRefinementIs9999Thousandths = refl

------------------------------------------------------------------------
-- Reuse the actual 0..11 stage atlas rather than defining a second ladder.
------------------------------------------------------------------------

stageForDigit : Digit0To9 → Atlas.StageAtlasZeroToEleven
stageForDigit d0 = Atlas.atlas-0
stageForDigit d1 = Atlas.atlas-1
stageForDigit d2 = Atlas.atlas-2
stageForDigit d3 = Atlas.atlas-3
stageForDigit d4 = Atlas.atlas-4
stageForDigit d5 = Atlas.atlas-5
stageForDigit d6 = Atlas.atlas-6
stageForDigit d7 = Atlas.atlas-7
stageForDigit d8 = Atlas.atlas-8
stageForDigit d9 = Atlas.atlas-9

fiveReusesDecisionGateRole :
  Stage.stageRole (stageForDigit d5) ≡ Stage.decisionGateRole
fiveReusesDecisionGateRole = refl

sixReusesReflexiveClosureRole :
  Stage.stageRole (stageForDigit d6) ≡ Stage.reflexiveClosureBarrierRole
sixReusesReflexiveClosureRole = refl

nineReusesSystemicClosureRole :
  Stage.stageRole (stageForDigit d9) ≡ Stage.systemicClosureBarrierRole
nineReusesSystemicClosureRole = refl

nineEscapeRequiresExistingGuardedEdge :
  Stage.GuardedStageEdge Atlas.atlas-9 Atlas.atlas-10
nineEscapeRequiresExistingGuardedEdge = Stage.admitExternalCoordinate

------------------------------------------------------------------------
-- Cross-pollination with the existing recursive fibre and J coarse/fine owners.
------------------------------------------------------------------------

recursiveObservableLevelTwoHasTwentySevenCodes :
  Tower.levelTwoCodeCount ≡ 27
recursiveObservableLevelTwoHasTwentySevenCodes =
  Tower.levelTwoCodeCountIsTwentySeven

jCoarseFrequencyRemainsNine : JFibre.Scale.jCoarseFrequency ≡ 9
jCoarseFrequencyRemainsNine = JFibre.jCoarseFrequencyIsNine

jFineFrequencyRemains19683 : JFibre.Scale.jFineFrequency ≡ 19683
jFineFrequencyRemains19683 = JFibre.jFineFrequencyIsThreePowerNine

-- Exact arithmetic coincidence from the declared independent toy model:
-- three ternary axes at 9/10 availability have expected-count numerator 19683
-- over denominator 1000, exactly the integer used by the existing JFine scale.
-- This is NOT an identification of 90% branch availability with JFine.

ninetyPercentThreeAxisNumeratorMatchesJFine :
  Branch.jointExpectedNumerator 3 3 (Branch.availability 9 10)
  ≡ JFibre.Scale.jFineFrequency
ninetyPercentThreeAxisNumeratorMatchesJFine = refl

fiveEighteenthsRemainsTernarySubcritical :
  Branch.branchingRegime 3 (Branch.availability 5 18)
  ≡ Branch.subcritical
fiveEighteenthsRemainsTernarySubcritical =
  Branch.fiveEighteenthsTernarySubcritical

------------------------------------------------------------------------
-- Boundaries: the bridge types the analogy without promoting it into cause.
------------------------------------------------------------------------

record DecimalNonaryRefinementBoundary : Set where
  constructor decimal-nonary-refinement-boundary
  field
    finiteRefinementChangesCoarseStageAutomatically : Bool
    decimalIdentityCausesStageAtlas : Bool
    nonaryComplementIsEmpiricalMissingInformation : Bool
    independentBranchProductIsUniversal : Bool
    ninetyPercentIsDefinitionallyJFine : Bool
    realLimitConvergenceProvedHere : Bool
    guardedStageTransitionStillRequired : Bool

canonicalDecimalNonaryRefinementBoundary : DecimalNonaryRefinementBoundary
canonicalDecimalNonaryRefinementBoundary =
  decimal-nonary-refinement-boundary
    false
    false
    false
    false
    false
    false
    true
