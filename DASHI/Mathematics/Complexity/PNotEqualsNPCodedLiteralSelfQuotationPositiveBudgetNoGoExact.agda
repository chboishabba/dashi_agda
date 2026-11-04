module DASHI.Mathematics.Complexity.PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact where

------------------------------------------------------------------------
-- POSITIVE-BUDGET NO-GO FOR LITERAL OWN-COOK-FORMULA MATERIALISATION
--
-- In the concrete coded-standard model:
--
--   I + 2*T <= |ownCL| <= I + p <= I + T,
--
-- so every structurally literal materialisation witness forces T = 0.
-- This is a no-go for that proof architecture, NOT a proof of P != NP.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_≤_; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.CodedStandardPolynomialCostModelExact as Cost
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as Decider
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedStandardCandidateBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralResourceClosingCompilerExact as StructuralResource
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralPrefixSpanNecessityExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralPrefixConcreteWriteExact as PrefixWrite
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralPrefixEndpointContentExact as Endpoint
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingBudgetNecessityExact as Budget

import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StructuralSimulationNonblankExact as StructuralNonblank
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeNonblankWriteBoundExact as Nonblank
import DASHI.Mathematics.Complexity.ConcreteTapeGuardedNonblankExact as GuardedNonblank
import DASHI.Mathematics.Complexity.ConcreteTapeInputNonblankPayloadExact as Payload
import DASHI.Mathematics.Complexity.CodedStandardFormulaInputNonblankExact as CodedInput
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinBitCodeWidthLowerExact as CookWidth
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.ConcreteTapeSymbolWriteLocalityExact as Writes
import DASHI.Mathematics.Complexity.ConcreteTapeStandardReverseRunExact as Reverse

cancelLeftAddLe :
  ∀ (left a b : Nat) →
  left + a ≤ left + b →
  a ≤ b
cancelLeftAddLe zero a b proof = proof
cancelLeftAddLe (suc left) a b (s≤s proof) =
  cancelLeftAddLe left a b proof

noSucLeSelf :
  ∀ (n : Nat) →
  suc n ≤ n → ⊥
noSucLeSelf zero ()
noSucLeSelf (suc n) (s≤s proof) =
  noSucLeSelf n proof

twoTimesAsDouble :
  ∀ (n : Nat) →
  (suc (suc zero)) * n ≡ n + n
twoTimesAsDouble n =
  trans
    (NatP.*-comm (suc (suc zero)) n)
    (trans
      (NatP.*-suc n (suc zero))
      (cong (n +_) (NatP.*-identityʳ n)))

positiveDoubleStrictlyAboveSelf :
  ∀ (n : Nat) →
  suc n + suc n ≤ suc n → ⊥
positiveDoubleStrictlyAboveSelf n doubleBelow =
  noSucLeSelf
    (suc n)
    (NatP.≤-trans strictGrowth doubleBelow)
  where
    sumShape :
      suc (suc n) + n ≡ suc n + suc n
    sumShape
      rewrite NatP.+-suc n n = refl

    strictGrowth :
      suc (suc n) ≤ suc n + suc n
    strictGrowth =
      subst
        (λ rhs → suc (suc n) ≤ rhs)
        sumShape
        (NatP.m≤m+n (suc (suc n)) n)

doubleLeSelfForcesZero :
  ∀ (n : Nat) →
  (suc (suc zero)) * n ≤ n →
  n ≡ zero
doubleLeSelfForcesZero zero proof = refl
doubleLeSelfForcesZero (suc n) proof =
  ⊥-elim
    (positiveDoubleStrictlyAboveSelf n
      (subst
        (λ doubled → doubled ≤ suc n)
        (twoTimesAsDouble (suc n))
        proof))

codedWitness :
  (closure : Cost.CodedStandardCostClosure)
  (candidate :
    Direct.PolynomialSATDeciderCandidate
      (Cost.codedStandardPolynomialCostModel closure)) →
  Decider.CodedStandardPolynomialDecider (Direct.decide candidate)
codedWitness closure candidate =
  Direct.polynomialDecision candidate

codedClockedCandidate :
  (closure : Cost.CodedStandardCostClosure)
  (candidate :
    Direct.PolynomialSATDeciderCandidate
      (Cost.codedStandardPolynomialCostModel closure)) →
  Clocked.PolynomiallyClockedStandardCandidate candidate
codedClockedCandidate closure candidate =
  Bridge.codedWitnessToPolynomiallyClockedCandidate
    (codedWitness closure candidate)

endpointNonblankExactOwnCookBits :
  (closure : Cost.CodedStandardCostClosure)
  (candidate :
    Direct.PolynomialSATDeciderCandidate
      (Cost.codedStandardPolynomialCostModel closure))
  (structuralResource :
    StructuralResource.StructuralResourceClosingFixedProgramCompilation
      (codedClockedCandidate closure candidate)) →
  Nonblank.nonblankCount
    (Presented.finiteSymbol
      (Opposite.presentation
        (Resource.fixed (StructuralResource.resource structuralResource))))
    (Presented.blank
      (Opposite.presentation
        (Resource.fixed (StructuralResource.resource structuralResource))))
    (Writes.eraseRow
      (Reverse.finish
        (PrefixWrite.reified
          (PrefixWrite.reifyStructuralPrefix structuralResource))))
  ≡
  Binary.formulaBitCodeLength
    (Prefix.candidateOwnFormula structuralResource)
endpointNonblankExactOwnCookBits closure candidate structuralResource =
  trans
    (cong
      (Nonblank.nonblankCount targetEnumeration targetBlank)
      (Endpoint.prefixEndpointContentExact structuralResource))
    (trans
      (StructuralNonblank.structuralMapNonblankCountExact
        sourceEnumeration targetEnumeration structural sourceGuardedSymbols)
      (trans
        (Payload.guardedInputNonblankExactPayload
          (Prefix.candidateOwnInput structuralResource)
          (Prefix.candidateOwnSteps structuralResource))
        (CodedInput.formulaInputNonblankCountExact
          witness
          (Prefix.candidateOwnFormula structuralResource))))
  where
    witness = codedWitness closure candidate
    clocked = codedClockedCandidate closure candidate
    standard = Clocked.standard clocked
    base = StructuralResource.resource structuralResource
    structural = StructuralResource.structuralSimulation structuralResource

    sourceEnumeration = Presented.finiteSymbol (Candidate.presentation standard)
    targetEnumeration = Presented.finiteSymbol (Opposite.presentation (Resource.fixed base))
    targetBlank = Presented.blank (Opposite.presentation (Resource.fixed base))

    sourceGuardedSymbols =
      Writes.eraseRow
        (Guard.guardedInitialRow
          (Prefix.candidateOwnInput structuralResource)
          (Prefix.candidateOwnSteps structuralResource))

ownCookBitsUpperBySeedAndPrefix :
  (closure : Cost.CodedStandardCostClosure)
  (candidate :
    Direct.PolynomialSATDeciderCandidate
      (Cost.codedStandardPolynomialCostModel closure))
  (structuralResource :
    StructuralResource.StructuralResourceClosingFixedProgramCompilation
      (codedClockedCandidate closure candidate)) →
  Binary.formulaBitCodeLength
      (Prefix.candidateOwnFormula structuralResource)
  ≤
  Input.initialInputCellCount fixedInput
    + Resource.prefixSteps base
  where
    base = StructuralResource.resource structuralResource
    fixedInput = Opposite.input (Resource.fixed base)
ownCookBitsUpperBySeedAndPrefix closure candidate structuralResource =
  subst
    (λ finalNonblank →
      finalNonblank
      ≤ Input.initialInputCellCount fixedInput
        + Resource.prefixSteps base)
    (endpointNonblankExactOwnCookBits closure candidate structuralResource)
    (NatP.≤-trans writeBound startBoundWithPrefix)
  where
    base = StructuralResource.resource structuralResource
    fixed = Resource.fixed base
    fixedInput = Opposite.input fixed
    totalSteps = Opposite.steps fixed
    targetMachine = Opposite.fixedConcreteMachine fixed
    targetEnumeration = Local.finiteSymbol targetMachine
    targetBlank = Local.blank targetMachine

    writeBound =
      Nonblank.writesWithinNonblankBound
        targetEnumeration targetBlank
        (PrefixWrite.prefixConcreteWritesWithin structuralResource)

    startBound =
      GuardedNonblank.guardedRowNonblankBelowInitialWidth
        fixedInput totalSteps

    startBoundWithPrefix =
      NatP.+-mono-≤
        startBound
        (NatP.≤-refl (Resource.prefixSteps base))

seedWidthBelowOwnCookBits :
  (closure : Cost.CodedStandardCostClosure)
  (candidate :
    Direct.PolynomialSATDeciderCandidate
      (Cost.codedStandardPolynomialCostModel closure))
  (structuralResource :
    StructuralResource.StructuralResourceClosingFixedProgramCompilation
      (codedClockedCandidate closure candidate)) →
  Guard.guardedInitialCols fixedInput totalSteps
  ≤ Binary.formulaBitCodeLength
      (Prefix.candidateOwnFormula structuralResource)
  where
    base = StructuralResource.resource structuralResource
    fixed = Resource.fixed base
    fixedInput = Opposite.input fixed
    totalSteps = Opposite.steps fixed
seedWidthBelowOwnCookBits closure candidate structuralResource =
  CookWidth.guardedColsBelowCookFormulaBitCode
    (Opposite.stateCoverage fixed)
    (Opposite.symbolCoverage fixed)
    (Opposite.nonemptyRules fixed)
    (Opposite.input fixed)
    (Opposite.steps fixed)
  where
    base = StructuralResource.resource structuralResource
    fixed = Resource.fixed base

literalStructuralSelfQuotationForcesZeroBudget :
  (closure : Cost.CodedStandardCostClosure)
  (candidate :
    Direct.PolynomialSATDeciderCandidate
      (Cost.codedStandardPolynomialCostModel closure))
  (structuralResource :
    StructuralResource.StructuralResourceClosingFixedProgramCompilation
      (codedClockedCandidate closure candidate)) →
  Opposite.steps
    (Resource.fixed (StructuralResource.resource structuralResource))
  ≡ zero
literalStructuralSelfQuotationForcesZeroBudget
    closure candidate structuralResource =
  doubleLeSelfForcesZero totalSteps doubleBelowSelf
  where
    base = StructuralResource.resource structuralResource
    fixed = Resource.fixed base
    fixedInput = Opposite.input fixed
    totalSteps = Opposite.steps fixed
    prefixSteps = Resource.prefixSteps base
    initialWidth = Input.initialInputCellCount fixedInput

    widthToUpper :
      initialWidth + ((suc (suc zero)) * totalSteps)
      ≤ initialWidth + prefixSteps
    widthToUpper =
      NatP.≤-trans
        (seedWidthBelowOwnCookBits closure candidate structuralResource)
        (ownCookBitsUpperBySeedAndPrefix closure candidate structuralResource)

    doubleBelowPrefix :
      (suc (suc zero)) * totalSteps ≤ prefixSteps
    doubleBelowPrefix =
      cancelLeftAddLe
        initialWidth
        ((suc (suc zero)) * totalSteps)
        prefixSteps
        widthToUpper

    doubleBelowSelf :
      (suc (suc zero)) * totalSteps ≤ totalSteps
    doubleBelowSelf =
      NatP.≤-trans
        doubleBelowPrefix
        (Budget.prefixFitsCookBudget base)

literalStructuralSelfQuotationPositiveBudgetImpossible :
  (closure : Cost.CodedStandardCostClosure)
  (candidate :
    Direct.PolynomialSATDeciderCandidate
      (Cost.codedStandardPolynomialCostModel closure))
  (structuralResource :
    StructuralResource.StructuralResourceClosingFixedProgramCompilation
      (codedClockedCandidate closure candidate)) →
  suc zero
  ≤ Opposite.steps
      (Resource.fixed (StructuralResource.resource structuralResource)) →
  ⊥
literalStructuralSelfQuotationPositiveBudgetImpossible
    closure candidate structuralResource positive
    rewrite literalStructuralSelfQuotationForcesZeroBudget
      closure candidate structuralResource =
  noSucLeSelf zero positive

------------------------------------------------------------------------
-- ROADMAP CONSEQUENCE
--
-- Explicit full own-Cook-formula materialisation on the same single tape before
-- running D cannot fit any positive exact Cook budget. The next architecture
-- must use resource-accounted virtual/streaming quotation, or another proved
-- same-semantics representation. No SAT lower bound is inferred from this.
------------------------------------------------------------------------
