module DASHI.Mathematics.Complexity.PNotEqualsNPVerifiedLocalArityTerminalAdmissionExact where

------------------------------------------------------------------------
-- COMPUTED TERMINAL VERIFICATION -> LOCAL ARITY/TERMINAL ADMISSION
--
-- Strengthens PNotEqualsNPLocalArityTerminalAdmissionExact by removing the
-- quantified terminalLabelCorrect theorem from the constructor-facing surface.
-- A single executable Boolean check over the finite Shannon tree is enough.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (Maybe; just; nothing)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPLocalArityTerminalAdmissionExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPTerminalPrefixCompletenessVerifierExact as Terminal
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfReferenceAllOverheadBudgetExact as Q1
import DASHI.Mathematics.Complexity.PNotEqualsNPReachableRewriteGeneratedQ1Exact as Reachable
import DASHI.Mathematics.Complexity.PNotEqualsNPRewriteGeneratedQ1DiscoveryExact as RewriteGenerated
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact as Operational
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ConstructionChargedRecurrenceExact as Charged

------------------------------------------------------------------------
-- Constructor-facing local admission.
------------------------------------------------------------------------

record VerifiedLocalArityTerminalAdmission
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root) : Set₁ where
  constructor verified-local-arity-terminal-admission
  field
    stateArity :
      Fin (Candidate.stateCount candidate) → Nat

    rootStateArityExact :
      stateArity (Candidate.rootState candidate)
      ≡ rootVariables

    falseStepArityExact :
      (state : Fin (Candidate.stateCount candidate))
      (remaining : Nat) →
      stateArity state ≡ suc remaining →
      stateArity (Candidate.step candidate state false)
      ≡ remaining

    trueStepArityExact :
      (state : Fin (Candidate.stateCount candidate))
      (remaining : Nat) →
      stateArity state ≡ suc remaining →
      stateArity (Candidate.step candidate state true)
      ≡ remaining

    terminalLabel :
      Fin (Candidate.stateCount candidate) → Bool

    terminalVerifierPasses :
      Terminal.verifyTerminalTree
        candidate
        terminalLabel
        (Candidate.rootState candidate)
        root
      ≡ true

open VerifiedLocalArityTerminalAdmission public

------------------------------------------------------------------------
-- Compile the computed receipt to the prior quantified admission.
------------------------------------------------------------------------

verifiedBuildsLocalAdmission :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root} →
  VerifiedLocalArityTerminalAdmission candidate →
  Local.LocalArityTerminalAdmission candidate
verifiedBuildsLocalAdmission verified =
  Local.local-arity-terminal-admission
    (stateArity verified)
    (rootStateArityExact verified)
    (falseStepArityExact verified)
    (trueStepArityExact verified)
    (terminalLabel verified)
    terminalCorrect
  where
    terminalCorrect :
      ∀ {terminal : SAT.BooleanFormula 0}
        (derivation :
          DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact.RestrictionDerivation
            _ terminal) →
      terminalLabel verified
        (Candidate.candidateSelect candidate derivation)
      ≡
      SAT.evaluate
        terminal
        DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact.emptyAssignment
    terminalCorrect =
      Terminal.terminalVerifierSound
        candidate
        (terminalLabel verified)
        (terminalVerifierPasses verified)

------------------------------------------------------------------------
-- Construction-path lift.
------------------------------------------------------------------------

record VerifiedLocalArityTerminalAdmittedConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor verified-local-arity-terminal-admitted-construction-run
  field
    construction :
      Candidate.FiniteCandidateConstructionRun state

    verifiedAdmission :
      VerifiedLocalArityTerminalAdmission
        (Candidate.transitionCandidate
          (Candidate.finiteCandidate construction))

    allOverheadFits :
      Q1.ClosedQuotientAllOverheadFits
        (RewriteGenerated.toClosedStrictRepresentativeQuotient
          (Reachable.toRewriteGeneratedClosedQuotient
            (Candidate.admitFiniteQ1Candidate
              (Candidate.finiteCandidate construction)
              (Local.localArityTerminalBuildsSemanticCongruence
                (verifiedBuildsLocalAdmission verifiedAdmission)))))
        (Recurrence.stateOverhead state)

    machineConstructionAndNextStrict :
      (Operational.q1WitnessGraphCellCount
        (RewriteGenerated.rewriteGeneratedWitnessToLegacy
          (Reachable.toRewriteGeneratedQ1StateWitness
            (Candidate.admittedFiniteToReachableWitness
              (Candidate.admitted-finite-q1-state-witness
                (Candidate.finiteCandidate construction)
                (Local.localArityTerminalBuildsSemanticCongruence
                  (verifiedBuildsLocalAdmission verifiedAdmission))
                allOverheadFits))))
        + Candidate.machineStepCount construction)
      +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState
          state
          (RewriteGenerated.rewriteGeneratedWitnessToLegacy
            (Reachable.toRewriteGeneratedQ1StateWitness
              (Candidate.admittedFiniteToReachableWitness
                (Candidate.admitted-finite-q1-state-witness
                  (Candidate.finiteCandidate construction)
                  (Local.localArityTerminalBuildsSemanticCongruence
                    (verifiedBuildsLocalAdmission verifiedAdmission))
                  allOverheadFits)))))
      <
      Q2.recursiveMeasure state

open VerifiedLocalArityTerminalAdmittedConstructionRun public

verifiedRunToLocalRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  VerifiedLocalArityTerminalAdmittedConstructionRun state →
  Local.LocalArityTerminalAdmittedConstructionRun state
verifiedRunToLocalRun run =
  Local.local-arity-terminal-admitted-construction-run
    (construction run)
    (verifiedBuildsLocalAdmission
      (verifiedAdmission run))
    (allOverheadFits run)
    (machineConstructionAndNextStrict run)

VerifiedLocalArityTerminalAdmittedStateConstructor : Set₁
VerifiedLocalArityTerminalAdmittedStateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (VerifiedLocalArityTerminalAdmittedConstructionRun state)

verifiedConstructorToLocal :
  VerifiedLocalArityTerminalAdmittedStateConstructor →
  Local.LocalArityTerminalAdmittedStateConstructor
verifiedConstructorToLocal constructor state
    with constructor state
... | nothing = nothing
... | just run = just (verifiedRunToLocalRun run)

verifiedConstructorToQ2StepSystem :
  VerifiedLocalArityTerminalAdmittedStateConstructor →
  Q2.BoundedSelfReferenceStepSystem
verifiedConstructorToQ2StepSystem constructor =
  Local.localConstructorToQ2StepSystem
    (verifiedConstructorToLocal constructor)

------------------------------------------------------------------------
-- Frontier: terminal semantic admission is now one finite Boolean execution
-- receipt rather than a theorem quantified over all terminal derivations.
------------------------------------------------------------------------
