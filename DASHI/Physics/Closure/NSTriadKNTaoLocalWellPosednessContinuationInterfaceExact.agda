module DASHI.Physics.Closure.NSTriadKNTaoLocalWellPosednessContinuationInterfaceExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Terence Tao.
-- Title: "254A, Notes 1: Local Well-Posedness of the Navier-Stokes
-- Equations".
-- Publication: expository lecture notes, 16 September 2018.
-- DOI: not assigned.
--
-- Classical continuation reference:
-- Author: James Serrin.
-- Title: "On the Interior Regularity of Weak Solutions of the Navier-Stokes
-- Equations".
-- DOI: 10.1007/BF00253344.
--
-- PURPOSE
-- Expose the exact final logical bridge from a terminal interaction estimate
-- to continuation of a local strong solution.  The analytic local theory owns
-- a maximal lifespan and a continuation norm.  The DASHI terminal theorem
-- supplies a sufficient smallness condition.  Once the local-theory extension
-- map accepts that condition, continuation follows by direct application.
--
-- No field below asserts that the terminal condition is automatic; that is the
-- separate F3/global-depletion frontier.
------------------------------------------------------------------------

record LocalStrongSolutionContinuation
  (Solution : Set)
  (TerminalCondition : Solution → Set)
  (ExtendsPastEndpoint : Solution → Set) : Set₁ where
  constructor local-strong-solution-continuation
  field
    continuationFromTerminalCondition :
      (solution : Solution) →
      TerminalCondition solution →
      ExtendsPastEndpoint solution

open LocalStrongSolutionContinuation public

record TerminalInteractionCriterion
  (Solution : Set) : Set₁ where
  constructor terminal-interaction-criterion
  field
    interactionSmall : Solution → Set
    continuationNormControlled : Solution → Set
    interactionControlsContinuationNorm :
      (solution : Solution) →
      interactionSmall solution →
      continuationNormControlled solution

open TerminalInteractionCriterion public

terminalInteractionContinuation :
  ∀ {Solution : Set}
    {ExtendsPastEndpoint : Solution → Set}
    (criterion : TerminalInteractionCriterion Solution) →
    LocalStrongSolutionContinuation
      Solution
      (continuationNormControlled criterion)
      ExtendsPastEndpoint →
    (solution : Solution) →
    interactionSmall criterion solution →
    ExtendsPastEndpoint solution
terminalInteractionContinuation criterion localTheory solution small =
  continuationFromTerminalCondition
    localTheory
    solution
    (interactionControlsContinuationNorm criterion solution small)
