module DASHI.Mathematics.Complexity.PNotEqualsNPPrizeBoundaryExact where

------------------------------------------------------------------------
-- PRIZE-FACING TERMINAL P != NP INTERFACE
--
-- Cook--Levin/tableau correctness and polynomial formula size are already
-- source-written elsewhere.  This file deliberately adds no new machine,
-- circuit, or encoding framework.
--
-- The only theorem needed after NP-completeness is the literal logical fact:
--
--   an NP-complete language outside P  ==>  P != NP.
--
-- Thus a Clay-facing P != NP proof may stop at one actual lower-bound
-- inhabitant for SAT (or any other NP-complete target).
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

PNotEqualsNP :
  ∀ {Word : Set} →
  PR.PolynomialCostModel Word →
  Setω
PNotEqualsNP cost =
  PR.PEqualsNP cost → ⊥

record NPCompleteOutsideP
    {Word : Set}
    (cost : PR.PolynomialCostModel Word)
    (target : PR.Language Word) : Setω where
  field
    complete : PR.NPComplete cost target
    targetNotInP : PR.InP cost target → ⊥

open NPCompleteOutsideP public

-- No P-subset-NP plumbing is needed in this direction.  If P=NP, the
-- npToP half puts every NP language in P; applying it to the NP-complete
-- target contradicts the supplied lower bound.
npCompleteOutsidePImpliesPNotEqualsNP :
  ∀ {Word : Set}
    {cost : PR.PolynomialCostModel Word}
    {target : PR.Language Word} →
  NPCompleteOutsideP cost target →
  PNotEqualsNP cost
npCompleteOutsidePImpliesPNotEqualsNP witness equality =
  targetNotInP witness
    (PR.npToP equality target
      (PR.targetInNP (complete witness)))
  where
    target = _

-- Once an NP-complete target is fixed, proving it is not in P is sufficient
-- for the Clay separation.
npCompleteTargetLowerBoundIsEnough :
  ∀ {Word : Set}
    {cost : PR.PolynomialCostModel Word}
    (target : PR.Language Word) →
  PR.NPComplete cost target →
  (PR.InP cost target → ⊥) →
  PNotEqualsNP cost
npCompleteTargetLowerBoundIsEnough target completeTarget lowerBound equality =
  lowerBound
    (PR.npToP equality target
      (PR.targetInNP completeTarget))

-- Conversely, P=NP forces every NP-complete target into P.
pEqualsNPForcesNPCompleteTargetInP :
  ∀ {Word : Set}
    {cost : PR.PolynomialCostModel Word}
    (target : PR.Language Word) →
  PR.NPComplete cost target →
  PR.PEqualsNP cost →
  PR.InP cost target
pEqualsNPForcesNPCompleteTargetInP target completeTarget equality =
  PR.npToP equality target (PR.targetInNP completeTarget)

record PrizeFacingPSeparationBoundary
    {Word : Set}
    (cost : PR.PolynomialCostModel Word)
    (target : PR.Language Word) : Setω where
  field
    targetNPComplete : PR.NPComplete cost target
    targetOutsideP : PR.InP cost target → ⊥
    separation : PNotEqualsNP cost

open PrizeFacingPSeparationBoundary public

makePrizeFacingPSeparationBoundary :
  ∀ {Word : Set}
    {cost : PR.PolynomialCostModel Word}
    {target : PR.Language Word} →
  PR.NPComplete cost target →
  (PR.InP cost target → ⊥) →
  PrizeFacingPSeparationBoundary cost target
makePrizeFacingPSeparationBoundary {target = target} completeTarget lowerBound = record
  { targetNPComplete = completeTarget
  ; targetOutsideP = lowerBound
  ; separation =
      npCompleteTargetLowerBoundIsEnough
        target completeTarget lowerBound
  }
