module DASHI.Environment.TaskFactorisationQuerySufficiencyBridgeExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Round 1 introduced an LES-local `TaskFactorisation`.  The repository already
-- owns the more general query-factorisation surface in
-- `DASHI.Core.QueryFactorisationSufficiency`.  This module proves the LES object
-- is an instance of that existing core rather than allowing a parallel theory.
------------------------------------------------------------------------

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Environment.LESResearchCrossPollinationExact as LES

constantOutputQuestions :
  ∀ {State Task Output : Set} →
  (Task → State → Output) →
  Query.InquiryQuestionFamily State Task
constantOutputQuestions {Output = Output} evaluate =
  Query.inquiryQuestionFamily (λ task → Output) evaluate

taskFactorisationToStaticSufficient :
  ∀ {State Representation Task Output : Set}
    {project : State → Representation}
    {evaluate : Task → State → Output} →
  LES.TaskFactorisation project evaluate →
  Query.StaticSufficient (constantOutputQuestions evaluate) project
taskFactorisationToStaticSufficient {Task = Task} {project = project}
  {evaluate = evaluate} factor =
  Query.staticSufficient proofFor
  where
    proofFor :
      (task : Task) →
      Query.FactorsThrough (constantOutputQuestions evaluate) project task
    proofFor task =
      Query.factorsThrough
        (LES.evaluateReduced factor task)
        (LES.factorises factor task)
