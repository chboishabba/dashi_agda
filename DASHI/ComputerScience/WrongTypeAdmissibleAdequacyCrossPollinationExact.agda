module DASHI.ComputerScience.WrongTypeAdmissibleAdequacyCrossPollinationExact where

------------------------------------------------------------------------
-- WRONGTYPE / ADMISSIBLE / FACTORSTHROUGH / FUTURE-SAFETY WELD
--
-- Reuse only:
--
--   * WrongTypeAttributionFactorisationPlanningSnowballExact owns the indexed
--     mismatch vocabulary;
--   * AdmissibleConsumerFutureAdequacyExact owns the composed adequacy spine;
--   * QueryIndexedProjectionAdequacyExact owns present FactorsThrough defects.
--
-- The point is diagnostic precision.  "The detector failed" is not one type:
-- the query may be inadmissible, the observation may be non-factorable, the
-- future transport may be unsafe, or an otherwise valid map may be outside the
-- declared resource/access regime.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.WrongTypeAttributionFactorisationPlanningSnowballExact as Wrong
import DASHI.Core.AdmissibleConsumerFutureAdequacyExact as Adequacy
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

data AdequacyMismatch
    {State Action Observation QueryIndex Answer : Set}
    (ProjectRealizable : (State → Observation) → Set)
    (AnswerRealizable : (Observation → Answer) → Set)
    (problem :
      Adequacy.AdmissibleConsumerProblem
        State Action Observation QueryIndex Answer)
    (query : QueryIndex) : Set₁ where

  inadmissibleQuery :
    (Adequacy.AdmissibleQuery problem query → ⊥) →
    AdequacyMismatch
      ProjectRealizable AnswerRealizable problem query

  presentNonFactorable :
    Query.QueryAdequacyDefect
      (Adequacy.project problem)
      (Adequacy.semantics problem)
      query →
    AdequacyMismatch
      ProjectRealizable AnswerRealizable problem query

  futureLanguageUnsafe :
    (Adequacy.FutureSafe problem → ⊥) →
    AdequacyMismatch
      ProjectRealizable AnswerRealizable problem query

  projectionOutsideResourceRegime :
    (ProjectRealizable (Adequacy.project problem) → ⊥) →
    AdequacyMismatch
      ProjectRealizable AnswerRealizable problem query

  noRealizableFactorisingAnswer :
    ((coarseAnswer : Observation → Answer) →
      ((state : State) →
        Query.answer (Adequacy.semantics problem) query state
        ≡
        coarseAnswer (Adequacy.project problem state)) →
      AnswerRealizable coarseAnswer →
      ⊥) →
    AdequacyMismatch
      ProjectRealizable AnswerRealizable problem query

------------------------------------------------------------------------
-- Map the typed failure back into the existing abstract WrongType vocabulary.
------------------------------------------------------------------------

abstractWrongType :
  ∀ {State Action Observation QueryIndex Answer}
    {ProjectRealizable : (State → Observation) → Set}
    {AnswerRealizable : (Observation → Answer) → Set}
    {problem :
      Adequacy.AdmissibleConsumerProblem
        State Action Observation QueryIndex Answer}
    {query : QueryIndex} →
  AdequacyMismatch
    ProjectRealizable AnswerRealizable problem query →
  Wrong.AbstractWrongTypeMismatch
abstractWrongType (inadmissibleQuery _) =
  Wrong.wrongIndexedObligation
abstractWrongType (presentNonFactorable _) =
  Wrong.nonFactorableRepresentation
abstractWrongType (futureLanguageUnsafe _) =
  Wrong.invalidInferenceTransport
abstractWrongType (projectionOutsideResourceRegime _) =
  Wrong.wrongComputationalType
abstractWrongType (noRealizableFactorisingAnswer _) =
  Wrong.wrongComputationalType

------------------------------------------------------------------------
-- Every mismatch blocks the full admissible + operational + future package.
------------------------------------------------------------------------

mismatchBlocksFullAdequacy :
  ∀ {State Action Observation QueryIndex Answer}
    {ProjectRealizable : (State → Observation) → Set}
    {AnswerRealizable : (Observation → Answer) → Set}
    {problem :
      Adequacy.AdmissibleConsumerProblem
        State Action Observation QueryIndex Answer}
    {query : QueryIndex} →
  AdequacyMismatch
    ProjectRealizable AnswerRealizable problem query →
  Adequacy.AdmissibleOperationalFutureAdequacy
    ProjectRealizable AnswerRealizable problem query →
  ⊥
mismatchBlocksFullAdequacy
    (inadmissibleQuery notAdmissible)
    full =
  notAdmissible
    (Adequacy.operationalQueryAdmissible
      (Adequacy.operational full))

mismatchBlocksFullAdequacy
    (presentNonFactorable defect)
    full =
  Query.queryAdequacyDefectBlocksFactorisation
    defect
    presentFactorisation
  where
    presentFactorisation :
      Adequacy.AdequateNow _ _
    presentFactorisation =
      Query.factorsForQuery
        (Adequacy.coarseAnswer
          (Adequacy.operational full))
        (Adequacy.operationalFactorisation
          (Adequacy.operational full))

mismatchBlocksFullAdequacy
    (futureLanguageUnsafe unsafe)
    full =
  unsafe (Adequacy.futureSafe full)

mismatchBlocksFullAdequacy
    (projectionOutsideResourceRegime outside)
    full =
  outside
    (Adequacy.projectionRealizable
      (Adequacy.operational full))

mismatchBlocksFullAdequacy
    (noRealizableFactorisingAnswer impossible)
    full =
  impossible
    (Adequacy.coarseAnswer
      (Adequacy.operational full))
    (Adequacy.operationalFactorisation
      (Adequacy.operational full))
    (Adequacy.coarseAnswerRealizable
      (Adequacy.operational full))

------------------------------------------------------------------------
-- Diagnostic boundary.
------------------------------------------------------------------------

record AdequacyWrongTypeBoundary : Set where
  constructor adequacy-wrongtype-boundary
  field
    nonFactorabilityIsComputationalTypeError : Bool
    futureUnsafetyIsPresentFactorisationError : Bool
    resourceFailureNegatesSemanticFactorisation : Bool
    mismatchKindsRemainIndexed : Bool

open import Agda.Builtin.Bool using (Bool; false; true)

canonicalAdequacyWrongTypeBoundary : AdequacyWrongTypeBoundary
canonicalAdequacyWrongTypeBoundary =
  adequacy-wrongtype-boundary
    false false false true
