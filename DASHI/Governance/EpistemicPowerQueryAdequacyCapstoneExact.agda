module DASHI.Governance.EpistemicPowerQueryAdequacyCapstoneExact where

-- Finite query-specific adequacy proof; not a model of actual Indigenous sovereignty.
open import DASHI.Core.Prelude
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Governance.EpistemicPowerHistoryAndNonSubstitutionExact as Hist

data CommitmentQuery : Set where
  inclusionReported landRequirement sovereigntyRequirement : CommitmentQuery

answerCommitment :
  CommitmentQuery → Hist.CommitmentsState → Bool
answerCommitment inclusionReported state = true
answerCommitment landRequirement state = Hist.landCommitment state
answerCommitment sovereigntyRequirement state = Hist.sovereigntyCommitment state

commitmentSemantics :
  Query.QuerySemantics Hist.CommitmentsState CommitmentQuery Bool
commitmentSemantics = Query.querySemantics answerCommitment

inclusionQueryAdequate :
  Query.AdequateFor
    Hist.inclusionReport commitmentSemantics inclusionReported
inclusionQueryAdequate =
  Query.factorsForQuery
    {project = Hist.inclusionReport}
    {semantics = commitmentSemantics}
    {query = inclusionReported}
    (λ observation → true)
    (λ state → refl)

landQueryDefect :
  Query.QueryAdequacyDefect
    Hist.inclusionReport commitmentSemantics landRequirement
landQueryDefect =
  Query.queryAdequacyDefect
    {project = Hist.inclusionReport}
    {semantics = commitmentSemantics}
    {query = landRequirement}
    Hist.neitherCommitment Hist.landOnly refl (λ ())

sovereigntyQueryDefect :
  Query.QueryAdequacyDefect
    Hist.inclusionReport commitmentSemantics sovereigntyRequirement
sovereigntyQueryDefect =
  Query.queryAdequacyDefect
    {project = Hist.inclusionReport}
    {semantics = commitmentSemantics}
    {query = sovereigntyRequirement}
    Hist.neitherCommitment Hist.sovereigntyOnly refl (λ ())

landQueryInadequate :
  Query.AdequateFor
    Hist.inclusionReport commitmentSemantics landRequirement → ⊥
landQueryInadequate =
  Query.queryAdequacyDefectBlocksFactorisation landQueryDefect

sovereigntyQueryInadequate :
  Query.AdequateFor
    Hist.inclusionReport commitmentSemantics sovereigntyRequirement → ⊥
sovereigntyQueryInadequate =
  Query.queryAdequacyDefectBlocksFactorisation sovereigntyQueryDefect

record InclusionAdequacyIsQueryRelative : Set₁ where
  constructor inclusion-adequacy-is-query-relative
  field
    inclusionAdequate :
      Query.AdequateFor
        Hist.inclusionReport commitmentSemantics inclusionReported
    landDefect :
      Query.QueryAdequacyDefect
        Hist.inclusionReport commitmentSemantics landRequirement
    sovereigntyDefect :
      Query.QueryAdequacyDefect
        Hist.inclusionReport commitmentSemantics sovereigntyRequirement

inclusionDoesNotSubstituteForDecolonialCommitments :
  InclusionAdequacyIsQueryRelative
inclusionDoesNotSubstituteForDecolonialCommitments =
  inclusion-adequacy-is-query-relative
    inclusionQueryAdequate landQueryDefect sovereigntyQueryDefect
