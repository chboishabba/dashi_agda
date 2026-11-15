module DASHI.Governance.EpistemicPowerMinimalObserverRepairExact where

-- DASHI constructive query-specific observer repair.
-- The Boolean commitment coordinates are ONLY a finite countermodel;
-- they do not operationalize Indigenous land rights or sovereignty.
-- The point is informational: a coarse inclusion indicator loses
-- distinctions, while explicitly adding the queried distinctions
-- provides an adequate observer for the specified query language.

open import DASHI.Core.Prelude

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.EpistemicPowerHistoryAndNonSubstitutionExact as History
import DASHI.Governance.EpistemicPowerQueryAdequacyCapstoneExact as Base

CommitmentWorld : Set
CommitmentWorld = History.CommitmentsState

-- A two-coordinate augmentation is a sufficient observation for the
-- THREE specified queries: inclusion, land flag, sovereignty flag.
repairedObserver : CommitmentWorld → Bool × Bool
repairedObserver state =
  History.landCommitment state , History.sovereigntyCommitment state

landOnlyObserver : CommitmentWorld → Bool
landOnlyObserver = History.landCommitment

sovereigntyOnlyObserver : CommitmentWorld → Bool
sovereigntyOnlyObserver = History.sovereigntyCommitment

repairedInclusionQueryAdequate :
  Query.AdequateFor
    repairedObserver Base.commitmentSemantics Base.inclusionReported
repairedInclusionQueryAdequate =
  Query.factorsForQuery
    {project = repairedObserver}
    {semantics = Base.commitmentSemantics}
    {query = Base.inclusionReported}
    (λ observation → true)
    (λ state → refl)

repairedLandQueryAdequate :
  Query.AdequateFor
    repairedObserver Base.commitmentSemantics Base.landRequirement
repairedLandQueryAdequate =
  Query.factorsForQuery
    {project = repairedObserver}
    {semantics = Base.commitmentSemantics}
    {query = Base.landRequirement}
    proj₁
    (λ state → refl)

repairedSovereigntyQueryAdequate :
  Query.AdequateFor
    repairedObserver Base.commitmentSemantics Base.sovereigntyRequirement
repairedSovereigntyQueryAdequate =
  Query.factorsForQuery
    {project = repairedObserver}
    {semantics = Base.commitmentSemantics}
    {query = Base.sovereigntyRequirement}
    proj₂
    (λ state → refl)

-- Negative controls: one new coordinate is insufficient for the other
-- independent query in the closed four-world carrier.
landOnlyCannotAnswerSovereignty :
  INF.NonFactorabilityWitness
    landOnlyObserver History.sovereigntyCommitment
landOnlyCannotAnswerSovereignty =
  INF.nonFactorabilityWitness
    History.neitherCommitment History.sovereigntyOnly
    refl (λ ())

sovereigntyOnlyCannotAnswerLand :
  INF.NonFactorabilityWitness
    sovereigntyOnlyObserver History.landCommitment
sovereigntyOnlyCannotAnswerLand =
  INF.nonFactorabilityWitness
    History.neitherCommitment History.landOnly
    refl (λ ())

landOnlyQueryNotAdequateForSovereignty :
  Query.AdequateFor
    landOnlyObserver Base.commitmentSemantics Base.sovereigntyRequirement → ⊥
landOnlyQueryNotAdequateForSovereignty =
  INF.witnessRulesOutEveryFlatFactorisation
    landOnlyCannotAnswerSovereignty

sovereigntyOnlyQueryNotAdequateForLand :
  Query.AdequateFor
    sovereigntyOnlyObserver Base.commitmentSemantics Base.landRequirement → ⊥
sovereigntyOnlyQueryNotAdequateForLand =
  INF.witnessRulesOutEveryFlatFactorisation
    sovereigntyOnlyCannotAnswerLand

-- No postprocessing of an inadequate one-coordinate observer
-- reconstructs the other coordinate.
landRechartCannotRecoverSovereignty :
  ∀ {R : Set} (f : Bool → R) →
  INF.FactorsThrough
    (λ state → f (landOnlyObserver state))
    History.sovereigntyCommitment → ⊥
landRechartCannotRecoverSovereignty f =
  INF.rechartingCannotRecoverErasedPhenomenon
    f landOnlyCannotAnswerSovereignty

sovereigntyRechartCannotRecoverLand :
  ∀ {R : Set} (f : Bool → R) →
  INF.FactorsThrough
    (λ state → f (sovereigntyOnlyObserver state))
    History.landCommitment → ⊥
sovereigntyRechartCannotRecoverLand f =
  INF.rechartingCannotRecoverErasedPhenomenon
    f sovereigntyOnlyCannotAnswerLand

record FiniteMinimalObserverRepair : Set₁ where
  constructor finite-minimal-observer-repair
  field
    inclusionRepaired :
      Query.AdequateFor
        repairedObserver Base.commitmentSemantics Base.inclusionReported
    landRepaired :
      Query.AdequateFor
        repairedObserver Base.commitmentSemantics Base.landRequirement
    sovereigntyRepaired :
      Query.AdequateFor
        repairedObserver Base.commitmentSemantics Base.sovereigntyRequirement
    landAloneInsufficient :
      Query.AdequateFor
        landOnlyObserver Base.commitmentSemantics Base.sovereigntyRequirement → ⊥
    sovereigntyAloneInsufficient :
      Query.AdequateFor
        sovereigntyOnlyObserver Base.commitmentSemantics Base.landRequirement → ⊥

finiteMinimalObserverRepair : FiniteMinimalObserverRepair
finiteMinimalObserverRepair =
  finite-minimal-observer-repair
    repairedInclusionQueryAdequate
    repairedLandQueryAdequate
    repairedSovereigntyQueryAdequate
    landOnlyQueryNotAdequateForSovereignty
    sovereigntyOnlyQueryNotAdequateForLand
