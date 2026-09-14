module DASHI.Core.FactorisationSpineCrosswalkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.CoarseFineFabricCalculusExact as Coarse

------------------------------------------------------------------------
-- FACTORISATION SPINE CROSSWALK
--
-- Several independently-developed Core lanes encode the same deterministic
-- factorisation law with domain-specific names.  This owner does not replace
-- those lanes.  It proves exact translations so future consumers can converge
-- on one canonical mathematical surface without deleting their extra structure
-- (query families, sectioned descent, conceptual/source attribution, etc.).
------------------------------------------------------------------------

queryFactorsToNonFactor :
  ∀ {State Surface QueryKey : Set}
    {questions : Query.InquiryQuestionFamily State QueryKey}
    {project : State → Surface}
    {query : QueryKey} →
  Query.FactorsThrough questions project query →
  NonFactor.FactorsThrough project (Query.ask questions query)
queryFactorsToNonFactor factor =
  NonFactor.factorsThrough
    (Query.quotientAnswer factor)
    (Query.factorisation factor)

nonFactorToQuery :
  ∀ {State Surface QueryKey : Set}
    (questions : Query.InquiryQuestionFamily State QueryKey)
    (query : QueryKey)
    {project : State → Surface} →
  NonFactor.FactorsThrough project (Query.ask questions query) →
  Query.FactorsThrough questions project query
nonFactorToQuery questions query factor =
  Query.factorsThrough
    (NonFactor.interpretFlat factor)
    (NonFactor.factorisation factor)

nonFactorToFactorized :
  ∀ {State Surface Outcome : Set}
    {project : State → Surface}
    {consumer : State → Outcome} →
  NonFactor.FactorsThrough project consumer →
  Factorized.FactorizedRefinement consumer project
nonFactorToFactorized factor =
  Factorized.factorizedRefinement
    (NonFactor.interpretFlat factor)
    (NonFactor.factorisation factor)

factorizedToNonFactor :
  ∀ {State Surface Outcome : Set}
    {project : State → Surface}
    {consumer : State → Outcome} →
  Factorized.FactorizedRefinement consumer project →
  NonFactor.FactorsThrough project consumer
factorizedToNonFactor factor =
  NonFactor.factorsThrough
    (Factorized.factor factor)
    (Factorized.factorizes factor)

queryFactorsToFactorized :
  ∀ {State Surface QueryKey : Set}
    {questions : Query.InquiryQuestionFamily State QueryKey}
    {project : State → Surface}
    {query : QueryKey} →
  Query.FactorsThrough questions project query →
  Factorized.FactorizedRefinement (Query.ask questions query) project
queryFactorsToFactorized factor =
  nonFactorToFactorized (queryFactorsToNonFactor factor)

------------------------------------------------------------------------
-- COLLISION / NON-DESCENT CROSSWALK
------------------------------------------------------------------------

projectionCollisionToNonFactorability :
  ∀ {State Surface Outcome : Set}
    {project : State → Surface}
    {consumer : State → Outcome} →
  Coarse.ProjectionCollision project consumer →
  NonFactor.NonFactorabilityWitness project consumer
projectionCollisionToNonFactorability collision =
  NonFactor.nonFactorabilityWitness
    (Coarse.left collision)
    (Coarse.right collision)
    (Coarse.sameProjection collision)
    (Coarse.consumerSeparates collision)

nonFactorabilityToProjectionCollision :
  ∀ {State Surface Outcome : Set}
    {project : State → Surface}
    {consumer : State → Outcome} →
  NonFactor.NonFactorabilityWitness project consumer →
  Coarse.ProjectionCollision project consumer
nonFactorabilityToProjectionCollision witness =
  Coarse.projectionCollision
    (NonFactor.left witness)
    (NonFactor.right witness)
    (NonFactor.sameFlatProjection witness)
    (NonFactor.situatedOutcomesDiffer witness)

projectionCollisionToNonDescent :
  ∀ {State Surface Outcome : Set}
    {project : State → Surface}
    {consumer : State → Outcome} →
  Coarse.ProjectionCollision project consumer →
  Descent.ConsumerNonDescentWitness project consumer
projectionCollisionToNonDescent collision =
  Descent.consumerNonDescentWitness
    (Coarse.left collision)
    (Coarse.right collision)
    (Coarse.sameProjection collision)
    (Coarse.consumerSeparates collision)

nonDescentToProjectionCollision :
  ∀ {State Surface Outcome : Set}
    {project : State → Surface}
    {consumer : State → Outcome} →
  Descent.ConsumerNonDescentWitness project consumer →
  Coarse.ProjectionCollision project consumer
nonDescentToProjectionCollision witness =
  Coarse.projectionCollision
    (Descent.left witness)
    (Descent.right witness)
    (Descent.sameSurface witness)
    (Descent.differentOutcome witness)

nonFactorabilityToNonDescent :
  ∀ {State Surface Outcome : Set}
    {project : State → Surface}
    {consumer : State → Outcome} →
  NonFactor.NonFactorabilityWitness project consumer →
  Descent.ConsumerNonDescentWitness project consumer
nonFactorabilityToNonDescent witness =
  projectionCollisionToNonDescent
    (nonFactorabilityToProjectionCollision witness)

nonDescentToNonFactorability :
  ∀ {State Surface Outcome : Set}
    {project : State → Surface}
    {consumer : State → Outcome} →
  Descent.ConsumerNonDescentWitness project consumer →
  NonFactor.NonFactorabilityWitness project consumer
nonDescentToNonFactorability witness =
  projectionCollisionToNonFactorability
    (nonDescentToProjectionCollision witness)

------------------------------------------------------------------------
-- Shared obstruction / repair theorems through the canonical crosswalk.
------------------------------------------------------------------------

projectionCollisionBlocksFactorizedRefinement :
  ∀ {State Surface Outcome : Set}
    {project : State → Surface}
    {consumer : State → Outcome} →
  Coarse.ProjectionCollision project consumer →
  Factorized.FactorizedRefinement consumer project →
  ⊥
projectionCollisionBlocksFactorizedRefinement collision factor =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (projectionCollisionToNonFactorability collision)
    (factorizedToNonFactor factor)

projectionCollisionRepairRequiresSeparation :
  ∀ {State Surface Refinement Outcome : Set}
    {project : State → Surface}
    {refine : State → Refinement}
    {consumer : State → Outcome} →
  (collision : Coarse.ProjectionCollision project consumer) →
  Repair.RefinementRepairs project refine consumer →
  refine (Coarse.left collision) ≡ refine (Coarse.right collision) →
  ⊥
projectionCollisionRepairRequiresSeparation collision =
  Repair.refinementRepairSeparatesWitness
    (projectionCollisionToNonDescent collision)

record FactorisationCrosswalkBoundary : Set where
  constructor factorisation-crosswalk-boundary
  field
    queryFactorisationTranslatesToCanonicalFactorisation : Bool
    canonicalFactorisationTranslatesToFactorizedRefinement : Bool
    projectionCollisionTranslatesToNonFactorability : Bool
    projectionCollisionTranslatesToConsumerNonDescent : Bool
    sufficientRepairMustSeparateWitnessedCollision : Bool
    separatingOneCollisionAloneProvesGlobalSufficiency : Bool
    queryIndexingStillAddsStructure : Bool
    sectionedProjectionStillAddsConstructiveDescentStructure : Bool
    historicalOwnersMustBeDeleted : Bool
    conceptualSourceRolesCollapseIntoMathematicalIdentity : Bool

canonicalFactorisationCrosswalkBoundary : FactorisationCrosswalkBoundary
canonicalFactorisationCrosswalkBoundary =
  factorisation-crosswalk-boundary
    true
    true
    true
    true
    true
    false
    true
    true
    false
    false
