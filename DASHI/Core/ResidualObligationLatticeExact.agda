module DASHI.Core.ResidualObligationLatticeExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- RECONSTRUCTION OBLIGATION LATTICE
--
-- A stronger reconstruction relation distinguishes at least as much fine
-- structure.  Residual obligations therefore move contravariantly: satisfying
-- a stronger relation implies satisfying every weaker relation, while a
-- residual sufficient only for a weaker relation may collapse distinctions a
-- stronger consumer still requires.
------------------------------------------------------------------------

record RelationRefines
    {State : Set}
    (strong weak : State → State → Set) : Set₁ where
  constructor relationRefines
  field
    refinement : ∀ {left right} → strong left right → weak left right

open RelationRefines public

record ResidualReopening
    (State Coarse Residual : Set)
    (Relation : State → State → Set)
    (coarsen : State → Coarse)
    (residual : State → Residual) : Set₁ where
  constructor residualReopening
  field
    reopen : Coarse → Residual → State
    reopenRelated :
      (state : State) → Relation (reopen (coarsen state) (residual state)) state

open ResidualReopening public

strongResidualAlsoSatisfiesWeakerObligation :
  ∀ {State Coarse Residual}
    {strong weak : State → State → Set}
    {coarsen : State → Coarse}
    {residual : State → Residual} →
  RelationRefines strong weak →
  ResidualReopening State Coarse Residual strong coarsen residual →
  ResidualReopening State Coarse Residual weak coarsen residual
strongResidualAlsoSatisfiesWeakerObligation refinementProof strongReceipt =
  residualReopening
    (reopen strongReceipt)
    (λ state → refinement refinementProof (reopenRelated strongReceipt state))

------------------------------------------------------------------------
-- Information lower bound induced by strict refinement.
-- If a weaker relation identifies two states but a stronger relation does not,
-- any pair-code certified for the stronger relation must distinguish them.
------------------------------------------------------------------------

record PairCodeSufficient
    (State Coarse Residual : Set)
    (Relation : State → State → Set)
    (coarsen : State → Coarse)
    (residual : State → Residual) : Set₁ where
  constructor pairCodeSufficient
  field
    samePairImpliesRelated :
      ∀ {left right} →
      coarsen left ≡ coarsen right →
      residual left ≡ residual right →
      Relation left right

open PairCodeSufficient public

strictlyStrongerObligationForcesResidualDistinction :
  ∀ {State Coarse Residual}
    {strong weak : State → State → Set}
    {coarsen : State → Coarse}
    {residual : State → Residual}
    (safeStrong : PairCodeSufficient State Coarse Residual strong coarsen residual)
    {left right : State} →
  coarsen left ≡ coarsen right →
  weak left right →
  (strong left right → ⊥) →
  residual left ≡ residual right → ⊥
strictlyStrongerObligationForcesResidualDistinction
  safeStrong coarseEqual weakRelated strongDistinct residualEqual =
  strongDistinct
    (samePairImpliesRelated safeStrong coarseEqual residualEqual)

------------------------------------------------------------------------
-- Canonical four-level vocabulary.  The relations themselves stay supplied by
-- applications; this type only prevents compute/semantic/provenance/exact
-- obligations from being silently conflated.
------------------------------------------------------------------------

data ReconstructionLevel : Set where
  computeLevel semanticLevel provenanceLevel exactLevel : ReconstructionLevel

record ReconstructionHierarchy
    (State : Set)
    (compute semantic provenance exact : State → State → Set) : Set₁ where
  constructor reconstructionHierarchy
  field
    exactRefinesProvenance : RelationRefines exact provenance
    provenanceRefinesSemantic : RelationRefines provenance semantic
    semanticRefinesCompute : RelationRefines semantic compute

open ReconstructionHierarchy public

exactRefinesSemantic :
  ∀ {State}
    {compute semantic provenance exact : State → State → Set} →
  ReconstructionHierarchy State compute semantic provenance exact →
  RelationRefines exact semantic
exactRefinesSemantic hierarchy =
  relationRefines λ exactRelated →
    refinement (provenanceRefinesSemantic hierarchy)
      (refinement (exactRefinesProvenance hierarchy) exactRelated)

exactRefinesCompute :
  ∀ {State}
    {compute semantic provenance exact : State → State → Set} →
  ReconstructionHierarchy State compute semantic provenance exact →
  RelationRefines exact compute
exactRefinesCompute hierarchy =
  relationRefines λ exactRelated →
    refinement (semanticRefinesCompute hierarchy)
      (refinement (exactRefinesSemantic hierarchy) exactRelated)

------------------------------------------------------------------------
-- No numerical code-length inequality is asserted without a finite-cardinality
-- model; the theorem above supplies the reusable pairwise lower-bound engine.
------------------------------------------------------------------------
