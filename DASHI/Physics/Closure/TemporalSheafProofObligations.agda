module DASHI.Physics.Closure.TemporalSheafProofObligations where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ)
open import Data.Sum using (_⊎_)

------------------------------------------------------------------------
-- Minimal temporal-sheaf proof-obligation interfaces.
--
-- These records do not claim that the current DASHI stack has a temporal
-- sheaf semantics.  They name the small surfaces needed to promote temporal
-- qualifiers from statement metadata into a time-indexed state-space model.

record TemporalSheafObligation : Set₁ where
  field
    Time Section Value Global : Set

    -- A section is only meaningful where it is valid over the time base.
    validAt :
      Section → Time → Set

    valueAt :
      (s : Section) →
      (t : Time) →
      validAt s t →
      Value

  -- Overlap and compatibility are separate: two sections can overlap but
  -- fail the gluing condition.
  field
    overlapRel :
      Section → Section → Set

    compatible :
      Section → Section → Set

    compatibleSound :
      ∀ s₁ s₂ →
      compatible s₁ s₂ →
      ∀ t →
      (p₁ : validAt s₁ t) →
      (p₂ : validAt s₂ t) →
      valueAt s₁ t p₁ ≡ valueAt s₂ t p₂

  -- `MereViol` is the explicit non-gluability certificate.
  field
    MereViol :
      Section → Section → Set

    mereViolSound :
      ∀ s₁ s₂ →
      MereViol s₁ s₂ →
      compatible s₁ s₂ →
      ⊥

    Glues :
      Global → Section → Section → Set

    glue :
      ∀ s₁ s₂ →
      compatible s₁ s₂ →
      Σ Global (λ g → Glues g s₁ s₂)

  -- Exclusive properties are the line-bundle case: at most one value can
  -- inhabit the fibre over a time point.
  field
    Exclusive :
      Set

    exclusiveSingleValued :
      Exclusive →
      ∀ s₁ s₂ t →
      (p₁ : validAt s₁ t) →
      (p₂ : validAt s₂ t) →
      valueAt s₁ t p₁ ≡ valueAt s₂ t p₂

------------------------------------------------------------------------
-- A JFixed/+1 reading as a temporal object needs a topology transition, not
-- merely a rotation inside one fixed time base.

record JFixedSheafTransitionObligation : Set₁ where
  field
    preSheaf postSheaf :
      TemporalSheafObligation

    carry :
      TemporalSheafObligation.Section preSheaf →
      TemporalSheafObligation.Section postSheaf

    topologyChanges :
      Set

    postAdmissible :
      TemporalSheafObligation.Section preSheaf → Set

    invalidatedByTransition :
      TemporalSheafObligation.Section preSheaf → Set

    invalidatedBlocksCarry :
      ∀ s →
      invalidatedByTransition s →
      postAdmissible s →
      ⊥

    -- This keeps the `+1` claim separate from ordinary CRT-period recurrence.
    notJustPeriodStep :
      topologyChanges

------------------------------------------------------------------------
-- Temporal distance over sections is a separate obligation from the existing
-- agreement ultrametrics over flat ternary carriers.

record TemporalSectionMetricObligation : Set₁ where
  field
    sheaf :
      TemporalSheafObligation

    Distance :
      Set

    zeroD :
      Distance

    _≤D_ :
      Distance → Distance → Set

    maxD :
      Distance → Distance → Distance

    compatibleRadius :
      Distance

    d :
      TemporalSheafObligation.Section sheaf →
      TemporalSheafObligation.Section sheaf →
      Distance

    identity :
      ∀ s → d s s ≡ zeroD

    symmetry :
      ∀ s₁ s₂ → d s₁ s₂ ≡ d s₂ s₁

    strongTriangle :
      ∀ s₁ s₂ s₃ →
      d s₁ s₃ ≤D maxD (d s₁ s₂) (d s₂ s₃)

    compatibleBound :
      ∀ s₁ s₂ →
      TemporalSheafObligation.compatible sheaf s₁ s₂ →
      d s₁ s₂ ≤D compatibleRadius

------------------------------------------------------------------------
-- Co-location receipt for the three temporal promotion gates.

record TemporalStateSpaceReceipt : Set₁ where
  field
    sheaf :
      TemporalSheafObligation

    transition :
      JFixedSheafTransitionObligation

    sectionMetric :
      TemporalSectionMetricObligation

------------------------------------------------------------------------
-- Spacetime extension of the temporal-sheaf obligation.
--
-- This is still only an obligation surface.  It records what must be supplied
-- before spatial containment properties can be read together with temporal
-- qualifiers as one spacetime-indexed state space.

record SpacetimeSheafObligation : Set₁ where
  field
    Time Space Section Value Global :
      Set

    -- Space is the mereological carrier.  The relation is intentionally
    -- abstract: a concrete instance may use containment, location, or another
    -- checked spatial/mereological ordering.
    _⊑space_ :
      Space → Space → Set

    spatialOverlap :
      Space → Space → Set

    -- Sections now live over coordinates in Time x Space.
    validAt :
      Section → Time → Space → Set

    valueAt :
      (s : Section) →
      (t : Time) →
      (x : Space) →
      validAt s t x →
      Value

  field
    overlapRel :
      Section → Section → Set

    compatible :
      Section → Section → Set

    compatibleSound :
      ∀ s₁ s₂ →
      compatible s₁ s₂ →
      ∀ t x →
      (p₁ : validAt s₁ t x) →
      (p₂ : validAt s₂ t x) →
      valueAt s₁ t x p₁ ≡ valueAt s₂ t x p₂

    SpacetimeMereViol :
      Section → Section → Set

    spacetimeMereViolSound :
      ∀ s₁ s₂ →
      SpacetimeMereViol s₁ s₂ →
      compatible s₁ s₂ →
      ⊥

    Glues :
      Global → Section → Section → Set

    glue :
      ∀ s₁ s₂ →
      compatible s₁ s₂ →
      Σ Global (λ g → Glues g s₁ s₂)

  -- Exclusive properties are single-valued at each spacetime coordinate.
  field
    Exclusive :
      Set

    exclusiveSpacetimeSingleValued :
      Exclusive →
      ∀ s₁ s₂ t x →
      (p₁ : validAt s₁ t x) →
      (p₂ : validAt s₂ t x) →
      valueAt s₁ t x p₁ ≡ valueAt s₂ t x p₂

------------------------------------------------------------------------
-- Cauchy-style evolution for spacetime-indexed ontology slices.
--
-- This does not claim general relativity.  It only names the obligation needed
-- to read `S ⊕ delta -> S'` as a constrained evolution of one valid slice into
-- another.

record CauchyEvolutionObligation : Set₁ where
  field
    spacetime :
      SpacetimeSheafObligation

    Slice Delta :
      Set

    sliceSection :
      Slice → SpacetimeSheafObligation.Section spacetime

    _⊕_ :
      Slice → Delta → Slice

    admissible :
      Delta → Slice → Set

    validSlice :
      Slice → Set

    evolutionPreservesValidity :
      ∀ s δ →
      validSlice s →
      admissible δ s →
      validSlice (s ⊕ δ)

------------------------------------------------------------------------
-- JFixed/+1 as a spacetime topology-change obligation.
--
-- A singularity reading needs proof that the old spacetime sheaf cannot be
-- extended through the proposed point, plus a post-transition carrier.  It is
-- not discharged by a scalar period identity or a temporal sheaf transition
-- alone.

record JFixedSpacetimeTransitionObligation : Set₁ where
  field
    preSpacetime postSpacetime :
      SpacetimeSheafObligation

    preEvolution postEvolution :
      CauchyEvolutionObligation

    extendThroughJ :
      SpacetimeSheafObligation.Section preSpacetime → Set

    extensionObstruction :
      SpacetimeSheafObligation.Section preSpacetime → Set

    obstructionBlocksExtension :
      ∀ s →
      extensionObstruction s →
      extendThroughJ s →
      ⊥

    topologyChanges :
      Set

    notMerelyTemporal :
      topologyChanges

    notMerelyCRTStep :
      topologyChanges

------------------------------------------------------------------------
-- Co-location receipt for spacetime promotion gates.

record SpacetimeStateSpaceReceipt : Set₁ where
  field
    spacetime :
      SpacetimeSheafObligation

    evolution :
      CauchyEvolutionObligation

    transition :
      JFixedSpacetimeTransitionObligation
