module DASHI.Dynamics.PNFOperatorLocalityResolution where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.StageAtlasZeroToEleven as Atlas

------------------------------------------------------------------------
-- Exact product-lane locality.
--
-- Updates supported on separate coordinates commute by construction.  This is
-- an algebraic locality theorem only; it does not imply metric orthogonality,
-- spectral independence, or absence of later coupling operators.
------------------------------------------------------------------------

record PairState (Left Right : Set) : Set where
  constructor pairState
  field
    left : Left
    right : Right

updateLeft :
  ∀ {Left Right} →
  (Left → Left) →
  PairState Left Right →
  PairState Left Right
updateLeft operation state =
  pairState (operation (PairState.left state)) (PairState.right state)

updateRight :
  ∀ {Left Right} →
  (Right → Right) →
  PairState Left Right →
  PairState Left Right
updateRight operation state =
  pairState (PairState.left state) (operation (PairState.right state))

disjointCoordinateUpdatesCommute :
  ∀ {Left Right}
    (leftOperation : Left → Left)
    (rightOperation : Right → Right)
    (state : PairState Left Right) →
  updateLeft leftOperation (updateRight rightOperation state) ≡
  updateRight rightOperation (updateLeft leftOperation state)
disjointCoordinateUpdatesCommute leftOperation rightOperation state = refl

------------------------------------------------------------------------
-- A nontrivial idempotent quotient cannot also be an involution.
------------------------------------------------------------------------

record IdempotentProjection (A : Set) : Set₁ where
  field
    project : A → A
    idempotent : ∀ value → project (project value) ≡ project value

record NontrivialIdempotentProjection (A : Set) : Set₁ where
  field
    projection : IdempotentProjection A
    witness : A
    witnessChanges :
      ¬ (IdempotentProjection.project projection witness ≡ witness)

nontrivialIdempotentProjectionNotInvolutive :
  ∀ {A} (projection : NontrivialIdempotentProjection A) →
  ¬ ((value : A) →
      IdempotentProjection.project
        (NontrivialIdempotentProjection.projection projection)
        (IdempotentProjection.project
          (NontrivialIdempotentProjection.projection projection)
          value)
      ≡ value)
nontrivialIdempotentProjectionNotInvolutive projection involutive =
  NontrivialIdempotentProjection.witnessChanges projection
    (trans
      (sym
        (IdempotentProjection.idempotent
          (NontrivialIdempotentProjection.projection projection)
          (NontrivialIdempotentProjection.witness projection)))
      (involutive (NontrivialIdempotentProjection.witness projection)))

record ResolutionDynamics (State Measure : Set) : Set₁ where
  field
    resolve : State → State
    measure : State → Measure
    StrictlyBelow : Measure → Measure → Set
    strictDescent :
      ∀ state → StrictlyBelow (measure (resolve state)) (measure state)
    nontrivialProjection : NontrivialIdempotentProjection State
    resolveIsProjection :
      IdempotentProjection.project
        (NontrivialIdempotentProjection.projection nontrivialProjection)
      ≡ resolve

record Stage10ResolutionCandidate (State : Set) : Set₁ where
  field
    stage : Atlas.StageAtlasZeroToEleven
    stageIsTen : stage ≡ Atlas.atlas-10
    projection : NontrivialIdempotentProjection State
    nonInvolutive :
      ¬ ((value : State) →
          IdempotentProjection.project
            (NontrivialIdempotentProjection.projection projection)
            (IdempotentProjection.project
              (NontrivialIdempotentProjection.projection projection)
              value)
          ≡ value)
    stageInterpretationCandidateOnly : Bool
    observerCausesPhysicalCollapseClaimed : Bool

record OperatorLocalityResolutionBoundary : Set where
  field
    disjointProductUpdatesCommute : Bool
    arbitraryPrimeLaneOperatorsCommute : Bool
    commutationImpliesMetricOrthogonality : Bool
    commutationImpliesSpectralIndependence : Bool
    nontrivialIdempotentCannotBeInvolution : Bool
    stage10MeaningPromoted : Bool
    boundaryNote : String

canonicalOperatorLocalityResolutionBoundary :
  OperatorLocalityResolutionBoundary
canonicalOperatorLocalityResolutionBoundary = record
  { disjointProductUpdatesCommute = true
  ; arbitraryPrimeLaneOperatorsCommute = false
  ; commutationImpliesMetricOrthogonality = false
  ; commutationImpliesSpectralIndependence = false
  ; nontrivialIdempotentCannotBeInvolution = true
  ; stage10MeaningPromoted = false
  ; boundaryNote =
      "Product-supported updates commute exactly; nontrivial idempotent resolution is non-involutive. Metric, spectral and stage semantics require separate witnesses."
  }
