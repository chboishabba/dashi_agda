module DASHI.Physics.YangMills.BalabanCommutingProjectionMartingaleExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact martingale orthogonality for four commuting self-adjoint projections.
--
-- This is the operator theorem underlying tensorization.  A concrete physical
-- block need only show that its four coordinate averages are linear,
-- idempotent, pairwise commuting and self-adjoint for the literal finite inner
-- product.  The six martingale cross terms then vanish here automatically.
------------------------------------------------------------------------

record ProjectionInnerCarrier (State Scalar : Set) : Set₁ where
  field
    subtractState : State → State → State
    subtractScalar : Scalar → Scalar → Scalar
    zeroScalar : Scalar
    inner : State → State → Scalar

    subtractSelfZero : ∀ scalar →
      subtractScalar scalar scalar ≡ zeroScalar

    innerSubtractLeft : ∀ left right test →
      inner (subtractState left right) test
      ≡ subtractScalar (inner left test) (inner right test)

open ProjectionInnerCarrier public

record SelfAdjointProjection
    {State Scalar : Set}
    (carrier : ProjectionInnerCarrier State Scalar) : Set₁ where
  field
    project : State → State
    projectSubtract : ∀ left right →
      project (subtractState carrier left right)
      ≡ subtractState carrier (project left) (project right)
    projectIdempotent : ∀ state → project (project state) ≡ project state
    projectSelfAdjoint : ∀ left right →
      inner carrier (project left) right
      ≡ inner carrier left (project right)

open SelfAdjointProjection public

residual :
  ∀ {State Scalar} {carrier : ProjectionInnerCarrier State Scalar} →
  SelfAdjointProjection carrier → State → State
residual {carrier = carrier} projection state =
  subtractState carrier state (project projection state)

FixedBy :
  ∀ {State Scalar} {carrier : ProjectionInnerCarrier State Scalar} →
  SelfAdjointProjection carrier → State → Set
FixedBy projection state = project projection state ≡ state

projectedIsFixed :
  ∀ {State Scalar} {carrier : ProjectionInnerCarrier State Scalar}
    (projection : SelfAdjointProjection carrier) state →
  FixedBy projection (project projection state)
projectedIsFixed = projectIdempotent

residualOrthogonalToFixed :
  ∀ {State Scalar} {carrier : ProjectionInnerCarrier State Scalar}
    (projection : SelfAdjointProjection carrier)
    state fixedState →
  FixedBy projection fixedState →
  inner carrier (residual projection state) fixedState
  ≡ zeroScalar carrier
residualOrthogonalToFixed {carrier = carrier}
  projection state fixedState fixed =
  trans
    (innerSubtractLeft carrier state (project projection state) fixedState)
    (trans
      (cong
        (subtractScalar carrier (inner carrier state fixedState))
        (trans
          (projectSelfAdjoint projection state fixedState)
          (cong (inner carrier state) fixed)))
      (subtractSelfZero carrier (inner carrier state fixedState)))

record FourCommutingProjections (State Scalar : Set) : Set₁ where
  field
    carrier : ProjectionInnerCarrier State Scalar
    projection0 projection1 projection2 projection3 :
      SelfAdjointProjection carrier

    commute01 : ∀ state →
      project projection0 (project projection1 state)
      ≡ project projection1 (project projection0 state)
    commute02 : ∀ state →
      project projection0 (project projection2 state)
      ≡ project projection2 (project projection0 state)
    commute03 : ∀ state →
      project projection0 (project projection3 state)
      ≡ project projection3 (project projection0 state)
    commute12 : ∀ state →
      project projection1 (project projection2 state)
      ≡ project projection2 (project projection1 state)
    commute13 : ∀ state →
      project projection1 (project projection3 state)
      ≡ project projection3 (project projection1 state)
    commute23 : ∀ state →
      project projection2 (project projection3 state)
      ≡ project projection3 (project projection2 state)

open FourCommutingProjections public

commutingResidualPreservesFixed :
  ∀ {State Scalar}
    {carrier : ProjectionInnerCarrier State Scalar}
    (fixedProjection residualProjection : SelfAdjointProjection carrier) →
  (∀ state →
    project fixedProjection (project residualProjection state)
    ≡ project residualProjection (project fixedProjection state)) →
  ∀ state → FixedBy fixedProjection state →
  FixedBy fixedProjection (residual residualProjection state)
commutingResidualPreservesFixed {carrier = carrier}
  fixedProjection residualProjection commute state fixed
  rewrite projectSubtract fixedProjection state
    (project residualProjection state)
  | fixed
  | commute state
  | fixed = refl

commutingProjectPreservesFixed :
  ∀ {State Scalar}
    {carrier : ProjectionInnerCarrier State Scalar}
    (fixedProjection movingProjection : SelfAdjointProjection carrier) →
  (∀ state →
    project fixedProjection (project movingProjection state)
    ≡ project movingProjection (project fixedProjection state)) →
  ∀ state → FixedBy fixedProjection state →
  FixedBy fixedProjection (project movingProjection state)
commutingProjectPreservesFixed fixedProjection movingProjection commute state fixed
  rewrite commute state | fixed = refl

average0 average01 average012 average0123 :
  ∀ {State Scalar} → FourCommutingProjections State Scalar → State → State
average0 dataSet state = project (projection0 dataSet) state
average01 dataSet state = project (projection1 dataSet) (average0 dataSet state)
average012 dataSet state = project (projection2 dataSet) (average01 dataSet state)
average0123 dataSet state = project (projection3 dataSet) (average012 dataSet state)

martingale0 martingale1 martingale2 martingale3 :
  ∀ {State Scalar} → FourCommutingProjections State Scalar → State → State
martingale0 dataSet state = residual (projection0 dataSet) state
martingale1 dataSet state = residual (projection1 dataSet) (average0 dataSet state)
martingale2 dataSet state = residual (projection2 dataSet) (average01 dataSet state)
martingale3 dataSet state = residual (projection3 dataSet) (average012 dataSet state)

average01Fixed0 :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  FixedBy (projection0 dataSet) (average01 dataSet state)
average01Fixed0 dataSet state =
  commutingProjectPreservesFixed
    (projection0 dataSet) (projection1 dataSet)
    (commute01 dataSet)
    (average0 dataSet state)
    (projectedIsFixed (projection0 dataSet) state)

average012Fixed0 :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  FixedBy (projection0 dataSet) (average012 dataSet state)
average012Fixed0 dataSet state =
  commutingProjectPreservesFixed
    (projection0 dataSet) (projection2 dataSet)
    (commute02 dataSet)
    (average01 dataSet state)
    (average01Fixed0 dataSet state)

average012Fixed1 :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  FixedBy (projection1 dataSet) (average012 dataSet state)
average012Fixed1 dataSet state =
  commutingProjectPreservesFixed
    (projection1 dataSet) (projection2 dataSet)
    (commute12 dataSet)
    (average01 dataSet state)
    (projectedIsFixed (projection1 dataSet) (average0 dataSet state))

martingale1Fixed0 :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  FixedBy (projection0 dataSet) (martingale1 dataSet state)
martingale1Fixed0 dataSet state =
  commutingResidualPreservesFixed
    (projection0 dataSet) (projection1 dataSet)
    (commute01 dataSet)
    (average0 dataSet state)
    (projectedIsFixed (projection0 dataSet) state)

martingale2Fixed0 :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  FixedBy (projection0 dataSet) (martingale2 dataSet state)
martingale2Fixed0 dataSet state =
  commutingResidualPreservesFixed
    (projection0 dataSet) (projection2 dataSet)
    (commute02 dataSet)
    (average01 dataSet state)
    (average01Fixed0 dataSet state)

martingale2Fixed1 :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  FixedBy (projection1 dataSet) (martingale2 dataSet state)
martingale2Fixed1 dataSet state =
  commutingResidualPreservesFixed
    (projection1 dataSet) (projection2 dataSet)
    (commute12 dataSet)
    (average01 dataSet state)
    (projectedIsFixed (projection1 dataSet) (average0 dataSet state))

martingale3Fixed0 :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  FixedBy (projection0 dataSet) (martingale3 dataSet state)
martingale3Fixed0 dataSet state =
  commutingResidualPreservesFixed
    (projection0 dataSet) (projection3 dataSet)
    (commute03 dataSet)
    (average012 dataSet state)
    (average012Fixed0 dataSet state)

martingale3Fixed1 :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  FixedBy (projection1 dataSet) (martingale3 dataSet state)
martingale3Fixed1 dataSet state =
  commutingResidualPreservesFixed
    (projection1 dataSet) (projection3 dataSet)
    (commute13 dataSet)
    (average012 dataSet state)
    (average012Fixed1 dataSet state)

martingale3Fixed2 :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  FixedBy (projection2 dataSet) (martingale3 dataSet state)
martingale3Fixed2 dataSet state =
  commutingResidualPreservesFixed
    (projection2 dataSet) (projection3 dataSet)
    (commute23 dataSet)
    (average012 dataSet state)
    (projectedIsFixed (projection2 dataSet) (average01 dataSet state))

martingale01Orthogonal martingale02Orthogonal martingale03Orthogonal
  martingale12Orthogonal martingale13Orthogonal martingale23Orthogonal :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  Scalar
martingale01Orthogonal dataSet state =
  inner (carrier dataSet) (martingale0 dataSet state) (martingale1 dataSet state)
martingale02Orthogonal dataSet state =
  inner (carrier dataSet) (martingale0 dataSet state) (martingale2 dataSet state)
martingale03Orthogonal dataSet state =
  inner (carrier dataSet) (martingale0 dataSet state) (martingale3 dataSet state)
martingale12Orthogonal dataSet state =
  inner (carrier dataSet) (martingale1 dataSet state) (martingale2 dataSet state)
martingale13Orthogonal dataSet state =
  inner (carrier dataSet) (martingale1 dataSet state) (martingale3 dataSet state)
martingale23Orthogonal dataSet state =
  inner (carrier dataSet) (martingale2 dataSet state) (martingale3 dataSet state)

martingale01Zero :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  martingale01Orthogonal dataSet state ≡ zeroScalar (carrier dataSet)
martingale01Zero dataSet state =
  residualOrthogonalToFixed
    (projection0 dataSet) state (martingale1 dataSet state)
    (martingale1Fixed0 dataSet state)

martingale02Zero :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  martingale02Orthogonal dataSet state ≡ zeroScalar (carrier dataSet)
martingale02Zero dataSet state =
  residualOrthogonalToFixed
    (projection0 dataSet) state (martingale2 dataSet state)
    (martingale2Fixed0 dataSet state)

martingale03Zero :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  martingale03Orthogonal dataSet state ≡ zeroScalar (carrier dataSet)
martingale03Zero dataSet state =
  residualOrthogonalToFixed
    (projection0 dataSet) state (martingale3 dataSet state)
    (martingale3Fixed0 dataSet state)

martingale12Zero :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  martingale12Orthogonal dataSet state ≡ zeroScalar (carrier dataSet)
martingale12Zero dataSet state =
  residualOrthogonalToFixed
    (projection1 dataSet) (average0 dataSet state) (martingale2 dataSet state)
    (martingale2Fixed1 dataSet state)

martingale13Zero :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  martingale13Orthogonal dataSet state ≡ zeroScalar (carrier dataSet)
martingale13Zero dataSet state =
  residualOrthogonalToFixed
    (projection1 dataSet) (average0 dataSet state) (martingale3 dataSet state)
    (martingale3Fixed1 dataSet state)

martingale23Zero :
  ∀ {State Scalar} (dataSet : FourCommutingProjections State Scalar) state →
  martingale23Orthogonal dataSet state ≡ zeroScalar (carrier dataSet)
martingale23Zero dataSet state =
  residualOrthogonalToFixed
    (projection2 dataSet) (average01 dataSet state) (martingale3 dataSet state)
    (martingale3Fixed2 dataSet state)

commutingProjectionMartingaleOrthogonalityLevel : ProofLevel
commutingProjectionMartingaleOrthogonalityLevel = machineChecked

physicalAxisAverageSelfAdjointnessLevel : ProofLevel
physicalAxisAverageSelfAdjointnessLevel = conditional
