module DASHI.Physics.Closure.ShiftContractAnchoredTrajectoryFamily where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.ShiftContractAnchoredTriadicFamily as SATF
  using
    ( anchored0
    ; anchored1
    ; anchored2
    ; anchored-π-mdl-max-constant
    ; anchoredPrimeDistinct01
    ; anchoredPrimeDistinct02
    ; anchoredPrimeDistinct12
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractMdlLevelExplicitStateSearchAudit as ES
  using (oneHot0)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using
    ( ShiftContractState
    ; shiftContractStateTransportedPrimeEmbedding
    )
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using (TriadicIndex; i0; i1; i2)

------------------------------------------------------------------------
-- First trajectory-generated same-carrier family on the noncanonical seam.
--
-- Start from the broadest anchored support-width-two state and iterate the
-- live shift step.  The first three trajectory states stay inside one
-- `π-mdl-max` fibre while keeping pairwise distinct transported prime images;
-- the next live step collapses out of that fibre to the one-hot fixed point.

private
  ShiftC : EC.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

shiftStep : ShiftContractState → ShiftContractState
shiftStep = EC.Contract.step ShiftC

trajectoryGen : TriadicIndex → ShiftContractState
trajectoryGen i0 = anchored2
trajectoryGen i1 = anchored1
trajectoryGen i2 = anchored0

trajectoryStep01 :
  shiftStep (trajectoryGen i0) ≡ trajectoryGen i1
trajectoryStep01 = refl

trajectoryStep12 :
  shiftStep (trajectoryGen i1) ≡ trajectoryGen i2
trajectoryStep12 = refl

trajectoryStep2Exit :
  shiftStep (trajectoryGen i2) ≡ oneHot0
trajectoryStep2Exit = refl

trajectory-π-mdl-max-constant :
  ∀ i j →
  π-mdl-max (trajectoryGen i) ≡ π-mdl-max (trajectoryGen j)
trajectory-π-mdl-max-constant i0 i0 = refl
trajectory-π-mdl-max-constant i0 i1 = sym (anchored-π-mdl-max-constant i1 i2)
trajectory-π-mdl-max-constant i0 i2 = sym (anchored-π-mdl-max-constant i0 i2)
trajectory-π-mdl-max-constant i1 i0 = anchored-π-mdl-max-constant i1 i2
trajectory-π-mdl-max-constant i1 i1 = refl
trajectory-π-mdl-max-constant i1 i2 = sym (anchored-π-mdl-max-constant i0 i1)
trajectory-π-mdl-max-constant i2 i0 = anchored-π-mdl-max-constant i0 i2
trajectory-π-mdl-max-constant i2 i1 = anchored-π-mdl-max-constant i0 i1
trajectory-π-mdl-max-constant i2 i2 = refl

trajectoryPrimeDistinct01 :
  shiftContractStateTransportedPrimeEmbedding (trajectoryGen i0)
    ≢
  shiftContractStateTransportedPrimeEmbedding (trajectoryGen i1)
trajectoryPrimeDistinct01 eq = anchoredPrimeDistinct12 (sym eq)

trajectoryPrimeDistinct02 :
  shiftContractStateTransportedPrimeEmbedding (trajectoryGen i0)
    ≢
  shiftContractStateTransportedPrimeEmbedding (trajectoryGen i2)
trajectoryPrimeDistinct02 eq = anchoredPrimeDistinct02 (sym eq)

trajectoryPrimeDistinct12 :
  shiftContractStateTransportedPrimeEmbedding (trajectoryGen i1)
    ≢
  shiftContractStateTransportedPrimeEmbedding (trajectoryGen i2)
trajectoryPrimeDistinct12 eq = anchoredPrimeDistinct01 (sym eq)

trajectoryExitFibre :
  π-mdl-max (trajectoryGen i2)
    ≢
  π-mdl-max oneHot0
trajectoryExitFibre eq with cong proj₁ eq
... | ()

record ShiftContractAnchoredTrajectoryFamily : Set₁ where
  field
    gen : TriadicIndex → ShiftContractState
    sameSurface :
      ∀ i j →
      π-mdl-max (gen i) ≡ π-mdl-max (gen j)
    liveStep01 :
      shiftStep (gen i0) ≡ gen i1
    liveStep12 :
      shiftStep (gen i1) ≡ gen i2
    liveExit :
      shiftStep (gen i2) ≡ oneHot0
    primeSplit01 :
      shiftContractStateTransportedPrimeEmbedding (gen i0)
        ≢
      shiftContractStateTransportedPrimeEmbedding (gen i1)
    primeSplit02 :
      shiftContractStateTransportedPrimeEmbedding (gen i0)
        ≢
      shiftContractStateTransportedPrimeEmbedding (gen i2)
    primeSplit12 :
      shiftContractStateTransportedPrimeEmbedding (gen i1)
        ≢
      shiftContractStateTransportedPrimeEmbedding (gen i2)
    exitLeavesSurface :
      π-mdl-max (gen i2)
        ≢
      π-mdl-max oneHot0

canonicalShiftContractAnchoredTrajectoryFamily :
  ShiftContractAnchoredTrajectoryFamily
canonicalShiftContractAnchoredTrajectoryFamily =
  record
    { gen = trajectoryGen
    ; sameSurface = trajectory-π-mdl-max-constant
    ; liveStep01 = trajectoryStep01
    ; liveStep12 = trajectoryStep12
    ; liveExit = trajectoryStep2Exit
    ; primeSplit01 = trajectoryPrimeDistinct01
    ; primeSplit02 = trajectoryPrimeDistinct02
    ; primeSplit12 = trajectoryPrimeDistinct12
    ; exitLeavesSurface = trajectoryExitFibre
    }

open ShiftContractAnchoredTrajectoryFamily public
