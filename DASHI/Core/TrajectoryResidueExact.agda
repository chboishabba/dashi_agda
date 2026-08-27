module DASHI.Core.TrajectoryResidueExact where

------------------------------------------------------------------------
-- TRAJECTORY-DEPOSITED RESIDUE
--
-- Generic DASHI seam for situations where a present state carries information
-- deposited by the path that produced it.  This is deliberately smaller than a
-- dynamical-systems framework: applications supply a transition relation and a
-- state observer for the retained residue.
--
-- The reusable theorem shape is:
--
--   trajectory deposits a residue
--       + later steps cannot erase that residue
--       => no finite reverse path to a residue-free state;
--
-- while a coarse observer collision across residue-distinct states gives a
-- strict observer refinement once the residue channel is retained.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- Generic finite transition traces.
------------------------------------------------------------------------

data Trace {State : Set} (Step : State → State → Set) :
  State → State → Set where
  traceRefl : ∀ {x} → Trace Step x x
  traceStep : ∀ {x y z} → Step x y → Trace Step y z → Trace Step x z

composeTrace :
  ∀ {State : Set} {Step : State → State → Set} {x y z} →
  Trace Step x y → Trace Step y z → Trace Step x z
composeTrace traceRefl yz = yz
composeTrace (traceStep xy rest) yz = traceStep xy (composeTrace rest yz)

------------------------------------------------------------------------
-- A minimal binary residue flag.  Applications may retain richer residue data
-- separately; this flag captures only the irreversible absent/present boundary.
------------------------------------------------------------------------

data ResidueFlag : Set where
  residueAbsent residuePresent : ResidueFlag

NoResidueErasure :
  ∀ {State : Set} →
  (Step : State → State → Set) →
  (residue : State → ResidueFlag) →
  Set
NoResidueErasure Step residue =
  ∀ {x y} →
  Step x y →
  residue x ≡ residuePresent →
  residue y ≡ residuePresent

tracePreservesPresentResidue :
  ∀ {State : Set}
    {Step : State → State → Set}
    {residue : State → ResidueFlag} →
  NoResidueErasure Step residue →
  ∀ {x y} →
  Trace Step x y →
  residue x ≡ residuePresent →
  residue y ≡ residuePresent
tracePreservesPresentResidue noErase traceRefl present = present
tracePreservesPresentResidue noErase (traceStep step rest) present =
  tracePreservesPresentResidue noErase rest (noErase step present)

presentResidueBlocksTraceToAbsent :
  ∀ {State : Set}
    {Step : State → State → Set}
    {residue : State → ResidueFlag} →
  NoResidueErasure Step residue →
  ∀ {x y} →
  residue x ≡ residuePresent →
  residue y ≡ residueAbsent →
  ¬ Trace Step x y
presentResidueBlocksTraceToAbsent noErase xPresent yAbsent trace =
  residuePresentNotAbsent
    (trans
      (sym (tracePreservesPresentResidue noErase trace xPresent))
      yAbsent)
  where
    residuePresentNotAbsent : ¬ (residuePresent ≡ residueAbsent)
    residuePresentNotAbsent ()

------------------------------------------------------------------------
-- A path-deposition witness separates historical origin from present-state
-- observation.  The path proves that the extra information was produced along
-- a trajectory; the residue observer records what remains available now.
------------------------------------------------------------------------

record ResidueDeposition
    {State : Set}
    (Step : State → State → Set)
    (residue : State → ResidueFlag) : Set where
  constructor residueDeposition
  field
    before after : State
    path : Trace Step before after
    beforeHasNoResidue : residue before ≡ residueAbsent
    afterHasResidue : residue after ≡ residuePresent

open ResidueDeposition public

------------------------------------------------------------------------
-- Observer cross-pollination.
------------------------------------------------------------------------

residueRefinedObserver :
  ∀ {State Coarse : Set} →
  Observer.Observer State Coarse →
  (State → ResidueFlag) →
  Observer.Observer State (Coarse × ResidueFlag)
residueRefinedObserver coarse residue =
  Observer.pairObserver coarse residue

coarseCollisionAcrossResidueGivesStrictRefinement :
  ∀ {State Coarse : Set}
    (coarse : Observer.Observer State Coarse)
    (residue : State → ResidueFlag)
    (x y : State) →
  coarse x ≡ coarse y →
  residue x ≡ residueAbsent →
  residue y ≡ residuePresent →
  Observer.StrictRefinement coarse (residueRefinedObserver coarse residue)
coarseCollisionAcrossResidueGivesStrictRefinement coarse residue x y coarseSame xAbsent yPresent =
  Observer.strictPairRefinement coarse residue x y coarseSame residuesDiffer
  where
    residuesDiffer : residue x ≡ residue y → ⊥
    residuesDiffer same = residueAbsentNotPresent (trans (sym xAbsent) (trans same yPresent))

    residueAbsentNotPresent : ¬ (residueAbsent ≡ residuePresent)
    residueAbsentNotPresent ()

ResidueDescendsThrough :
  ∀ {State Coarse : Set} →
  Observer.Observer State Coarse →
  (State → ResidueFlag) →
  Set
ResidueDescendsThrough {Coarse = Coarse} coarse residue =
  Σ (Coarse → ResidueFlag)
    (λ reconstruct → ∀ state → reconstruct (coarse state) ≡ residue state)

coarseCollisionAcrossResidueBlocksDescent :
  ∀ {State Coarse : Set}
    {coarse : Observer.Observer State Coarse}
    {residue : State → ResidueFlag}
    {x y : State} →
  coarse x ≡ coarse y →
  residue x ≡ residueAbsent →
  residue y ≡ residuePresent →
  ResidueDescendsThrough coarse residue →
  ⊥
coarseCollisionAcrossResidueBlocksDescent coarseSame xAbsent yPresent descent =
  residueAbsentNotPresent
    (trans
      (sym xAbsent)
      (trans
        (sym (commutes x))
        (trans
          (cong reconstruct coarseSame)
          (trans (commutes y) yPresent))))
  where
    reconstruct = proj₁ descent
    commutes = proj₂ descent

    residueAbsentNotPresent : ¬ (residueAbsent ≡ residuePresent)
    residueAbsentNotPresent ()

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record TrajectoryResidueBoundary : Set where
  constructor trajectoryResidueBoundary
  field
    pathDepositedResidueRepresentable : Bool
    pathDepositedResidueRepresentableIsTrue :
      pathDepositedResidueRepresentable ≡ true

    persistentResidueCanBlockReverseReachability : Bool
    persistentResidueCanBlockReverseReachabilityIsTrue :
      persistentResidueCanBlockReverseReachability ≡ true

    residueCanStrictlyRefineCoarseObservation : Bool
    residueCanStrictlyRefineCoarseObservationIsTrue :
      residueCanStrictlyRefineCoarseObservation ≡ true

    coarseObservationAutomaticallyDeterminesResidue : Bool
    coarseObservationAutomaticallyDeterminesResidueIsFalse :
      coarseObservationAutomaticallyDeterminesResidue ≡ false

canonicalTrajectoryResidueBoundary : TrajectoryResidueBoundary
canonicalTrajectoryResidueBoundary =
  trajectoryResidueBoundary
    true refl
    true refl
    true refl
    false refl
