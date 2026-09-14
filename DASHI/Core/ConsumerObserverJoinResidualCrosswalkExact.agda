module DASHI.Core.ConsumerObserverJoinResidualCrosswalkExact where

open import DASHI.Core.Prelude

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ConsumerObserverJoinResidualExact as Join
import DASHI.Core.KernelConsumerDescentFactorisationCrosswalkExact as KernelFactor
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ObserverRefinementLatticeExact as Lattice

------------------------------------------------------------------------
-- WRAPPED OBSERVER / HOT-COLD CROSSWALK
--
-- ConsumerObserverJoinResidualExact carries useful packaging and the minimal
-- consumer-hot-state universal property.  Its observer refinement, exact
-- hot/cold reopening, and explicit consumer descent are exact manifestations of
-- existing canonical Core owners.  Translate them rather than creating another
-- generic observer/reopening/factorisation theory.
------------------------------------------------------------------------

wrappedRefinesToLattice :
  ∀ {State : Set}
    {fine coarse : Join.Observer State} →
  Join.Refines fine coarse →
  Lattice.Refines (Join.observe coarse) (Join.observe fine)
wrappedRefinesToLattice refinement = Join.collisionMapsBack refinement

latticeRefinesToWrapped :
  ∀ {State : Set}
    {fine coarse : Join.Observer State} →
  Lattice.Refines (Join.observe coarse) (Join.observe fine) →
  Join.Refines fine coarse
latticeRefinesToWrapped refinement = Join.refines refinement

joinObserverUsesCanonicalPair :
  ∀ {State : Set}
    (left right : Join.Observer State)
    (state : State) →
  Join.observe (Join.joinObserver left right) state
  ≡ Lattice.pairObserver (Join.observe left) (Join.observe right) state
joinObserverUsesCanonicalPair left right state = refl

hotColdToCoarseFineReopening :
  ∀ {Fine Hot Residual : Set} →
  Join.RecoverableHotCold Fine Hot Residual →
  Fibre.CoarseFineReopening Fine
hotColdToCoarseFineReopening {Hot = Hot} {Residual = Residual} recoverable =
  Fibre.coarseFineReopening
    Hot
    Residual
    (Join.hot recoverable)
    (Join.residual recoverable)
    (Join.reopen recoverable)
    (Join.reopenExact recoverable)

coarseFineReopeningToHotCold :
  ∀ {Fine : Set}
    (geometry : Fibre.CoarseFineReopening Fine) →
  Join.RecoverableHotCold
    Fine
    (Fibre.Coarse geometry)
    (Fibre.RelativeFine geometry)
coarseFineReopeningToHotCold geometry =
  Join.recoverableHotCold
    (Fibre.coarse geometry)
    (Fibre.relativeFine geometry)
    (Fibre.reopen geometry)
    (Fibre.reopenExact geometry)

sameHotAndResidualSameFineViaCanonical :
  ∀ {Fine Hot Residual : Set}
    (recoverable : Join.RecoverableHotCold Fine Hot Residual)
    {left right : Fine} →
  Join.hot recoverable left ≡ Join.hot recoverable right →
  Join.residual recoverable left ≡ Join.residual recoverable right →
  left ≡ right
sameHotAndResidualSameFineViaCanonical recoverable =
  Fibre.coarseAndRelativeFineDetermineState
    (hotColdToCoarseFineReopening recoverable)

consumerSufficientHotToFactorized :
  ∀ {Fine Hot Output : Set}
    {hot : Fine → Hot}
    {consume : Fine → Output} →
  Join.ConsumerSufficientHotState hot consume →
  Factorized.FactorizedRefinement consume hot
consumerSufficientHotToFactorized sufficient =
  KernelFactor.kernelDescentToFactorized (Join.descent sufficient)

minimalHotSufficiencyToFactorized :
  ∀ {Fine Hot Output : Set}
    {hot : Fine → Hot}
    {consume : Fine → Output} →
  Join.MinimalConsumerSufficientHotState hot consume →
  Factorized.FactorizedRefinement consume hot
minimalHotSufficiencyToFactorized minimal =
  consumerSufficientHotToFactorized (Join.sufficient minimal)
