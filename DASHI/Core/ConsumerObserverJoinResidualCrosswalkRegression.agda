module DASHI.Core.ConsumerObserverJoinResidualCrosswalkRegression where

open import DASHI.Core.Prelude

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ConsumerObserverJoinResidualExact as Join
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ObserverRefinementLatticeExact as Lattice
import DASHI.Core.ConsumerObserverJoinResidualCrosswalkExact as Crosswalk

wrappedRefinementToCanonical :
  ∀ {State : Set}
    {fine coarse : Join.Observer State} →
  Join.Refines fine coarse →
  Lattice.Refines (Join.observe coarse) (Join.observe fine)
wrappedRefinementToCanonical = Crosswalk.wrappedRefinesToLattice

wrappedJoinUsesCanonicalPair :
  ∀ {State : Set}
    (left right : Join.Observer State)
    (state : State) →
  Join.observe (Join.joinObserver left right) state
  ≡ Lattice.pairObserver (Join.observe left) (Join.observe right) state
wrappedJoinUsesCanonicalPair = Crosswalk.joinObserverUsesCanonicalPair

hotColdToCanonicalReopening :
  ∀ {Fine Hot Residual : Set} →
  Join.RecoverableHotCold Fine Hot Residual →
  Fibre.CoarseFineReopening Fine
hotColdToCanonicalReopening = Crosswalk.hotColdToCoarseFineReopening

canonicalReopeningBackToHotCold :
  ∀ {Fine : Set}
    (geometry : Fibre.CoarseFineReopening Fine) →
  Join.RecoverableHotCold
    Fine
    (Fibre.Coarse geometry)
    (Fibre.RelativeFine geometry)
canonicalReopeningBackToHotCold = Crosswalk.coarseFineReopeningToHotCold

hotStateSufficiencyIsCanonicalFactorisation :
  ∀ {Fine Hot Output : Set}
    {hot : Fine → Hot}
    {consume : Fine → Output} →
  Join.ConsumerSufficientHotState hot consume →
  Factorized.FactorizedRefinement consume hot
hotStateSufficiencyIsCanonicalFactorisation =
  Crosswalk.consumerSufficientHotToFactorized
