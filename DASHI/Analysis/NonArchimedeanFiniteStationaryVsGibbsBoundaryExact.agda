module DASHI.Analysis.NonArchimedeanFiniteStationaryVsGibbsBoundaryExact where

------------------------------------------------------------------------
-- FINITE STATIONARY UNIQUENESS != INFINITE GIBBS UNIQUENESS
--
-- Cross-pollination from the repaired finite Markov lane gives a useful new
-- finite theorem boundary:
--
--   directed irreducibility on ZMod (2^n)
--   + bistochastic / uniform stationarity
--   -> unique stationary law on that FINITE chain.
--
-- This does NOT prove the source's stronger thermodynamic statement that
-- normalized Haar is the unique conformal Gibbs state on the 2-adic inverse
-- limit.  That promotion additionally needs compatibility across levels and a
-- genuine infinite-system Gibbs/conformal uniqueness theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data StationaryGibbsLeaf : Set where
  finiteDirectedIrreducibility : StationaryGibbsLeaf
  finiteUniformStationarity : StationaryGibbsLeaf
  finiteUniqueStationaryLaw : StationaryGibbsLeaf
  projectiveStationaryCompatibility : StationaryGibbsLeaf
  infiniteHaarStationarity : StationaryGibbsLeaf
  conformalGibbsProperty : StationaryGibbsLeaf
  infiniteGibbsUniqueness : StationaryGibbsLeaf


data StationaryGibbsStatus : Set where
  dependencyClosed : StationaryGibbsStatus
  standardFiniteConsumer : StationaryGibbsStatus
  liveInfiniteProducer : StationaryGibbsStatus

status : StationaryGibbsLeaf → StationaryGibbsStatus
status finiteDirectedIrreducibility = dependencyClosed
status finiteUniformStationarity = dependencyClosed
status finiteUniqueStationaryLaw = standardFiniteConsumer
status projectiveStationaryCompatibility = liveInfiniteProducer
status infiniteHaarStationarity = liveInfiniteProducer
status conformalGibbsProperty = liveInfiniteProducer
status infiniteGibbsUniqueness = liveInfiniteProducer


data GibbsPromotionObligation : Set where
  needProjectiveStationaryCompatibility : GibbsPromotionObligation
  needInfiniteHaarStationarityWeld : GibbsPromotionObligation
  needConformalGibbsTheorem : GibbsPromotionObligation
  needInfiniteGibbsUniquenessTheorem : GibbsPromotionObligation

infiniteGibbsCutset : List GibbsPromotionObligation
infiniteGibbsCutset =
  needProjectiveStationaryCompatibility ∷
  needInfiniteHaarStationarityWeld ∷
  needConformalGibbsTheorem ∷
  needInfiniteGibbsUniquenessTheorem ∷
  []

record StationaryGibbsFirewall : Set where
  constructor stationaryGibbsFirewall
  field
    finiteUniqueStationaryImpliesInfiniteHaarUnique : Bool
    finiteStationaryImpliesConformalGibbs : Bool
    everyFiniteLevelUniqueImpliesProjectiveCompatibility : Bool
    finiteResultStillScientificallyUseful : Bool

canonicalStationaryGibbsFirewall : StationaryGibbsFirewall
canonicalStationaryGibbsFirewall =
  stationaryGibbsFirewall false false false true

finiteDoesNotPromoteToGibbs :
  StationaryGibbsFirewall.finiteStationaryImpliesConformalGibbs
    canonicalStationaryGibbsFirewall
  ≡ false
finiteDoesNotPromoteToGibbs = refl

finiteStationaryUniquenessUseful :
  StationaryGibbsFirewall.finiteResultStillScientificallyUseful
    canonicalStationaryGibbsFirewall
  ≡ true
finiteStationaryUniquenessUseful = refl
