{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayProjectiveCompactnessMaxCut20261003Exact where

------------------------------------------------------------------------
-- YM BLOCK D / PROJECTIVE COMPACTNESS MAX-CUT
--
-- The continuum lane does not logically require every proof to pass through
-- one globally coercive scalar observable.  The existing physical T5 carrier
-- already records a second legitimate route:
--
--   finite-dimensional marginal moment bounds
--      -> finite-marginal tightness
--      -> diagonal subsequence for a countable test family
--      -> projective consistency
--      -> projective-limit measure
--      -> cylinder expectation uniqueness.
--
-- This file records that route beside the previously isolated direct-global
-- containment / global-coercive-observable route.
--
-- Nothing here upgrades the conditional physical inputs of
-- `FiniteMarginalCompactness`.  In particular, the selected CMP119 measures,
-- their literal marginals, their moment bounds, and their consistency maps
-- still have to be welded to that carrier.  The point is to prevent the proof
-- programme from forcing a single scalar V_k when a projective family of
-- coercive seminorm/marginal bounds is the physically correct topology.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCoerciveObservableMaxCut20261002Exact as ScalarCut
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentCompactnessRound434Exact as Global
import DASHI.Physics.YangMills.BalabanClayT5SelectedWeakTopologyMeaningRound435Exact as Weak
import DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentWeakTopologyRound436Exact as GlobalWeak

------------------------------------------------------------------------
-- The three honest continuum-compactness producers.
------------------------------------------------------------------------

data ContinuumCompactnessRoute : Set where
  directSelectedGlobalContainment
  globalCoerciveObservable
  projectiveFiniteMarginals
  boundedPlaquetteMoment : ContinuumCompactnessRoute

data CompactnessRouteDisposition : Set where
  preferredLeastPrivilegeProducer
  viablePhysicalProducer
  insufficientForContinuumContainment : CompactnessRouteDisposition

routeDisposition : ContinuumCompactnessRoute → CompactnessRouteDisposition
routeDisposition directSelectedGlobalContainment = preferredLeastPrivilegeProducer
routeDisposition globalCoerciveObservable = viablePhysicalProducer
routeDisposition projectiveFiniteMarginals = viablePhysicalProducer
routeDisposition boundedPlaquetteMoment = insufficientForContinuumContainment

------------------------------------------------------------------------
-- Existing theorem-bearing compiler infrastructure.
------------------------------------------------------------------------

-- Direct selected containment remains the least-privilege global route.
directGlobalContainmentCompilerLevel : ProofLevel
directGlobalContainmentCompilerLevel =
  Global.round434SelectedDiagonalTightnessLevel

-- Once a genuine global containment theorem is supplied, every-subsequence
-- tightness is compiler output.
globalContainmentToEverySubsequenceTightLevel : ProofLevel
globalContainmentToEverySubsequenceTightLevel =
  Global.round434EverySubsequenceTightLevel

-- The projective carrier itself is already explicit in the physical cluster
-- closure: finite marginals, Prokhorov extraction, diagonal subsequence,
-- projective consistency, projective-limit existence and uniqueness on
-- cylinder functions are all fields of one same carrier.
projectiveFiniteMarginalCarrierCompilerLevel : ProofLevel
projectiveFiniteMarginalCarrierCompilerLevel =
  Physical.physicalClusterExpansionAdapterLevel

-- Selected weak-expectation topology compilers are downstream once the
-- physical topology/measure semantics are supplied.
selectedWeakTopologyCompilerLevel : ProofLevel
selectedWeakTopologyCompilerLevel = Weak.round435SelectedWeakTopologyCompilerLevel

selectedWeakTopologyToFullConvergenceCompilerLevel : ProofLevel
selectedWeakTopologyToFullConvergenceCompilerLevel =
  GlobalWeak.round436PreferredCompactnessCompilerLevel

------------------------------------------------------------------------
-- Exact physical leaves on the projective route.
------------------------------------------------------------------------

-- The live projective theorem must instantiate the generic
-- `FiniteMarginalCompactness` fields on the SAME selected CMP119 measure
-- sequence.  This is where the actual finite-dimensional moment estimates and
-- marginal Markov tails enter.
projectivePhysicalMomentCompactnessInputsLevel : ProofLevel
projectivePhysicalMomentCompactnessInputsLevel =
  Physical.physicalMomentCompactnessInputsLevel

-- The finite marginals must be the actual restrictions/projections of the
-- selected CMP119 measures, with source/lattice blocking compatibility.
selectedCMP119ToProjectiveMarginalDictionaryLevel : ProofLevel
selectedCMP119ToProjectiveMarginalDictionaryLevel = conditional

-- The same bounded cylinder expectations must define the selected weak
-- measure topology and separate measures.
selectedProjectiveWeakTopologyMeaningLevel : ProofLevel
selectedProjectiveWeakTopologyMeaningLevel =
  Weak.round435SelectedMeasureWeakExpectationMeaningLevel

selectedProjectiveDeterminingClassLevel : ProofLevel
selectedProjectiveDeterminingClassLevel =
  Weak.round435BoundedDeterminingClassMeaningLevel

------------------------------------------------------------------------
-- Comparison with the scalar/global route.
------------------------------------------------------------------------

globalSelectedContainmentProducerLevel : ProofLevel
globalSelectedContainmentProducerLevel =
  ScalarCut.blockDGlobalSelectedContainmentProducerLevel

globalCoerciveObservableGeometryLevel : ProofLevel
globalCoerciveObservableGeometryLevel =
  ScalarCut.selectedCoercivityAndCompactSublevelLevel

-- A bounded plaquette expectation remains a negative control only.  It is not
-- promoted to either global compact containment or finite-marginal tightness.
boundedPlaquetteMomentDoesNotPayD :
  routeDisposition boundedPlaquetteMoment
    ≡ insufficientForContinuumContainment
boundedPlaquetteMomentDoesNotPayD = refl

projectiveFiniteMarginalsRemainLive :
  routeDisposition projectiveFiniteMarginals
    ≡ viablePhysicalProducer
projectiveFiniteMarginalsRemainLive = refl

------------------------------------------------------------------------
-- Final D cut.
------------------------------------------------------------------------

-- D can now close by EITHER:
--   (1) one selected global compact-containment theorem;
--   (2) one global coercive observable with genuine compact sublevels and
--       probability-integral semantics;
--   (3) same-object finite-marginal/projective moment tightness plus consistency.
--
-- All three routes still require a real physical producer.  The projective
-- route is not an escape hatch from estimates; it changes the shape of the
-- estimate to the topology actually consumed by the continuum construction.
blockDProjectiveMaxCutCompilerLevel : ProofLevel
blockDProjectiveMaxCutCompilerLevel = machineChecked

blockDPhysicalCompactnessProducerLevel : ProofLevel
blockDPhysicalCompactnessProducerLevel = conditional
