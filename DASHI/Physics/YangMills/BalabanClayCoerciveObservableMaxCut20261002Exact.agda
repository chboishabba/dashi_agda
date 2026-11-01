{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCoerciveObservableMaxCut20261002Exact where

------------------------------------------------------------------------
-- YM BLOCK D / COERCIVE-CONTINUUM MAX-CUT
--
-- Work backwards from the actual selected compactness consumer.
--
-- The repository already proves that finite moment bounds, by themselves, are
-- insufficient for the global selected compact-containment theorem.  The
-- preferred Round211/212 route requires either:
--
--   (A) direct compact containment of the literal selected diagonal measures,
--
-- or
--
--   (B) one physical observable which is simultaneously
--       * nonnegative,
--       * coercive for the selected topology,
--       * has admissibly compact sublevels in that topology,
--       * is evaluated by the actual probability integral,
--       * and has the required selected moment bound.
--
-- Path4 gauge energy is presently the strongest explicit candidate in the
-- checked tree: its pointwise nonnegativity/coercivity compiler is already
-- machine checked.  But its compact-sublevel theorem and the selected
-- expectation/probability-integral semantics remain conditional.  Therefore
-- Path4 is NOT promoted here to the global Clay coercive observable.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT1PhysicalMeaningRound211Exact as R211
import DASHI.Physics.YangMills.BalabanClayT1SelectedCoerciveContainmentRound212Exact as R212
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyMarkovBridgeExact as Path4
import DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentCompactnessRound434Exact as R434
import DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentWeakTopologyRound436Exact as R436

data BlockDRoute : Set where
  directSelectedGlobalContainment : BlockDRoute
  globalCoerciveObservable : BlockDRoute
  path4LocalEnergyWithoutGlobalSublevel : BlockDRoute
  boundedPlaquetteMoment : BlockDRoute

data BlockDDisposition : Set where
  livePhysicalProducer : BlockDDisposition
  viableAfterGlobalGeometry : BlockDDisposition
  insufficientForClayContainment : BlockDDisposition

blockDDisposition : BlockDRoute → BlockDDisposition
blockDDisposition directSelectedGlobalContainment = livePhysicalProducer
blockDDisposition globalCoerciveObservable = viableAfterGlobalGeometry
blockDDisposition path4LocalEnergyWithoutGlobalSublevel =
  insufficientForClayContainment
blockDDisposition boundedPlaquetteMoment = insufficientForClayContainment

------------------------------------------------------------------------
-- Existing checked facts.
------------------------------------------------------------------------

path4PointwiseNonnegativeAndCoerciveAlreadyChecked : Bool
path4PointwiseNonnegativeAndCoerciveAlreadyChecked = true

finiteMomentAloneDoesNotPayContainment : Bool
finiteMomentAloneDoesNotPayContainment =
  R211.round211FiniteMomentAlonePaysCompactContainment

localChartAloneDoesNotPayGlobalT1 : Bool
localChartAloneDoesNotPayGlobalT1 =
  R211.round211LocalChartAlonePaysGlobalT1

selectedMarkovContainmentCompilerClosed : Bool
selectedMarkovContainmentCompilerClosed =
  R212.round212SelectedMarkovContainmentCompilerClosed

directContainmentIsLeastPrivilegeTarget : Bool
directContainmentIsLeastPrivilegeTarget =
  R211.round211DirectContainmentIsLeastPrivilegeTarget

------------------------------------------------------------------------
-- Exact surviving physical leaves for the observable route.
------------------------------------------------------------------------

path4FiniteCoercivityLevel : ProofLevel
path4FiniteCoercivityLevel =
  Path4.path4FiniteNonnegativityAndCoercivityReuseLevel

path4ProbabilityIntegralSemanticsLevel : ProofLevel
path4ProbabilityIntegralSemanticsLevel =
  Path4.physicalSelectedExpectationMarkovSemanticsLevel

path4CompactSublevelInSelectedTopologyLevel : ProofLevel
path4CompactSublevelInSelectedTopologyLevel =
  Path4.path4GaugeEnergyCompactSublevelLevel

selectedPhysicalExpectationProbabilitySemanticsLevel : ProofLevel
selectedPhysicalExpectationProbabilitySemanticsLevel =
  R212.physicalSelectedExpectationProbabilitySemanticsLevel

selectedCoercivityAndCompactSublevelLevel : ProofLevel
selectedCoercivityAndCompactSublevelLevel =
  R212.physicalSelectedCoercivityAndCompactSublevelLevel

------------------------------------------------------------------------
-- Once global containment is paid, the downstream compactness route is compiler
-- work rather than a second independent tightness theorem.
------------------------------------------------------------------------

globalContainmentToSelectedDiagonalTightnessLevel : ProofLevel
globalContainmentToSelectedDiagonalTightnessLevel =
  R434.round434SelectedDiagonalTightnessLevel

globalContainmentToEverySubsequenceTightLevel : ProofLevel
globalContainmentToEverySubsequenceTightLevel =
  R434.round434EverySubsequenceTightLevel

globalContainmentPreferredCompactnessCompilerLevel : ProofLevel
globalContainmentPreferredCompactnessCompilerLevel =
  R436.round436PreferredCompactnessCompilerLevel

globalMomentCompactContainmentStillPhysicalLevel : ProofLevel
globalMomentCompactContainmentStillPhysicalLevel =
  R436.round436GlobalMomentCompactContainmentLevel

selectedWeakTopologyMeaningStillPhysicalLevel : ProofLevel
selectedWeakTopologyMeaningStillPhysicalLevel =
  R436.round436SelectedWeakTopologyMeaningLevel

------------------------------------------------------------------------
-- Status firewall.
------------------------------------------------------------------------

path4MayBeFinalGlobalObservable : Bool
path4MayBeFinalGlobalObservable = false

path4MayBeFinalGlobalObservableIsFalse :
  path4MayBeFinalGlobalObservable ≡ false
path4MayBeFinalGlobalObservableIsFalse = refl

blockDSearchReducedToGlobalEscapeGeometry : Bool
blockDSearchReducedToGlobalEscapeGeometry = true

blockDSearchReducedToGlobalEscapeGeometryIsTrue :
  blockDSearchReducedToGlobalEscapeGeometry ≡ true
blockDSearchReducedToGlobalEscapeGeometryIsTrue = refl

blockDMaxCutCompilerLevel : ProofLevel
blockDMaxCutCompilerLevel = machineChecked

-- Clay-facing producer: prove one literal selected global containment theorem,
-- either directly or via an observable with genuine compact sublevels and real
-- probability-integral semantics.  No bounded Wilson-trace moment can fill it.
blockDGlobalSelectedContainmentProducerLevel : ProofLevel
blockDGlobalSelectedContainmentProducerLevel = conditional
