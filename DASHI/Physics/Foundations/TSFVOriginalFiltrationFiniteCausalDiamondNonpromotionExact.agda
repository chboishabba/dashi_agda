module DASHI.Physics.Foundations.TSFVOriginalFiltrationFiniteCausalDiamondNonpromotionExact where

------------------------------------------------------------------------
-- P01 -> P02: ORIGINAL observer visibility vs ORIGINAL 1+3 diamond.
--
-- Existing finite causal diamond: one past, three pairwise incomparable
-- spatial slice events, one future; original causal/null edges.
-- Existing HistoryWeightFiltrationExact: original three access levels.
--
-- A concrete coarse-time map preserves each original causal edge
-- into the actual observable-access preorder, but x/y/z all share the
-- same original intermediate observable level. Thus no decoder using
-- ONLY original filtration levels can identify x and y separately.
-- The physical 3-dimensional spatial/propagation measurement is NOT
-- derivable from this finite temporal-access hierarchy by itself.
--
-- This uses exact pre-existing diamond owners, not a new arbitrary
-- "physical" causal graph. No 4D continuum/metric is constructed.
-- The legacy diamond owner is not transitively --safe; this file is
-- intentionally a non-Golden source adapter, KERNEL PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Geometry.FiniteCausalDiamond as Diamond
import DASHI.Physics.Foundations.HistoryWeightFiltrationExact as History
import DASHI.Physics.Foundations.TSFVOriginalObserverVisibilityCausalOrderExact as Access

originalDiamondCoarseAccessLevel :
  Diamond.Event → History.FiltrationLevel
originalDiamondCoarseAccessLevel Diamond.past = History.initialFiltration
originalDiamondCoarseAccessLevel Diamond.xNow =
  History.intermediateFiltration
originalDiamondCoarseAccessLevel Diamond.yNow =
  History.intermediateFiltration
originalDiamondCoarseAccessLevel Diamond.zNow =
  History.intermediateFiltration
originalDiamondCoarseAccessLevel Diamond.future =
  History.terminalFiltration

originalDiamondCausalEdgesRespectObserverAccess :
  ∀ {a b : Diamond.Event} →
  Diamond._≺_ a b →
  Access._⊑obs_
    (originalDiamondCoarseAccessLevel a)
    (originalDiamondCoarseAccessLevel b)
originalDiamondCausalEdgesRespectObserverAccess Diamond.past-x =
  Access.initialAccessPrecedesIntermediate
originalDiamondCausalEdgesRespectObserverAccess Diamond.past-y =
  Access.initialAccessPrecedesIntermediate
originalDiamondCausalEdgesRespectObserverAccess Diamond.past-z =
  Access.initialAccessPrecedesIntermediate
originalDiamondCausalEdgesRespectObserverAccess Diamond.x-future =
  Access.intermediateAccessPrecedesTerminal
originalDiamondCausalEdgesRespectObserverAccess Diamond.y-future =
  Access.intermediateAccessPrecedesTerminal
originalDiamondCausalEdgesRespectObserverAccess Diamond.z-future =
  Access.intermediateAccessPrecedesTerminal
originalDiamondCausalEdgesRespectObserverAccess Diamond.past-future =
  Access.initialAccessPrecedesTerminal

originalSpatialXYZHaveOneObservedFiltrationLevel :
  (originalDiamondCoarseAccessLevel Diamond.xNow
   ≡ originalDiamondCoarseAccessLevel Diamond.yNow)
  ×
  (originalDiamondCoarseAccessLevel Diamond.yNow
   ≡ originalDiamondCoarseAccessLevel Diamond.zNow)
originalSpatialXYZHaveOneObservedFiltrationLevel = refl , refl

originalDiamondSpatialXAndYAreDistinct :
  Diamond.xNow ≡ Diamond.yNow → ⊥
originalDiamondSpatialXAndYAreDistinct ()

noOriginalSpatialBranchDecoderFromObserverFiltration :
  (decode : History.FiltrationLevel → Diamond.Event) →
  ((event : Diamond.Event) →
    decode (originalDiamondCoarseAccessLevel event) ≡ event) →
  ⊥
noOriginalSpatialBranchDecoderFromObserverFiltration decode correct =
  originalDiamondSpatialXAndYAreDistinct
    (trans
      (sym (correct Diamond.xNow))
      (trans
        (cong decode refl)
        (correct Diamond.yNow)))

originalDiamondXYZArePairwiseIncomparable :
  Diamond.Incomparable Diamond.xNow Diamond.yNow
originalDiamondXYZArePairwiseIncomparable =
  Diamond.x-y-incomparable

------------------------------------------------------------------------
-- S02 / P02.L01,06 BACKWARD NECESSITY:
-- Exactly WHICH additional original observer measurement is required?
--
-- If a source-selected sensor readout together with the original
-- 3-level filtration can reconstruct the three actual spatial
-- diamond events, that sensor MUST distinguish x/y, x/z and y/z.
-- These are derived necessary consequences, not separately assumed
-- empirical independence of the three sensors. A generic Reading
-- carrier does NOT produce a physical detector or a 4D continuum.
------------------------------------------------------------------------

originalDiamondSpatialXAndZAreDistinct :
  Diamond.xNow ≡ Diamond.zNow → ⊥
originalDiamondSpatialXAndZAreDistinct ()

originalDiamondSpatialYAndZAreDistinct :
  Diamond.yNow ≡ Diamond.zNow → ⊥
originalDiamondSpatialYAndZAreDistinct ()

originalSpatialSensorMustDistinguishXY :
  ∀ {Reading : Set}
    (sensor : Diamond.Event → Reading)
    (decode : History.FiltrationLevel → Reading → Diamond.Event) →
    ((event : Diamond.Event) →
      decode (originalDiamondCoarseAccessLevel event)
        (sensor event) ≡ event) →
    sensor Diamond.xNow ≡ sensor Diamond.yNow →
    ⊥
originalSpatialSensorMustDistinguishXY sensor decode correct same =
  originalDiamondSpatialXAndYAreDistinct
    (trans
      (sym (correct Diamond.xNow))
      (trans
        (cong (decode History.intermediateFiltration) same)
        (correct Diamond.yNow)))

originalSpatialSensorMustDistinguishXZ :
  ∀ {Reading : Set}
    (sensor : Diamond.Event → Reading)
    (decode : History.FiltrationLevel → Reading → Diamond.Event) →
    ((event : Diamond.Event) →
      decode (originalDiamondCoarseAccessLevel event)
        (sensor event) ≡ event) →
    sensor Diamond.xNow ≡ sensor Diamond.zNow →
    ⊥
originalSpatialSensorMustDistinguishXZ sensor decode correct same =
  originalDiamondSpatialXAndZAreDistinct
    (trans
      (sym (correct Diamond.xNow))
      (trans
        (cong (decode History.intermediateFiltration) same)
        (correct Diamond.zNow)))

originalSpatialSensorMustDistinguishYZ :
  ∀ {Reading : Set}
    (sensor : Diamond.Event → Reading)
    (decode : History.FiltrationLevel → Reading → Diamond.Event) →
    ((event : Diamond.Event) →
      decode (originalDiamondCoarseAccessLevel event)
        (sensor event) ≡ event) →
    sensor Diamond.yNow ≡ sensor Diamond.zNow →
    ⊥
originalSpatialSensorMustDistinguishYZ sensor decode correct same =
  originalDiamondSpatialYAndZAreDistinct
    (trans
      (sym (correct Diamond.yNow))
      (trans
        (cong (decode History.intermediateFiltration) same)
        (correct Diamond.zNow)))

-- These three independent conclusions put an actual empirical
-- discriminability burden on S02: an observation that depends only
-- on coarse time/filtration cannot carry the missing spatial data.
originalSpatialSensorNeedsThreePairwiseDistinctReadouts :
  ∀ {Reading : Set}
    (sensor : Diamond.Event → Reading)
    (decode : History.FiltrationLevel → Reading → Diamond.Event) →
    ((event : Diamond.Event) →
      decode (originalDiamondCoarseAccessLevel event)
        (sensor event) ≡ event) →
    ((sensor Diamond.xNow ≡ sensor Diamond.yNow → ⊥)
    × ((sensor Diamond.xNow ≡ sensor Diamond.zNow → ⊥)
    × (sensor Diamond.yNow ≡ sensor Diamond.zNow → ⊥)))
originalSpatialSensorNeedsThreePairwiseDistinctReadouts
    sensor decode correct =
  originalSpatialSensorMustDistinguishXY sensor decode correct ,
  (originalSpatialSensorMustDistinguishXZ sensor decode correct ,
   originalSpatialSensorMustDistinguishYZ sensor decode correct)

-- Proper next physical producer: a nonconstant measured spatial
-- observable on the SOURCE-selected microscopic observer system,
-- supporting one common operational cone/principal symbol, rather
-- than a disconnected finite diamond signature fixture.
