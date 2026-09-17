module DASHI.Wikimedia.IbrahimMonsterSSP14GlobalInversionOrbitWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Modes
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as SSP15
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction
import DASHI.Wikimedia.IbrahimMonster42dFifteenFourteenPhaseCarrierExact as Carrier14

------------------------------------------------------------------------
-- SSP15 RESIDUAL-14 <-> FULL TERNARY-27 GLOBAL-INVERSION ORBIT-14 WELD
--
-- There are two different 14-state constructions in the merged repository:
--
--   (A) SSP15 minus the distinguished neutral lane (mode09 , zeroTrit),
--   (B) the full global inversion quotient T^3 / (x ~ -x).
--
-- Cardinality alone does not identify them.  In fact the most obvious map,
-- obtained by canonical-lifting each residual SSP lane back to T^3 and then
-- applying the full global quotient, is NOT bijective:
--
--   (mode09,-) and (mode09,+) both land in the x-axis orbit,
--   while the fixed origin orbit is not hit because the neutral origin lane
--   was exactly the lane deleted from SSP15.
--
-- This module therefore exposes both facts explicitly:
--
--   * a literal finite two-sided chart between the two 14-element carriers;
--   * a firewall proving that this chart is not the canonical-lift-induced
--     quotient map.  It uses one explicit exceptional reindexing:
--
--       (mode09,+)  |->  origin orbit.
--
-- The chart is a finite carrier weld only.  It creates no D4, N(3B), Monster,
-- character, action, or same-object authority.
------------------------------------------------------------------------

Ternary27Point : Set
Ternary27Point = Geometry.Ternary27Point

negate27 : Ternary27Point → Ternary27Point
negate27 (Geometry.ternary27Point x y z) =
  Geometry.ternary27Point
    (Reduction.negateSSP x)
    (Reduction.negateSSP y)
    (Reduction.negateSSP z)

------------------------------------------------------------------------
-- 1. Canonical full global-inversion orbit carrier of T^3.
------------------------------------------------------------------------

data Ternary27GlobalInversionOrbit14 : Set where
  globalOriginOrbit : Ternary27GlobalInversionOrbit14
  globalXOnlyOrbit : Ternary27GlobalInversionOrbit14
  globalYOnlyOrbit : Ternary27GlobalInversionOrbit14
  globalZOnlyOrbit : Ternary27GlobalInversionOrbit14
  globalXYEqualZZeroOrbit : Ternary27GlobalInversionOrbit14
  globalXYOppositeZZeroOrbit : Ternary27GlobalInversionOrbit14
  globalXZEqualYZeroOrbit : Ternary27GlobalInversionOrbit14
  globalXZOppositeYZeroOrbit : Ternary27GlobalInversionOrbit14
  globalYZEqualXZeroOrbit : Ternary27GlobalInversionOrbit14
  globalYZOppositeXZeroOrbit : Ternary27GlobalInversionOrbit14
  globalAllEqualOrbit : Ternary27GlobalInversionOrbit14
  globalXYEqualZOppositeOrbit : Ternary27GlobalInversionOrbit14
  globalXZEqualYOppositeOrbit : Ternary27GlobalInversionOrbit14
  globalYZEqualXOppositeOrbit : Ternary27GlobalInversionOrbit14

quotient27Global : Ternary27Point → Ternary27GlobalInversionOrbit14
quotient27Global (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = globalOriginOrbit
quotient27Global (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = globalXOnlyOrbit
quotient27Global (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = globalXOnlyOrbit
quotient27Global (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = globalYOnlyOrbit
quotient27Global (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = globalYOnlyOrbit
quotient27Global (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = globalZOnlyOrbit
quotient27Global (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = globalZOnlyOrbit
quotient27Global (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = globalXYEqualZZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = globalXYEqualZZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = globalXYOppositeZZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = globalXYOppositeZZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = globalXZEqualYZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = globalXZEqualYZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = globalXZOppositeYZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = globalXZOppositeYZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = globalYZEqualXZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = globalYZEqualXZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = globalYZOppositeXZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = globalYZOppositeXZeroOrbit
quotient27Global (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = globalAllEqualOrbit
quotient27Global (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = globalAllEqualOrbit
quotient27Global (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = globalXYEqualZOppositeOrbit
quotient27Global (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = globalXYEqualZOppositeOrbit
quotient27Global (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = globalXZEqualYOppositeOrbit
quotient27Global (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = globalXZEqualYOppositeOrbit
quotient27Global (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = globalYZEqualXOppositeOrbit
quotient27Global (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = globalYZEqualXOppositeOrbit

quotient27GlobalNegationInvariant :
  (p : Ternary27Point) → quotient27Global (negate27 p) ≡ quotient27Global p
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = refl
quotient27GlobalNegationInvariant (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = refl

canonicalGlobalRepresentative :
  Ternary27GlobalInversionOrbit14 → Ternary27Point
canonicalGlobalRepresentative globalOriginOrbit = Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero
canonicalGlobalRepresentative globalXOnlyOrbit = Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero
canonicalGlobalRepresentative globalYOnlyOrbit = Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero
canonicalGlobalRepresentative globalZOnlyOrbit = Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne
canonicalGlobalRepresentative globalXYEqualZZeroOrbit = Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero
canonicalGlobalRepresentative globalXYOppositeZZeroOrbit = Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero
canonicalGlobalRepresentative globalXZEqualYZeroOrbit = Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne
canonicalGlobalRepresentative globalXZOppositeYZeroOrbit = Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne
canonicalGlobalRepresentative globalYZEqualXZeroOrbit = Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne
canonicalGlobalRepresentative globalYZOppositeXZeroOrbit = Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne
canonicalGlobalRepresentative globalAllEqualOrbit = Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne
canonicalGlobalRepresentative globalXYEqualZOppositeOrbit = Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne
canonicalGlobalRepresentative globalXZEqualYOppositeOrbit = Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne
canonicalGlobalRepresentative globalYZEqualXOppositeOrbit = Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne

canonicalGlobalRepresentativeReturnsOrbit :
  (g : Ternary27GlobalInversionOrbit14) →
  quotient27Global (canonicalGlobalRepresentative g) ≡ g
canonicalGlobalRepresentativeReturnsOrbit globalOriginOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalXOnlyOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalYOnlyOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalZOnlyOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalXYEqualZZeroOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalXYOppositeZZeroOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalXZEqualYZeroOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalXZOppositeYZeroOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalYZEqualXZeroOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalYZOppositeXZeroOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalAllEqualOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalXYEqualZOppositeOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalXZEqualYOppositeOrbit = refl
canonicalGlobalRepresentativeReturnsOrbit globalYZEqualXOppositeOrbit = refl

------------------------------------------------------------------------
-- 2. Typed index for the exact fourteen lanes already enumerated by Carrier14.
------------------------------------------------------------------------

data Residual14Index : Set where
  residualMode09Negative : Residual14Index
  residualMode09Positive : Residual14Index
  residualMode18Negative : Residual14Index
  residualMode18Zero : Residual14Index
  residualMode18Positive : Residual14Index
  residualMode27Negative : Residual14Index
  residualMode27Zero : Residual14Index
  residualMode27Positive : Residual14Index
  residualMode36Negative : Residual14Index
  residualMode36Zero : Residual14Index
  residualMode36Positive : Residual14Index
  residualMode45Negative : Residual14Index
  residualMode45Zero : Residual14Index
  residualMode45Positive : Residual14Index

residualLane : Residual14Index → SSP15.SSP15InternalLane
residualLane residualMode09Negative = Modes.mode09 , Harmonic.negativeTrit
residualLane residualMode09Positive = Modes.mode09 , Harmonic.positiveTrit
residualLane residualMode18Negative = Modes.mode18 , Harmonic.negativeTrit
residualLane residualMode18Zero = Modes.mode18 , Harmonic.zeroTrit
residualLane residualMode18Positive = Modes.mode18 , Harmonic.positiveTrit
residualLane residualMode27Negative = Modes.mode27 , Harmonic.negativeTrit
residualLane residualMode27Zero = Modes.mode27 , Harmonic.zeroTrit
residualLane residualMode27Positive = Modes.mode27 , Harmonic.positiveTrit
residualLane residualMode36Negative = Modes.mode36 , Harmonic.negativeTrit
residualLane residualMode36Zero = Modes.mode36 , Harmonic.zeroTrit
residualLane residualMode36Positive = Modes.mode36 , Harmonic.positiveTrit
residualLane residualMode45Negative = Modes.mode45 , Harmonic.negativeTrit
residualLane residualMode45Zero = Modes.mode45 , Harmonic.zeroTrit
residualLane residualMode45Positive = Modes.mode45 , Harmonic.positiveTrit

------------------------------------------------------------------------
-- 3. The natural canonical-lift map exposes the obstruction.
------------------------------------------------------------------------

naturalGlobalTarget : Residual14Index → Ternary27GlobalInversionOrbit14
naturalGlobalTarget r =
  quotient27Global
    (Reduction.canonicalLiftPhaseOrbit15
      (Reduction.ssp15ToPhaseOrbit (residualLane r)))

naturalMode09SignsCollide :
  naturalGlobalTarget residualMode09Negative
  ≡ naturalGlobalTarget residualMode09Positive
naturalMode09SignsCollide = refl

naturalMode09NegativeIsXOnly :
  naturalGlobalTarget residualMode09Negative ≡ globalXOnlyOrbit
naturalMode09NegativeIsXOnly = refl

naturalMode09PositiveIsXOnly :
  naturalGlobalTarget residualMode09Positive ≡ globalXOnlyOrbit
naturalMode09PositiveIsXOnly = refl

------------------------------------------------------------------------
-- 4. Explicit finite weld: one exceptional coordinate repairs the collision.
------------------------------------------------------------------------

residual14ToGlobal14 : Residual14Index → Ternary27GlobalInversionOrbit14
residual14ToGlobal14 residualMode09Negative = globalXOnlyOrbit
residual14ToGlobal14 residualMode09Positive = globalOriginOrbit
residual14ToGlobal14 residualMode18Negative = globalXYOppositeZZeroOrbit
residual14ToGlobal14 residualMode18Zero = globalYOnlyOrbit
residual14ToGlobal14 residualMode18Positive = globalXYEqualZZeroOrbit
residual14ToGlobal14 residualMode27Negative = globalXZOppositeYZeroOrbit
residual14ToGlobal14 residualMode27Zero = globalZOnlyOrbit
residual14ToGlobal14 residualMode27Positive = globalXZEqualYZeroOrbit
residual14ToGlobal14 residualMode36Negative = globalYZEqualXOppositeOrbit
residual14ToGlobal14 residualMode36Zero = globalYZEqualXZeroOrbit
residual14ToGlobal14 residualMode36Positive = globalAllEqualOrbit
residual14ToGlobal14 residualMode45Negative = globalXZEqualYOppositeOrbit
residual14ToGlobal14 residualMode45Zero = globalYZOppositeXZeroOrbit
residual14ToGlobal14 residualMode45Positive = globalXYEqualZOppositeOrbit

global14ToResidual14 : Ternary27GlobalInversionOrbit14 → Residual14Index
global14ToResidual14 globalOriginOrbit = residualMode09Positive
global14ToResidual14 globalXOnlyOrbit = residualMode09Negative
global14ToResidual14 globalYOnlyOrbit = residualMode18Zero
global14ToResidual14 globalZOnlyOrbit = residualMode27Zero
global14ToResidual14 globalXYEqualZZeroOrbit = residualMode18Positive
global14ToResidual14 globalXYOppositeZZeroOrbit = residualMode18Negative
global14ToResidual14 globalXZEqualYZeroOrbit = residualMode27Positive
global14ToResidual14 globalXZOppositeYZeroOrbit = residualMode27Negative
global14ToResidual14 globalYZEqualXZeroOrbit = residualMode36Zero
global14ToResidual14 globalYZOppositeXZeroOrbit = residualMode45Zero
global14ToResidual14 globalAllEqualOrbit = residualMode36Positive
global14ToResidual14 globalXYEqualZOppositeOrbit = residualMode45Positive
global14ToResidual14 globalXZEqualYOppositeOrbit = residualMode45Negative
global14ToResidual14 globalYZEqualXOppositeOrbit = residualMode36Negative

residualGlobalRoundTrip :
  (r : Residual14Index) → global14ToResidual14 (residual14ToGlobal14 r) ≡ r
residualGlobalRoundTrip residualMode09Negative = refl
residualGlobalRoundTrip residualMode09Positive = refl
residualGlobalRoundTrip residualMode18Negative = refl
residualGlobalRoundTrip residualMode18Zero = refl
residualGlobalRoundTrip residualMode18Positive = refl
residualGlobalRoundTrip residualMode27Negative = refl
residualGlobalRoundTrip residualMode27Zero = refl
residualGlobalRoundTrip residualMode27Positive = refl
residualGlobalRoundTrip residualMode36Negative = refl
residualGlobalRoundTrip residualMode36Zero = refl
residualGlobalRoundTrip residualMode36Positive = refl
residualGlobalRoundTrip residualMode45Negative = refl
residualGlobalRoundTrip residualMode45Zero = refl
residualGlobalRoundTrip residualMode45Positive = refl

globalResidualRoundTrip :
  (g : Ternary27GlobalInversionOrbit14) → residual14ToGlobal14 (global14ToResidual14 g) ≡ g
globalResidualRoundTrip globalOriginOrbit = refl
globalResidualRoundTrip globalXOnlyOrbit = refl
globalResidualRoundTrip globalYOnlyOrbit = refl
globalResidualRoundTrip globalZOnlyOrbit = refl
globalResidualRoundTrip globalXYEqualZZeroOrbit = refl
globalResidualRoundTrip globalXYOppositeZZeroOrbit = refl
globalResidualRoundTrip globalXZEqualYZeroOrbit = refl
globalResidualRoundTrip globalXZOppositeYZeroOrbit = refl
globalResidualRoundTrip globalYZEqualXZeroOrbit = refl
globalResidualRoundTrip globalYZOppositeXZeroOrbit = refl
globalResidualRoundTrip globalAllEqualOrbit = refl
globalResidualRoundTrip globalXYEqualZOppositeOrbit = refl
globalResidualRoundTrip globalXZEqualYOppositeOrbit = refl
globalResidualRoundTrip globalYZEqualXOppositeOrbit = refl

exceptionalLaneTargetsOrigin :
  residual14ToGlobal14 residualMode09Positive ≡ globalOriginOrbit
exceptionalLaneTargetsOrigin = refl

exceptionalLaneNaturalTargetIsXOnly :
  naturalGlobalTarget residualMode09Positive ≡ globalXOnlyOrbit
exceptionalLaneNaturalTargetIsXOnly = refl

------------------------------------------------------------------------
-- 5. WrongType / attribution boundaries.
------------------------------------------------------------------------

data ExplicitWeldEqualsCanonicalLiftInducedMap : Set where
data ExplicitWeldCreatesMonsterAction : Set where
data ExplicitWeldCreatesD4SemanticIdentity : Set where

explicitWeldDoesNotEqualCanonicalLiftInducedMap :
  ExplicitWeldEqualsCanonicalLiftInducedMap → ⊥
explicitWeldDoesNotEqualCanonicalLiftInducedMap ()

explicitWeldDoesNotCreateMonsterAction :
  ExplicitWeldCreatesMonsterAction → ⊥
explicitWeldDoesNotCreateMonsterAction ()

explicitWeldDoesNotCreateD4SemanticIdentity :
  ExplicitWeldCreatesD4SemanticIdentity → ⊥
explicitWeldDoesNotCreateD4SemanticIdentity ()

existingResidual14Carrier : Carrier14.Monster42dFifteenFourteenBoundary
existingResidual14Carrier = Carrier14.currentMonster42dFifteenFourteenBoundary

record SSP14Global14WeldBoundary : Set where
  constructor ssp14-global14-weld-boundary
  field
    existingSSP14CarrierReused : Bool
    existingTernary27CarrierReused : Bool
    fullGlobalInversionQuotientConstructed : Bool
    fullGlobalInversionNegationInvariantPaid : Bool
    naturalCanonicalLiftCollisionObserved : Bool
    explicitResidual14Global14WeldPaid : Bool
    explicitWeldIsCanonicalLiftInduced : Bool
    newExternalSourceClaimIntroduced : Bool
    weldCreatesD4SemanticIdentity : Bool
    weldCreatesMonsterAction : Bool
    nextResidual : String
open SSP14Global14WeldBoundary public

currentSSP14Global14WeldBoundary : SSP14Global14WeldBoundary
currentSSP14Global14WeldBoundary =
  ssp14-global14-weld-boundary
    true true true true true true
    false false false false
    "The two fourteen-element carriers are now explicitly bijective, but the chart is not induced by the canonical SSP15 lift followed by the full T^3/global-inversion quotient. That natural map has a single collision: the two residual mode09 sign lanes share the x-axis orbit, while the deleted neutral origin lane leaves the fixed origin orbit absent. The explicit weld repairs exactly that coordinate by sending residual (mode09,+) to the origin orbit. Treat this as finite reindexing only; the next independent debt is the canonical NineOrbit adapter into the merged five-orbit D4/N(3B) screen, with Monster action authority still unpaid."

explicitResidual14Global14WeldPaidIsTrue :
  explicitResidual14Global14WeldPaid currentSSP14Global14WeldBoundary ≡ true
explicitResidual14Global14WeldPaidIsTrue = refl

explicitWeldIsCanonicalLiftInducedIsFalse :
  explicitWeldIsCanonicalLiftInduced currentSSP14Global14WeldBoundary ≡ false
explicitWeldIsCanonicalLiftInducedIsFalse = refl

weldCreatesMonsterActionIsFalse :
  weldCreatesMonsterAction currentSSP14Global14WeldBoundary ≡ false
weldCreatesMonsterActionIsFalse = refl
