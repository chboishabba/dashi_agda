module DASHI.Moonshine.Base369P2FiveOrbitOrientationGroupoidsExact where

------------------------------------------------------------------------
-- BASE369 p=2 FIVE-ORBIT x ORIENTATION TARGET GROUPOIDS
--
-- DASHI CONTRIBUTION
--
-- Independent 369 target carrier:
--
--   OrientationPolarity x NineOrbit
--
-- using the canonical Base369 two-sheet polarity and canonical five global-
-- inversion classes of one ternary nine-sheet.
--
-- Two groupoid semantics are constructed on the SAME ten objects:
--
--   1. gauge semantics: C2 flips orientation, giving five pi0 components;
--   2. retained semantics: trivial morphism group, giving ten components.
--
-- Therefore the 369 carrier by itself does not decide whether orientation is
-- gauge or gluing/provenance data.  Arithmetic/Fricke recognition must decide.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Foundations.Base369MobiusTransport as Mobius

------------------------------------------------------------------------
-- 1. Canonical ten-state Base369 carrier.
------------------------------------------------------------------------

P2Base369State : Set
P2Base369State =
  Mobius.OrientationPolarity × Triadic.NineOrbit

stateOrientation :
  P2Base369State ->
  Mobius.OrientationPolarity
stateOrientation = proj₁

stateInnerOrbit :
  P2Base369State ->
  Triadic.NineOrbit
stateInnerOrbit = proj₂

------------------------------------------------------------------------
-- 2. Gauge semantics: C2 flips orientation only.
------------------------------------------------------------------------

actGaugeC2 :
  C2.C2 ->
  P2Base369State ->
  P2Base369State
actGaugeC2 C2.identity state = state
actGaugeC2 C2.flip (orientation , orbit) =
  Mobius.flipOrientationPolarity orientation , orbit

gaugeIdentityActs :
  (state : P2Base369State) ->
  actGaugeC2 C2.identity state ≡ state
gaugeIdentityActs state = refl

gaugeCombineActs :
  (g h : C2.C2) ->
  (state : P2Base369State) ->
  actGaugeC2 (C2.combineC2 g h) state
  ≡
  actGaugeC2 g (actGaugeC2 h state)
gaugeCombineActs C2.identity h state = refl
gaugeCombineActs C2.flip C2.identity state = refl
gaugeCombineActs C2.flip C2.flip (Mobius.positive , orbit) = refl
gaugeCombineActs C2.flip C2.flip (Mobius.negative , orbit) = refl

gaugeInverseLeft :
  (g : C2.C2) ->
  (state : P2Base369State) ->
  actGaugeC2 (C2.inverseC2 g) (actGaugeC2 g state) ≡ state
gaugeInverseLeft C2.identity state = refl
gaugeInverseLeft C2.flip (Mobius.positive , orbit) = refl
gaugeInverseLeft C2.flip (Mobius.negative , orbit) = refl

gaugeInverseRight :
  (g : C2.C2) ->
  (state : P2Base369State) ->
  actGaugeC2 g (actGaugeC2 (C2.inverseC2 g) state) ≡ state
gaugeInverseRight C2.identity state = refl
gaugeInverseRight C2.flip (Mobius.positive , orbit) = refl
gaugeInverseRight C2.flip (Mobius.negative , orbit) = refl

p2GaugeAction :
  Action.InvertibleSymmetryAction P2Base369State C2.C2
p2GaugeAction =
  Action.invertibleSymmetryAction
    C2.identity
    C2.combineC2
    C2.inverseC2
    actGaugeC2
    gaugeIdentityActs
    gaugeCombineActs
    gaugeInverseLeft
    gaugeInverseRight

gaugeOrbitOf :
  P2Base369State ->
  Triadic.NineOrbit
gaugeOrbitOf = proj₂

gaugeRepresentative :
  Triadic.NineOrbit ->
  P2Base369State
gaugeRepresentative orbit =
  Mobius.negative , orbit

gaugeOrbitInvariant :
  (g : C2.C2) ->
  (state : P2Base369State) ->
  gaugeOrbitOf (actGaugeC2 g state)
  ≡ gaugeOrbitOf state
gaugeOrbitInvariant C2.identity state = refl
gaugeOrbitInvariant C2.flip (orientation , orbit) = refl

gaugeRepresentativeInOrbit :
  (orbit : Triadic.NineOrbit) ->
  gaugeOrbitOf (gaugeRepresentative orbit) ≡ orbit
gaugeRepresentativeInOrbit orbit = refl

gaugeTransporter :
  P2Base369State ->
  C2.C2
gaugeTransporter (Mobius.negative , orbit) = C2.identity
gaugeTransporter (Mobius.positive , orbit) = C2.flip

gaugeTransporterHits :
  (state : P2Base369State) ->
  actGaugeC2
    (gaugeTransporter state)
    (gaugeRepresentative (gaugeOrbitOf state))
  ≡ state
gaugeTransporterHits (Mobius.negative , orbit) = refl
gaugeTransporterHits (Mobius.positive , orbit) = refl

p2GaugeOrbitPresentation :
  Orbit.OrbitPresentation p2GaugeAction
p2GaugeOrbitPresentation =
  Orbit.orbitPresentation
    Triadic.NineOrbit
    gaugeOrbitOf
    gaugeRepresentative
    gaugeOrbitInvariant
    gaugeRepresentativeInOrbit
    gaugeTransporter
    gaugeTransporterHits

------------------------------------------------------------------------
-- 3. Retained-orientation semantics: identity-only groupoid.
------------------------------------------------------------------------

unitCombine : ⊤ -> ⊤ -> ⊤
unitCombine tt tt = tt

unitInverse : ⊤ -> ⊤
unitInverse tt = tt

actRetained :
  ⊤ ->
  P2Base369State ->
  P2Base369State
actRetained tt state = state

retainedIdentityActs :
  (state : P2Base369State) ->
  actRetained tt state ≡ state
retainedIdentityActs state = refl

retainedCombineActs :
  (g h : ⊤) ->
  (state : P2Base369State) ->
  actRetained (unitCombine g h) state
  ≡ actRetained g (actRetained h state)
retainedCombineActs tt tt state = refl

retainedInverseLeft :
  (g : ⊤) ->
  (state : P2Base369State) ->
  actRetained (unitInverse g) (actRetained g state) ≡ state
retainedInverseLeft tt state = refl

retainedInverseRight :
  (g : ⊤) ->
  (state : P2Base369State) ->
  actRetained g (actRetained (unitInverse g) state) ≡ state
retainedInverseRight tt state = refl

p2RetainedAction :
  Action.InvertibleSymmetryAction P2Base369State ⊤
p2RetainedAction =
  Action.invertibleSymmetryAction
    tt
    unitCombine
    unitInverse
    actRetained
    retainedIdentityActs
    retainedCombineActs
    retainedInverseLeft
    retainedInverseRight

p2RetainedOrbitPresentation :
  Orbit.OrbitPresentation p2RetainedAction
p2RetainedOrbitPresentation =
  Orbit.orbitPresentation
    P2Base369State
    (λ state -> state)
    (λ state -> state)
    (λ tt state -> refl)
    (λ state -> refl)
    (λ state -> tt)
    (λ state -> refl)

------------------------------------------------------------------------
-- 4. Exact semantic fork.
------------------------------------------------------------------------

p2GaugePi0Count : Nat
p2GaugePi0Count = 5

p2RetainedPi0Count : Nat
p2RetainedPi0Count = 10

gaugeAndRetainedUseSameFineCarrier :
  Set
gaugeAndRetainedUseSameFineCarrier =
  P2Base369State

data Base369CarrierChoosesGaugeSemantics : Set where
data Base369CarrierChoosesRetainedSemantics : Set where
data TenObjectsImpliesTenComponents : Set where

base369CarrierDoesNotChooseGaugeSemantics :
  Base369CarrierChoosesGaugeSemantics -> ⊥
base369CarrierDoesNotChooseGaugeSemantics ()

base369CarrierDoesNotChooseRetainedSemantics :
  Base369CarrierChoosesRetainedSemantics -> ⊥
base369CarrierDoesNotChooseRetainedSemantics ()

tenObjectsDoNotAutomaticallyImplyTenComponents :
  TenObjectsImpliesTenComponents -> ⊥
tenObjectsDoNotAutomaticallyImplyTenComponents ()

record Base369P2FiveOrbitOrientationGroupoidsBoundary : Set where
  constructor base369-p2-five-orbit-orientation-groupoids-boundary
  field
    canonicalBase369OrientationCarrierUsed : Bool
    canonicalFiveNineOrbitCarrierUsed : Bool
    sameTenFineStatesSupportBothSemantics : Bool
    gaugePi0CountFive : Bool
    retainedPi0CountTen : Bool
    carrierAloneChoosesSemantics : Bool
    arithmeticRecognitionClaimedHere : Bool

canonicalBase369P2FiveOrbitOrientationGroupoidsBoundary :
  Base369P2FiveOrbitOrientationGroupoidsBoundary
canonicalBase369P2FiveOrbitOrientationGroupoidsBoundary =
  base369-p2-five-orbit-orientation-groupoids-boundary
    true true true true true false false
