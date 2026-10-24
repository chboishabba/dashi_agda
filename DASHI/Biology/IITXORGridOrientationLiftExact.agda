module DASHI.Biology.IITXORGridOrientationLiftExact where

------------------------------------------------------------------------
-- SAME GRID FABRIC, DIFFERENT USE OF INPUT ORDER
--
-- The grid-wide owner IITXORGridSynthesisFabricExact exposes the causal fabric
-- independently of the local law.  This module places the characteristic-2 /
-- characteristic-3 parity split on that exact same fabric.
--
-- Boolean XOR and ternary sum are symmetric: globally swapping every cell's
-- named A/B input sockets leaves the step unchanged.  Ternary difference is
-- antisymmetric: the identical socket swap negates every local output.
--
-- Hence a recurrent XOR grid already has the same 2-input/1-output synthesis
-- architecture as the trialectic/torque cells.  What Boolean XOR lacks is not
-- causal arity or gluing complexity, but a local algebra that consumes the
-- retained A/B ordering as handedness.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Biology.IITCausalPantsFibreGluingExact as Pants
import DASHI.Biology.IITXORGridSynthesisFabricExact as GridFabric
import DASHI.Biology.IITBinaryTernaryParityTorqueLiftExact as Lift

TriField : Set → Set
TriField Site = Site → Base.TriTruth

triSumFabricStep :
  {Site : Set} →
  GridFabric.TwoInputFabric Site →
  TriField Site →
  TriField Site
triSumFabricStep fabric state target =
  Lift.triSum
    (state (GridFabric.inputASource fabric target))
    (state (GridFabric.inputBSource fabric target))

triDiffFabricStep :
  {Site : Set} →
  GridFabric.TwoInputFabric Site →
  TriField Site →
  TriField Site
triDiffFabricStep fabric state target =
  Lift.triDiff
    (state (GridFabric.inputASource fabric target))
    (state (GridFabric.inputBSource fabric target))

------------------------------------------------------------------------
-- Same local causal-pants ABI on ternary fibres.
------------------------------------------------------------------------

siteTriFamily : {Site : Set} → Pants.FibreFamily Site
siteTriFamily = record { Fibre = λ _ → Base.TriTruth }

triWireAAt :
  {Site : Set} →
  (fabric : GridFabric.TwoInputFabric Site) →
  (target : Site) →
  Pants.OutputInputGluing
    siteTriFamily
    (GridFabric.inputASource fabric target)
    target
triWireAAt fabric target = record
  { targetPort = Pants.inputA
  ; transport = λ x → x
  }

triWireBAt :
  {Site : Set} →
  (fabric : GridFabric.TwoInputFabric Site) →
  (target : Site) →
  Pants.OutputInputGluing
    siteTriFamily
    (GridFabric.inputBSource fabric target)
    target
triWireBAt fabric target = record
  { targetPort = Pants.inputB
  ; transport = λ x → x
  }

triWiringAt :
  {Site : Set} →
  (fabric : GridFabric.TwoInputFabric Site) →
  (target : Site) →
  Pants.TwoSourceInputGluing
    siteTriFamily
    (GridFabric.inputASource fabric target)
    (GridFabric.inputBSource fabric target)
    target
triWiringAt fabric target = record
  { leftWire = triWireAAt fabric target
  ; rightWire = triWireBAt fabric target
  ; leftTargetsA = refl
  ; rightTargetsB = refl
  }

triSumCellAt :
  {Site : Set} →
  (target : Site) →
  Pants.LocalSynthesisCell siteTriFamily target
triSumCellAt target = record { combine = Lift.triSum }

triDiffCellAt :
  {Site : Set} →
  (target : Site) →
  Pants.LocalSynthesisCell siteTriFamily target
triDiffCellAt target = record { combine = Lift.triDiff }

gluedTriSumEqualsFabricStep :
  {Site : Set} →
  (fabric : GridFabric.TwoInputFabric Site) →
  (state : TriField Site) →
  (target : Site) →
  Pants.evaluateGluedCell
    (triWiringAt fabric target)
    (triSumCellAt target)
    (state (GridFabric.inputASource fabric target))
    (state (GridFabric.inputBSource fabric target))
  ≡ triSumFabricStep fabric state target
gluedTriSumEqualsFabricStep fabric state target = refl

gluedTriDiffEqualsFabricStep :
  {Site : Set} →
  (fabric : GridFabric.TwoInputFabric Site) →
  (state : TriField Site) →
  (target : Site) →
  Pants.evaluateGluedCell
    (triWiringAt fabric target)
    (triDiffCellAt target)
    (state (GridFabric.inputASource fabric target))
    (state (GridFabric.inputBSource fabric target))
  ≡ triDiffFabricStep fabric state target
gluedTriDiffEqualsFabricStep fabric state target = refl

------------------------------------------------------------------------
-- Global input-socket swap: symmetric channels quotient orientation;
-- antisymmetric difference consumes it and negates pointwise.
------------------------------------------------------------------------

triSumStepIgnoresLocalInputOrder :
  {Site : Set} →
  (fabric : GridFabric.TwoInputFabric Site) →
  (state : TriField Site) →
  (target : Site) →
  triSumFabricStep (GridFabric.swapFabricInputs fabric) state target
  ≡ triSumFabricStep fabric state target
triSumStepIgnoresLocalInputOrder fabric state target =
  Lift.triSumSwapInvariant
    (state (GridFabric.inputBSource fabric target))
    (state (GridFabric.inputASource fabric target))

triDiffStepSwapNegatesPointwise :
  {Site : Set} →
  (fabric : GridFabric.TwoInputFabric Site) →
  (state : TriField Site) →
  (target : Site) →
  triDiffFabricStep (GridFabric.swapFabricInputs fabric) state target
  ≡ Lift.triNeg (triDiffFabricStep fabric state target)
triDiffStepSwapNegatesPointwise fabric state target =
  Lift.triDiffSwapNegates
    (state (GridFabric.inputASource fabric target))
    (state (GridFabric.inputBSource fabric target))

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record XORGridOrientationLiftBoundary : Set where
  constructor xor-grid-orientation-lift-boundary
  field
    booleanAndTernaryUseSameTwoInputFabricType : Bool
    booleanXorSwapInvariant : Bool
    ternarySumSwapInvariant : Bool
    ternaryDifferenceSwapNegates : Bool
    namedABOrderingExistsBeforeLocalLaw : Bool
    booleanXorErasesThatOrderingFromItsOutput : Bool
    antisymmetricTernaryLawCanConsumeThatOrdering : Bool
    higherOrderGridIntegrationRequiresPrimitiveThreeInputGate : Bool
    antisymmetricGridOutputIsPhysicalTorqueByDefinition : Bool
    siblingTorqueTheoremAuthorityImported : Bool
open XORGridOrientationLiftBoundary public

canonicalXORGridOrientationLiftBoundary : XORGridOrientationLiftBoundary
canonicalXORGridOrientationLiftBoundary =
  xor-grid-orientation-lift-boundary
    true true true true true true true false false false

sameFabricSupportsOrientationBlindAndSensitiveChannels :
  booleanXorSwapInvariant canonicalXORGridOrientationLiftBoundary ≡ true
  × ternaryDifferenceSwapNegates canonicalXORGridOrientationLiftBoundary ≡ true
sameFabricSupportsOrientationBlindAndSensitiveChannels = refl , refl

higherOrderGridDoesNotRequirePrimitiveTriadicGate :
  higherOrderGridIntegrationRequiresPrimitiveThreeInputGate
    canonicalXORGridOrientationLiftBoundary ≡ false
higherOrderGridDoesNotRequirePrimitiveTriadicGate = refl
