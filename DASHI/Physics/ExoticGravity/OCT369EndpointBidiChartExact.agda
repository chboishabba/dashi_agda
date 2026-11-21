module DASHI.Physics.ExoticGravity.OCT369EndpointBidiChartExact where

-- P0.25: 3 L12 Mn site indices × 2 magnetic domains as an exact partial
-- decoder into the ORIGINAL native DASHI balanced-ternary 27-point carrier.
-- This is an INDEX selection, NOT an assertion of physical coordinate
-- identity or metric equivalence. Native geometry and typed antigravity
-- discriminator owners retain provenance. No experimental claim follows.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Unified.Hyperfabric27MinusOneAntipodalSameCarrierCutExact as Native
import DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact as Q13
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti

data MnSite : Set where mn0 mn1 mn2 : MnSite
data Domain : Set where magPlus magMinus : Domain
record Label : Set where
  constructor labelled
  field
    site : MnSite
    domain : Domain
open Label public

Address : Set
Address = Cube.Ternary27Point

encode : Label → Address
encode (labelled mn0 magPlus) = Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne
encode (labelled mn1 magPlus) = Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero
encode (labelled mn2 magPlus) = Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne
encode (labelled mn0 magMinus) = Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne
encode (labelled mn1 magMinus) = Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero
encode (labelled mn2 magMinus) = Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne

decode : Address → Maybe Label
decode (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = just (labelled mn0 magPlus)
decode (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = just (labelled mn1 magPlus)
decode (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = just (labelled mn2 magPlus)
decode (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = just (labelled mn0 magMinus)
decode (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = just (labelled mn1 magMinus)
decode (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = just (labelled mn2 magMinus)
decode _ = nothing

roundTrip : (label : Label) → decode (encode label) ≡ just label
roundTrip (labelled mn0 magPlus) = refl
roundTrip (labelled mn1 magPlus) = refl
roundTrip (labelled mn2 magPlus) = refl
roundTrip (labelled mn0 magMinus) = refl
roundTrip (labelled mn1 magMinus) = refl
roundTrip (labelled mn2 magMinus) = refl

centreUnmapped : decode Cube.origin ≡ nothing
centreUnmapped = refl

rotate : Address → Address
rotate (Cube.ternary27Point a b c) = Cube.ternary27Point c a b
rotateSite : MnSite → MnSite
rotateSite mn0 = mn1
rotateSite mn1 = mn2
rotateSite mn2 = mn0
rotateLabel : Label → Label
rotateLabel (labelled a d) = labelled (rotateSite a) d

encodeCommutesWithC3 : (label : Label) → rotate (encode label) ≡ encode (rotateLabel label)
encodeCommutesWithC3 (labelled mn0 magPlus) = refl
encodeCommutesWithC3 (labelled mn1 magPlus) = refl
encodeCommutesWithC3 (labelled mn2 magPlus) = refl
encodeCommutesWithC3 (labelled mn0 magMinus) = refl
encodeCommutesWithC3 (labelled mn1 magMinus) = refl
encodeCommutesWithC3 (labelled mn2 magMinus) = refl

rotateCubeThree : (a : Address) → rotate (rotate (rotate a)) ≡ a
rotateCubeThree (Cube.ternary27Point a b c) = refl

-- Reuse the ORIGINAL signed antipode, no second definition.
antipode : Address → Address
antipode = Native.antipode

flipDomain : Domain → Domain
flipDomain magPlus = magMinus
flipDomain magMinus = magPlus
flipLabel : Label → Label
flipLabel (labelled a d) = labelled a (flipDomain d)

encodeCommutesWithAntipode : (label : Label) → antipode (encode label) ≡ encode (flipLabel label)
encodeCommutesWithAntipode (labelled mn0 magPlus) = refl
encodeCommutesWithAntipode (labelled mn1 magPlus) = refl
encodeCommutesWithAntipode (labelled mn2 magPlus) = refl
encodeCommutesWithAntipode (labelled mn0 magMinus) = refl
encodeCommutesWithAntipode (labelled mn1 magMinus) = refl
encodeCommutesWithAntipode (labelled mn2 magMinus) = refl

antipodeTwice : (a : Address) → antipode (antipode a) ≡ a
antipodeTwice = Native.antipodeInvolutive

-- THIS is the native 13 × orientation decoding of the *same* six addresses.
-- The orientation Bool depends on Q13's canonical representative, not on
-- a globally fixed reinterpretation of physical magnetic domain signs.
projectiveAddress : Label → Q13.Axis13 × Bool
projectiveAddress (labelled mn0 magPlus) = Q13.faceXZpm , true
projectiveAddress (labelled mn1 magPlus) = Q13.faceXYpm , false
projectiveAddress (labelled mn2 magPlus) = Q13.faceYZpm , false
projectiveAddress (labelled mn0 magMinus) = Q13.faceXZpm , false
projectiveAddress (labelled mn1 magMinus) = Q13.faceXYpm , true
projectiveAddress (labelled mn2 magMinus) = Q13.faceYZpm , true

nativeProjectiveDecodeCommutes :
  (label : Label) → Q13.decode (projectiveAddress label) ≡ encode label
nativeProjectiveDecodeCommutes (labelled mn0 magPlus) = refl
nativeProjectiveDecodeCommutes (labelled mn1 magPlus) = refl
nativeProjectiveDecodeCommutes (labelled mn2 magPlus) = refl
nativeProjectiveDecodeCommutes (labelled mn0 magMinus) = refl
nativeProjectiveDecodeCommutes (labelled mn1 magMinus) = refl
nativeProjectiveDecodeCommutes (labelled mn2 magMinus) = refl

nativeProjectiveEncodeCommutes :
  (label : Label) → Q13.encode (encode label) ≡ just (projectiveAddress label)
nativeProjectiveEncodeCommutes (labelled mn0 magPlus) = refl
nativeProjectiveEncodeCommutes (labelled mn1 magPlus) = refl
nativeProjectiveEncodeCommutes (labelled mn2 magPlus) = refl
nativeProjectiveEncodeCommutes (labelled mn0 magMinus) = refl
nativeProjectiveEncodeCommutes (labelled mn1 magMinus) = refl
nativeProjectiveEncodeCommutes (labelled mn2 magMinus) = refl

-- These are DIRECT projections of original six anti-gravity endpoints.
loadEndpoint :
  Anti.requiredDiscriminator Anti.reducedPassiveWeight ≡ Anti.staticLoadDiscriminator
loadEndpoint = refl
freeFallEndpoint :
  Anti.requiredDiscriminator Anti.changedFreeFallResponse ≡ Anti.freeFallDiscriminator
freeFallEndpoint = refl
remoteEndpoint :
  Anti.requiredDiscriminator Anti.remoteRepulsiveField ≡ Anti.externalTestMassDiscriminator
remoteEndpoint = refl
inertiaEndpoint :
  Anti.requiredDiscriminator Anti.alteredInertialResponse ≡ Anti.inertialComparisonDiscriminator
inertiaEndpoint = refl
impulseEndpoint :
  Anti.requiredDiscriminator Anti.persistentPropulsiveImpulse ≡ Anti.momentumClosureDiscriminator
impulseEndpoint = refl
clockEndpoint :
  Anti.requiredDiscriminator Anti.engineeredMetricResponse ≡ Anti.metricClockDiscriminator
clockEndpoint = refl

noCoarsePhysicalObservable :
  Anti.AntigravityPromotionBoundary.coarseAntigravityLabelIsPhysicalObservable
    Anti.canonicalAntigravityPromotionBoundary ≡ false
noCoarsePhysicalObservable = refl
