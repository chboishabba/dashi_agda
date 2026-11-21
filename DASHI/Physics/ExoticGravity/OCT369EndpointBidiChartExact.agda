module DASHI.Physics.ExoticGravity.OCT369EndpointBidiChartExact where

-- P0.25: 3 L12 Mn site indices × 2 magnetic domains as an exact partial
-- decoder into the ORIGINAL native DASHI balanced-ternary 27-point carrier.
-- This is an INDEX selection, NOT an assertion of physical coordinate
-- identity or metric equivalence. Native geometry and typed antigravity
-- discriminator owners retain provenance. No experimental claim follows.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.SSPTritCarrier as SSP
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

negateTrit : SSP.SSPTrit → SSP.SSPTrit
negateTrit SSP.sspNegOne = SSP.sspPosOne
negateTrit SSP.sspZero = SSP.sspZero
negateTrit SSP.sspPosOne = SSP.sspNegOne
antipode : Address → Address
antipode (Cube.ternary27Point a b c) =
  Cube.ternary27Point (negateTrit a) (negateTrit b) (negateTrit c)
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

negateTritTwice : (t : SSP.SSPTrit) → negateTrit (negateTrit t) ≡ t
negateTritTwice SSP.sspNegOne = refl
negateTritTwice SSP.sspZero = refl
negateTritTwice SSP.sspPosOne = refl

antipodeTwice : (a : Address) → antipode (antipode a) ≡ a
antipodeTwice (Cube.ternary27Point a b c)
  rewrite negateTritTwice a | negateTritTwice b | negateTritTwice c = refl

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
