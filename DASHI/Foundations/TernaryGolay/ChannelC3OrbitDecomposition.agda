module DASHI.Foundations.TernaryGolay.ChannelC3OrbitDecomposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import Base369 using
  ( TriTruth ; tri-low ; tri-mid ; tri-high
  ; HexTruth ; hex-0 ; hex-1 ; hex-2 ; hex-3 ; hex-4 ; hex-5
  ; NonaryTruth ; non-0 ; non-1 ; non-2 ; non-3 ; non-4
  ; non-5 ; non-6 ; non-7 ; non-8
  )
open import DASHI.Foundations.RecursiveRadixHypervoxel using
  ( Axis3 ; axis-low ; axis-mid ; axis-high )

------------------------------------------------------------------------
-- Three axes, six directed off-diagonal faces, and nine ordered channels.
--
-- Correction to a common informal claim:
--   * under the full S3 action, the six off-diagonal channels form one orbit;
--   * under the rotation subgroup C3, they split into a cyclic orbit and an
--     anti-cyclic orbit, each of size three.
------------------------------------------------------------------------

data Channel : Set where
  low-low low-mid low-high : Channel
  mid-low mid-mid mid-high : Channel
  high-low high-mid high-high : Channel

data DirectedFace : Set where
  low-to-mid mid-to-high high-to-low : DirectedFace
  mid-to-low high-to-mid low-to-high : DirectedFace

data C3Orbit : Set where
  diagonalOrbit cyclicOrbit antiCyclicOrbit : C3Orbit

data S3Orbit : Set where
  diagonalS3Orbit offDiagonalS3Orbit : S3Orbit

channel : Axis3 → Axis3 → Channel
channel axis-low axis-low = low-low
channel axis-low axis-mid = low-mid
channel axis-low axis-high = low-high
channel axis-mid axis-low = mid-low
channel axis-mid axis-mid = mid-mid
channel axis-mid axis-high = mid-high
channel axis-high axis-low = high-low
channel axis-high axis-mid = high-mid
channel axis-high axis-high = high-high

sourceAxis : Channel → Axis3
sourceAxis low-low = axis-low
sourceAxis low-mid = axis-low
sourceAxis low-high = axis-low
sourceAxis mid-low = axis-mid
sourceAxis mid-mid = axis-mid
sourceAxis mid-high = axis-mid
sourceAxis high-low = axis-high
sourceAxis high-mid = axis-high
sourceAxis high-high = axis-high

targetAxis : Channel → Axis3
targetAxis low-low = axis-low
targetAxis low-mid = axis-mid
targetAxis low-high = axis-high
targetAxis mid-low = axis-low
targetAxis mid-mid = axis-mid
targetAxis mid-high = axis-high
targetAxis high-low = axis-low
targetAxis high-mid = axis-mid
targetAxis high-high = axis-high

channelRoundTrip : (c : Channel) → channel (sourceAxis c) (targetAxis c) ≡ c
channelRoundTrip low-low = refl
channelRoundTrip low-mid = refl
channelRoundTrip low-high = refl
channelRoundTrip mid-low = refl
channelRoundTrip mid-mid = refl
channelRoundTrip mid-high = refl
channelRoundTrip high-low = refl
channelRoundTrip high-mid = refl
channelRoundTrip high-high = refl

rotateAxis : Axis3 → Axis3
rotateAxis axis-low = axis-mid
rotateAxis axis-mid = axis-high
rotateAxis axis-high = axis-low

swapLowMid : Axis3 → Axis3
swapLowMid axis-low = axis-mid
swapLowMid axis-mid = axis-low
swapLowMid axis-high = axis-high

rotateChannel : Channel → Channel
rotateChannel c = channel (rotateAxis (sourceAxis c)) (rotateAxis (targetAxis c))

swapLowMidChannel : Channel → Channel
swapLowMidChannel c = channel (swapLowMid (sourceAxis c)) (swapLowMid (targetAxis c))

rotateAxisCubed : (a : Axis3) → rotateAxis (rotateAxis (rotateAxis a)) ≡ a
rotateAxisCubed axis-low = refl
rotateAxisCubed axis-mid = refl
rotateAxisCubed axis-high = refl

rotateChannelCubed :
  (c : Channel) →
  rotateChannel (rotateChannel (rotateChannel c)) ≡ c
rotateChannelCubed low-low = refl
rotateChannelCubed low-mid = refl
rotateChannelCubed low-high = refl
rotateChannelCubed mid-low = refl
rotateChannelCubed mid-mid = refl
rotateChannelCubed mid-high = refl
rotateChannelCubed high-low = refl
rotateChannelCubed high-mid = refl
rotateChannelCubed high-high = refl

c3OrbitOf : Channel → C3Orbit
c3OrbitOf low-low = diagonalOrbit
c3OrbitOf mid-mid = diagonalOrbit
c3OrbitOf high-high = diagonalOrbit
c3OrbitOf low-mid = cyclicOrbit
c3OrbitOf mid-high = cyclicOrbit
c3OrbitOf high-low = cyclicOrbit
c3OrbitOf mid-low = antiCyclicOrbit
c3OrbitOf high-mid = antiCyclicOrbit
c3OrbitOf low-high = antiCyclicOrbit

s3OrbitOf : Channel → S3Orbit
s3OrbitOf low-low = diagonalS3Orbit
s3OrbitOf mid-mid = diagonalS3Orbit
s3OrbitOf high-high = diagonalS3Orbit
s3OrbitOf _ = offDiagonalS3Orbit

c3OrbitRotationInvariant :
  (c : Channel) → c3OrbitOf (rotateChannel c) ≡ c3OrbitOf c
c3OrbitRotationInvariant low-low = refl
c3OrbitRotationInvariant low-mid = refl
c3OrbitRotationInvariant low-high = refl
c3OrbitRotationInvariant mid-low = refl
c3OrbitRotationInvariant mid-mid = refl
c3OrbitRotationInvariant mid-high = refl
c3OrbitRotationInvariant high-low = refl
c3OrbitRotationInvariant high-mid = refl
c3OrbitRotationInvariant high-high = refl

-- A transposition exchanges the two C3 off-diagonal orbits, showing that
-- they are not distinct orbits for the full S3 action.
swapExchangesCyclicOrientation :
  c3OrbitOf (swapLowMidChannel low-mid) ≡ antiCyclicOrbit
swapExchangesCyclicOrientation = refl

swapReturnsToSingleS3Orbit :
  s3OrbitOf (swapLowMidChannel low-mid) ≡ offDiagonalS3Orbit
swapReturnsToSingleS3Orbit = refl

faceChannel : DirectedFace → Channel
faceChannel low-to-mid = low-mid
faceChannel mid-to-high = mid-high
faceChannel high-to-low = high-low
faceChannel mid-to-low = mid-low
faceChannel high-to-mid = high-mid
faceChannel low-to-high = low-high

channelFace : DirectedFace → DirectedFace
channelFace face = face

faceToHex : DirectedFace → HexTruth
faceToHex low-to-mid = hex-0
faceToHex mid-to-high = hex-1
faceToHex high-to-low = hex-2
faceToHex mid-to-low = hex-3
faceToHex high-to-mid = hex-4
faceToHex low-to-high = hex-5

hexToFace : HexTruth → DirectedFace
hexToFace hex-0 = low-to-mid
hexToFace hex-1 = mid-to-high
hexToFace hex-2 = high-to-low
hexToFace hex-3 = mid-to-low
hexToFace hex-4 = high-to-mid
hexToFace hex-5 = low-to-high

faceHexRoundTrip : (f : DirectedFace) → hexToFace (faceToHex f) ≡ f
faceHexRoundTrip low-to-mid = refl
faceHexRoundTrip mid-to-high = refl
faceHexRoundTrip high-to-low = refl
faceHexRoundTrip mid-to-low = refl
faceHexRoundTrip high-to-mid = refl
faceHexRoundTrip low-to-high = refl

channelToNonary : Channel → NonaryTruth
channelToNonary low-low = non-0
channelToNonary low-mid = non-1
channelToNonary low-high = non-2
channelToNonary mid-low = non-3
channelToNonary mid-mid = non-4
channelToNonary mid-high = non-5
channelToNonary high-low = non-6
channelToNonary high-mid = non-7
channelToNonary high-high = non-8

nonaryToChannel : NonaryTruth → Channel
nonaryToChannel non-0 = low-low
nonaryToChannel non-1 = low-mid
nonaryToChannel non-2 = low-high
nonaryToChannel non-3 = mid-low
nonaryToChannel non-4 = mid-mid
nonaryToChannel non-5 = mid-high
nonaryToChannel non-6 = high-low
nonaryToChannel non-7 = high-mid
nonaryToChannel non-8 = high-high

channelNonaryRoundTrip : (c : Channel) → nonaryToChannel (channelToNonary c) ≡ c
channelNonaryRoundTrip low-low = refl
channelNonaryRoundTrip low-mid = refl
channelNonaryRoundTrip low-high = refl
channelNonaryRoundTrip mid-low = refl
channelNonaryRoundTrip mid-mid = refl
channelNonaryRoundTrip mid-high = refl
channelNonaryRoundTrip high-low = refl
channelNonaryRoundTrip high-mid = refl
channelNonaryRoundTrip high-high = refl

axisToTri : Axis3 → TriTruth
axisToTri axis-low = tri-low
axisToTri axis-mid = tri-mid
axisToTri axis-high = tri-high

triToAxis : TriTruth → Axis3
triToAxis tri-low = axis-low
triToAxis tri-mid = axis-mid
triToAxis tri-high = axis-high

axisTriRoundTrip : (a : Axis3) → triToAxis (axisToTri a) ≡ a
axisTriRoundTrip axis-low = refl
axisTriRoundTrip axis-mid = refl
axisTriRoundTrip axis-high = refl

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

allChannels : List Channel
allChannels =
  low-low ∷ low-mid ∷ low-high
  ∷ mid-low ∷ mid-mid ∷ mid-high
  ∷ high-low ∷ high-mid ∷ high-high ∷ []

allDirectedFaces : List DirectedFace
allDirectedFaces =
  low-to-mid ∷ mid-to-high ∷ high-to-low
  ∷ mid-to-low ∷ high-to-mid ∷ low-to-high ∷ []

allDiagonalChannels : List Channel
allDiagonalChannels = low-low ∷ mid-mid ∷ high-high ∷ []

channelCountIsNine : listCount allChannels ≡ 9
channelCountIsNine = refl

faceCountIsSix : listCount allDirectedFaces ≡ 6
faceCountIsSix = refl

diagonalCountIsThree : listCount allDiagonalChannels ≡ 3
diagonalCountIsThree = refl
