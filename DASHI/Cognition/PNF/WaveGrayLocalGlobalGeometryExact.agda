module DASHI.Cognition.PNF.WaveGrayLocalGlobalGeometryExact where

------------------------------------------------------------------------
-- Gray coding is transition-optimal for the Wave4 path, but local edge
-- optimality is not the same as preserving the whole path metric.  The first
-- and last Wave4 states are graph distance three apart while their Gray codes
-- are Hamming distance one apart.  This is an exact finite warning against
-- identifying minimum one-step transition cost with global geometric fidelity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave
import DASHI.Cognition.PNF.OrientedZeroGrayTransitionGeometryExact as Gray
import DASHI.Cognition.PNF.FinitePathTransitionOptimalityExact as Path

wavePathEndpointDistance : Nat
wavePathEndpointDistance = 3

grayEndpointCodeDistance : Nat
grayEndpointCodeDistance =
  Gray.hamming
    (Wave.grayCode Wave.negativeOne)
    (Wave.grayCode Wave.positiveOne)

binaryEndpointCodeDistance : Nat
binaryEndpointCodeDistance =
  Gray.hamming
    (Wave.binaryCode Wave.negativeOne)
    (Wave.binaryCode Wave.positiveOne)

grayEndpointCodeDistanceIsOne : grayEndpointCodeDistance ≡ 1
grayEndpointCodeDistanceIsOne = refl

binaryEndpointCodeDistanceIsTwo : binaryEndpointCodeDistance ≡ 2
binaryEndpointCodeDistanceIsTwo = refl

wavePathEndpointDistanceIsThree : wavePathEndpointDistance ≡ 3
wavePathEndpointDistanceIsThree = refl

grayFoldsLongRangePathDistance :
  grayEndpointCodeDistance < wavePathEndpointDistance
grayFoldsLongRangePathDistance = s≤s (s≤s z≤n)

binaryAlsoCompressesLongRangePathDistance :
  binaryEndpointCodeDistance < wavePathEndpointDistance
binaryAlsoCompressesLongRangePathDistance =
  s≤s (s≤s (s≤s z≤n))

-- The local theorem remains true simultaneously.
grayLocallyTransitionOptimal :
  Path.pathCost Path.waveGrayDistances ≤ Path.pathCost Path.waveBinaryDistances
grayLocallyTransitionOptimal = Path.waveGrayOptimalAgainstBinary

record LocalGlobalGeometrySeparation : Set where
  field
    grayIsLocallyOptimal :
      Path.pathCost Path.waveGrayDistances ≤ Path.pathCost Path.waveBinaryDistances
    grayEndpointDistanceIsStrictlyContracted :
      grayEndpointCodeDistance < wavePathEndpointDistance

waveLocalGlobalSeparation : LocalGlobalGeometrySeparation
waveLocalGlobalSeparation = record
  { grayIsLocallyOptimal = grayLocallyTransitionOptimal
  ; grayEndpointDistanceIsStrictlyContracted = grayFoldsLongRangePathDistance
  }

------------------------------------------------------------------------
-- Consequence for the programme:
--
--   edge distortion / update locality
--
-- and
--
--   all-pairs future / graph metric distortion
--
-- are distinct objectives.  A Pareto theory needs both when long-range
-- geometry matters to the consumer.
------------------------------------------------------------------------
