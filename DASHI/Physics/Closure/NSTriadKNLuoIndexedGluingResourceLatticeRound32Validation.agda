module DASHI.Physics.Closure.NSTriadKNLuoIndexedGluingResourceLatticeRound32Validation where

------------------------------------------------------------------------
-- Round Thirty-Two validation root.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNLuoHHBadScaleGainRound31Validation
import DASHI.Physics.Closure.NSTriadKNIndexedGluingRound32Exact as Gluing
import DASHI.Physics.Closure.NSTriadKNResourceLatticeRound32Exact as Resource
import DASHI.Physics.Closure.NSTriadKNScaleTransitionRound32Exact as Scale
import DASHI.Physics.Closure.NSTriadKNNineOwnerGridRound32Exact as Grid

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

indexedGluingRegression : Gluing.indexedGluingInterfaceClosed ≡ true
indexedGluingRegression = Gluing.indexedGluingInterfaceClosedIsTrue

resourceLatticeRegression : Resource.resourceLatticeClosed ≡ true
resourceLatticeRegression = Resource.resourceLatticeClosedIsTrue

forbiddenResourceRegression :
  Resource.forbiddenResourceFailClosed ≡ true
forbiddenResourceRegression = Resource.forbiddenResourceFailClosedIsTrue

scaleTransitionRegression :
  Scale.inverseScaleTransportInterfaceClosed ≡ true
scaleTransitionRegression = Scale.inverseScaleTransportInterfaceClosedIsTrue

physicalProducerStillOpenRegression :
  Scale.physicalInverseScaleProducerConstructed ≡ false
physicalProducerStillOpenRegression =
  Scale.physicalInverseScaleProducerConstructedIsFalse

nineOwnerGridRegression : Grid.nineOwnerGridClosed ≡ true
nineOwnerGridRegression = Grid.nineOwnerGridClosedIsTrue
