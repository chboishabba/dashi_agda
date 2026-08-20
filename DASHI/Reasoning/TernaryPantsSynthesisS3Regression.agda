module DASHI.Reasoning.TernaryPantsSynthesisS3Regression where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as S3
import DASHI.Reasoning.TernaryPantsSynthesisS3BridgeExact as Bridge
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Topology.TernaryPantsFrontierExact as Frontier

slotRoundTrip3 : Bridge.truthToSlot (Bridge.slotToTruth Pants.slot3) ≡ Pants.slot3
slotRoundTrip3 = refl

slotRoundTrip6 : Bridge.truthToSlot (Bridge.slotToTruth Pants.slot6) ≡ Pants.slot6
slotRoundTrip6 = refl

slotRoundTrip9 : Bridge.truthToSlot (Bridge.slotToTruth Pants.slot9) ≡ Pants.slot9
slotRoundTrip9 = refl

rotateSlot3 : Bridge.permuteSlot S3.permRotate Pants.slot3 ≡ Pants.slot6
rotateSlot3 = refl

rotateSlot6 : Bridge.permuteSlot S3.permRotate Pants.slot6 ≡ Pants.slot9
rotateSlot6 = refl

rotateSlot9 : Bridge.permuteSlot S3.permRotate Pants.slot9 ≡ Pants.slot3
rotateSlot9 = refl

depthThreeFrontierStillExact :
  Frontier.addressToPantsPath Frontier.depthThreeCylinder
  ≡ Frontier.depthThreePantsPath
depthThreeFrontierStillExact = refl

recursiveWeldKeepsSmoothBoundaryClosed :
  Bridge.TernaryPantsSynthesisS3Boundary.smoothPantsThickeningConstructed
    Bridge.canonicalTernaryPantsSynthesisS3Boundary
  ≡ false
recursiveWeldKeepsSmoothBoundaryClosed = refl

recursiveWreathStillOutstanding :
  Bridge.TernaryPantsSynthesisS3Boundary.localS3EqualsGlobalRecursiveWreathAction
    Bridge.canonicalTernaryPantsSynthesisS3Boundary
  ≡ false
recursiveWreathStillOutstanding = refl
