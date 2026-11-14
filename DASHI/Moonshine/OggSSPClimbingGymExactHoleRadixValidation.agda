module DASHI.Moonshine.OggSSPClimbingGymExactHoleRadixValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.NatRadialTreeCodecExact as NatRadix
import DASHI.Moonshine.OggSSPClimbingGymExactHoleRadixCodec as Hole
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym

------------------------------------------------------------------------
-- RED-first regression contract.
--
-- The production owners are intentionally imported before they exist.  The
-- target is not another radix tree: it must compile ordinary Nat residues into
-- the already-owned RadialTreeAddress and use that codec for exact JMD hole
-- vertices without requiring a constructive-real floor.
------------------------------------------------------------------------

p2Depth1Example :
  NatRadix.radialValue
    (Gym.oggPrimeRadixChart (Gym.formLane Gym.p2Exponent1))
    (NatRadix.natRadialAddress
      (Gym.oggPrimeRadixChart (Gym.formLane Gym.p2Exponent1)) 1 3)
  ≡ 1
p2Depth1Example = refl

p2Depth3Example :
  NatRadix.radialValue
    (Gym.oggPrimeRadixChart (Gym.formLane Gym.p2Exponent3))
    (NatRadix.natRadialAddress
      (Gym.oggPrimeRadixChart (Gym.formLane Gym.p2Exponent3)) 3 13)
  ≡ 5
p2Depth3Example = refl

p3Depth2Example :
  NatRadix.radialValue
    (Gym.oggPrimeRadixChart (Gym.formLane Gym.p3Exponent2))
    (NatRadix.natRadialAddress
      (Gym.oggPrimeRadixChart (Gym.formLane Gym.p3Exponent2)) 2 14)
  ≡ 5
p3Depth2Example = refl

holeCodecIsFinite :
  (form : Gym.WallForm) →
  (m : Nat) →
  Hole.ExactHoleRadixAddress form
holeCodecIsFinite form m = Hole.exactHoleRadialAddress form m

holeCodecNeedsNoRealFloor :
  Hole.holeAddressNeedsConstructiveRealFloor
    Hole.canonicalExactHoleRadixCodecBoundary
  ≡ false
holeCodecNeedsNoRealFloor = refl
