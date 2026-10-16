module DASHI.Physics.Chemistry.AtomicPeriodicTable369ExteriorHodgeC3IntertwinerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as C3
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ExteriorC3RepresentationExact as Exterior

------------------------------------------------------------------------
-- Finite three-dimensional Hodge-style intertwiner.
--
-- Sibling PR #1164 proves the continuous R3 identity *(u wedge v)=u cross v.
-- This file does NOT import that sibling as theorem authority.  It pays the
-- corresponding finite basis theorem directly on the atomic p-shell charge
-- carrier: wedge^2 of the oriented three-state representation is equivalent
-- to the one-particle representation, including the exchange signs.
------------------------------------------------------------------------

record SignedMagneticState : Set where
  constructor signedMagneticState
  field
    magneticSign : Exterior.WedgeSign
    magneticState : C3.MagneticState

open SignedMagneticState public

negateMagnetic : SignedMagneticState -> SignedMagneticState
negateMagnetic (signedMagneticState s m) =
  signedMagneticState (Exterior.flipSign s) m

signedChargePositiveStep : SignedMagneticState -> SignedMagneticState
signedChargePositiveStep (signedMagneticState s m) =
  signedMagneticState s (C3.chargePositiveStep m)

-- Oriented Hodge chart:
--   e_- ^ e_0  ->  e_+
--   e_- ^ e_+  -> -e_0
--   e_0 ^ e_+  ->  e_-
-- which is the usual three-dimensional oriented complement pattern.
hodgeWedge2 : Exterior.SignedWedge2 -> SignedMagneticState
hodgeWedge2 (Exterior.signedWedge2 s Exterior.wedgeNegZero) =
  signedMagneticState s C3.mPosOne
hodgeWedge2 (Exterior.signedWedge2 s Exterior.wedgeNegPos) =
  signedMagneticState (Exterior.flipSign s) C3.mZero
hodgeWedge2 (Exterior.signedWedge2 s Exterior.wedgeZeroPos) =
  signedMagneticState s C3.mNegOne

hodgeRespectsNegation :
  (x : Exterior.SignedWedge2) ->
  hodgeWedge2 (Exterior.negateWedge2 x)
  ≡ negateMagnetic (hodgeWedge2 x)
hodgeRespectsNegation (Exterior.signedWedge2 Exterior.positiveWedge Exterior.wedgeNegZero) = refl
hodgeRespectsNegation (Exterior.signedWedge2 Exterior.negativeWedge Exterior.wedgeNegZero) = refl
hodgeRespectsNegation (Exterior.signedWedge2 Exterior.positiveWedge Exterior.wedgeNegPos) = refl
hodgeRespectsNegation (Exterior.signedWedge2 Exterior.negativeWedge Exterior.wedgeNegPos) = refl
hodgeRespectsNegation (Exterior.signedWedge2 Exterior.positiveWedge Exterior.wedgeZeroPos) = refl
hodgeRespectsNegation (Exterior.signedWedge2 Exterior.negativeWedge Exterior.wedgeZeroPos) = refl

-- Exact commuting square H o wedge^2(U) = U o H.
hodgeIntertwinesC3 :
  (x : Exterior.SignedWedge2) ->
  hodgeWedge2 (Exterior.wedge2PositiveStep x)
  ≡ signedChargePositiveStep (hodgeWedge2 x)
hodgeIntertwinesC3 (Exterior.signedWedge2 Exterior.positiveWedge Exterior.wedgeNegZero) = refl
hodgeIntertwinesC3 (Exterior.signedWedge2 Exterior.negativeWedge Exterior.wedgeNegZero) = refl
hodgeIntertwinesC3 (Exterior.signedWedge2 Exterior.positiveWedge Exterior.wedgeNegPos) = refl
hodgeIntertwinesC3 (Exterior.signedWedge2 Exterior.negativeWedge Exterior.wedgeNegPos) = refl
hodgeIntertwinesC3 (Exterior.signedWedge2 Exterior.positiveWedge Exterior.wedgeZeroPos) = refl
hodgeIntertwinesC3 (Exterior.signedWedge2 Exterior.negativeWedge Exterior.wedgeZeroPos) = refl

record ExteriorHodgeC3Boundary : Set where
  constructor exteriorHodgeC3Boundary
  field
    finiteOrientedComplementMapPaid : Bool
    exchangeSignsPreserved : Bool
    wedge2ToOneParticleC3IntertwinerPaid : Bool
    sibling1164ContinuousHodgeUsedAsTheoremAuthority : Bool
    finiteHodgeIntertwinerIsContinuumWavefunctionIdentity : Bool
    fullSO3ExteriorRepresentationPaid : Bool

open ExteriorHodgeC3Boundary public

canonicalExteriorHodgeC3Boundary : ExteriorHodgeC3Boundary
canonicalExteriorHodgeC3Boundary =
  exteriorHodgeC3Boundary true true true false false false

sibling1164NotImportedAsAuthority :
  sibling1164ContinuousHodgeUsedAsTheoremAuthority canonicalExteriorHodgeC3Boundary
  ≡ false
sibling1164NotImportedAsAuthority = refl
