module DASHI.Cognition.Teleodynamics.AlbertPriorBridgeRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Albert
import DASHI.Cognition.Teleodynamics.AlbertPriorBridgeExact as Bridge

sameTernaryOriginMapsToScalarArm :
  Albert.toAlbertShape Geometry.origin ≡ Bridge.scalarArmPoint
sameTernaryOriginMapsToScalarArm = Bridge.originMapsToPriorScalar

adapterDoesNotCreateF4Action :
  Bridge.AlbertPriorCreatesF4Action → ⊥
adapterDoesNotCreateF4Action = Bridge.albertPriorDoesNotCreateF4Action

adapterDoesNotCreateE6Action :
  Bridge.AlbertPriorCreatesE6Action → ⊥
adapterDoesNotCreateE6Action = Bridge.albertPriorDoesNotCreateE6Action

sameCarrierRoundTrips :
  (p : Geometry.Ternary27Point) →
  Albert.fromAlbertShape (Albert.toAlbertShape p) ≡ p
sameCarrierRoundTrips = Albert.fromAfterTo
