module DASHI.Physics.Plasma.MHDElsasserTangentRechartExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Plasma.MHDHelicalElsasserTriadTangentExact as Pair

------------------------------------------------------------------------
-- TANGENT RECHART
--
-- If T_u and T_b are the same-object momentum/induction tangents, then the
-- Elsasser tangents are merely the linear rechart
--
--   T_+ = T_u + T_b
--   T_- = T_u - T_b.
--
-- This does not manufacture a new dynamical law; it is the tangent map of the
-- existing Elsasser coordinate change.
------------------------------------------------------------------------

private
  sub : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

plusTangent : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
plusTangent {F = F} tu tb = C3.add F tu tb

minusTangent : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
minusTangent tu tb = sub tu tb

record ElsasserPairedTangent {r : _} (F : C3.RealField r) : Set r where
  constructor elsasser-paired-tangent
  field
    velocityTangent : C3.Carrier F
    magneticTangent : C3.Carrier F
    plusDirection : C3.Carrier F
    minusDirection : C3.Carrier F
    plusDirectionWeld : plusDirection ≡ plusTangent velocityTangent magneticTangent
    minusDirectionWeld : minusDirection ≡ minusTangent velocityTangent magneticTangent
    sameObjectVelocityMagneticTangentReceipt : Set

open ElsasserPairedTangent public

rechartPairedTriadTangent :
  ∀ {r} {F : C3.RealField r}
    (coefficients : Pair.PairedTriadCoefficient F)
    (up bp uq bq : C3.Carrier F) →
  ElsasserPairedTangent F
rechartPairedTriadTangent {F = F} coefficients up bp uq bq =
  elsasser-paired-tangent
    tu tb
    (plusTangent tu tb)
    (minusTangent tu tb)
    refl refl
    ⊤
  where
    tu = Pair.momentumTangent coefficients up bp uq bq
    tb = Pair.inductionTangent coefficients up bp uq bq

record ElsasserTangentBoundary : Set where
  constructor elsasser-tangent-boundary
  field
    tangentRechartCreatesIndependentPhysics : Bool
    tangentRechartCreatesIndependentPhysicsIsFalse :
      tangentRechartCreatesIndependentPhysics ≡ false

    plusMinusDirectionsNeedSameObjectVelocityMagneticTangent : Bool
    plusMinusDirectionsNeedSameObjectVelocityMagneticTangentIsTrue :
      plusMinusDirectionsNeedSameObjectVelocityMagneticTangent ≡ true

canonicalElsasserTangentBoundary : ElsasserTangentBoundary
canonicalElsasserTangentBoundary =
  elsasser-tangent-boundary false refl true refl
