{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact where

------------------------------------------------------------------------
-- E1 SIGNED AXIS ACTION FROM THE REPOSITORY'S ACTUAL B_4 GENERATORS.
--
-- The CMP109 hypercubic machinery already owns the seven generators used by
-- the source covariance proof:
--
--   flip0 flip1 flip2 flip3 swap01 swap12 swap23.
--
-- A rank-two symmetric metric/stress component transforms by applying the
-- corresponding signed coordinate action to each index.  This file therefore
-- removes the previously abstract `e1-signed-axis-action` leaf: for exactly the
-- same generator carrier used by the CMP109 source symmetry theorem, the signed
-- tensor action is constructed definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper

axisImageOf : Hyper.HypercubicGenerator → Signed.Axis4 → Signed.Axis4
axisImageOf Hyper.flip0 axis = axis
axisImageOf Hyper.flip1 axis = axis
axisImageOf Hyper.flip2 axis = axis
axisImageOf Hyper.flip3 axis = axis
axisImageOf Hyper.swap01 Signed.axis0 = Signed.axis1
axisImageOf Hyper.swap01 Signed.axis1 = Signed.axis0
axisImageOf Hyper.swap01 Signed.axis2 = Signed.axis2
axisImageOf Hyper.swap01 Signed.axis3 = Signed.axis3
axisImageOf Hyper.swap12 Signed.axis0 = Signed.axis0
axisImageOf Hyper.swap12 Signed.axis1 = Signed.axis2
axisImageOf Hyper.swap12 Signed.axis2 = Signed.axis1
axisImageOf Hyper.swap12 Signed.axis3 = Signed.axis3
axisImageOf Hyper.swap23 Signed.axis0 = Signed.axis0
axisImageOf Hyper.swap23 Signed.axis1 = Signed.axis1
axisImageOf Hyper.swap23 Signed.axis2 = Signed.axis3
axisImageOf Hyper.swap23 Signed.axis3 = Signed.axis2

axisSignOf : Hyper.HypercubicGenerator → Signed.Axis4 → Signed.BasisSign
axisSignOf Hyper.flip0 Signed.axis0 = Signed.minus
axisSignOf Hyper.flip0 Signed.axis1 = Signed.plus
axisSignOf Hyper.flip0 Signed.axis2 = Signed.plus
axisSignOf Hyper.flip0 Signed.axis3 = Signed.plus
axisSignOf Hyper.flip1 Signed.axis0 = Signed.plus
axisSignOf Hyper.flip1 Signed.axis1 = Signed.minus
axisSignOf Hyper.flip1 Signed.axis2 = Signed.plus
axisSignOf Hyper.flip1 Signed.axis3 = Signed.plus
axisSignOf Hyper.flip2 Signed.axis0 = Signed.plus
axisSignOf Hyper.flip2 Signed.axis1 = Signed.plus
axisSignOf Hyper.flip2 Signed.axis2 = Signed.minus
axisSignOf Hyper.flip2 Signed.axis3 = Signed.plus
axisSignOf Hyper.flip3 Signed.axis0 = Signed.plus
axisSignOf Hyper.flip3 Signed.axis1 = Signed.plus
axisSignOf Hyper.flip3 Signed.axis2 = Signed.plus
axisSignOf Hyper.flip3 Signed.axis3 = Signed.minus
axisSignOf Hyper.swap01 _ = Signed.plus
axisSignOf Hyper.swap12 _ = Signed.plus
axisSignOf Hyper.swap23 _ = Signed.plus

hypercubicSignedAxisAction :
  Hyper.HypercubicGenerator → Signed.SignedAxisAction
hypercubicSignedAxisAction generator = record
  { Signed.SignedAxisAction.axisImage = axisImageOf generator
  ; Signed.SignedAxisAction.axisSign = axisSignOf generator
  }

------------------------------------------------------------------------
-- Executable sanity checks on the rank-two action.
------------------------------------------------------------------------

flip0Flips01 :
  Signed.actSignedComponent
    (hypercubicSignedAxisAction Hyper.flip0)
    K.component01
  ≡ Signed.signed-component Signed.minus K.component01
flip0Flips01 = refl

flip0Keeps00 :
  Signed.actSignedComponent
    (hypercubicSignedAxisAction Hyper.flip0)
    K.component00
  ≡ Signed.signed-component Signed.plus K.component00
flip0Keeps00 = refl

flip1Flips01 :
  Signed.actSignedComponent
    (hypercubicSignedAxisAction Hyper.flip1)
    K.component01
  ≡ Signed.signed-component Signed.minus K.component01
flip1Flips01 = refl

flip2Keeps01 :
  Signed.actSignedComponent
    (hypercubicSignedAxisAction Hyper.flip2)
    K.component01
  ≡ Signed.signed-component Signed.plus K.component01
flip2Keeps01 = refl

swap01Sends02To12 :
  Signed.actSignedComponent
    (hypercubicSignedAxisAction Hyper.swap01)
    K.component02
  ≡ Signed.signed-component Signed.plus K.component12
swap01Sends02To12 = refl

swap12Sends01To02 :
  Signed.actSignedComponent
    (hypercubicSignedAxisAction Hyper.swap12)
    K.component01
  ≡ Signed.signed-component Signed.plus K.component02
swap12Sends01To02 = refl

swap23Sends12To13 :
  Signed.actSignedComponent
    (hypercubicSignedAxisAction Hyper.swap23)
    K.component12
  ≡ Signed.signed-component Signed.plus K.component13
swap23Sends12To13 = refl

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

e1SignedAxisActionConstructedOnActualHypercubicGeneratorCarrier : Bool
e1SignedAxisActionConstructedOnActualHypercubicGeneratorCarrier = true

e1SignedAxisActionStillIndependentPhysicalLeaf : Bool
e1SignedAxisActionStillIndependentPhysicalLeaf = false

remainingE1SymmetryLeafIsCovarianceOfSourceObjectsUnderThisAction : Bool
remainingE1SymmetryLeafIsCovarianceOfSourceObjectsUnderThisAction = true
