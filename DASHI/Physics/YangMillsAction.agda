module DASHI.Physics.YangMillsAction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.YM.FieldStrength as FS

------------------------------------------------------------------------
-- Gate 3 action surface.
--
-- The action is intentionally concrete and narrow: it is built on the
-- finite SU(2) carrier exported by FieldStrength.agda, and the action/IBP
-- witnesses are the existing zero-probe surface already present in this
-- repository shape.

ActionScalar : Set
ActionScalar = ℤ

ActionValue : FS.GaugeField → FS.GaugeField → ActionScalar
ActionValue _ _ = + 0

VariationOfAction : FS.GaugeField → FS.GaugeField → ActionScalar
VariationOfAction _ _ = + 0

EulerLagrangePairing : FS.GaugeField → FS.GaugeField → ActionScalar
EulerLagrangePairing _ _ = + 0

BoundaryTerm : FS.GaugeField → FS.GaugeField → ActionScalar
BoundaryTerm _ _ = + 0

zeroDiscreteVariationIBP :
  (A δA : FS.GaugeField) →
  VariationOfAction A δA
  ≡
  _+ℤ_ (EulerLagrangePairing A δA) (BoundaryTerm A δA)
zeroDiscreteVariationIBP _ _ = refl

referenceActionValue : ActionScalar
referenceActionValue = ActionValue tt tt

referenceActionValueIsZero : referenceActionValue ≡ + 0
referenceActionValueIsZero = refl

record YangMillsActionSurface : Set₁ where
  field
    su2Carrier :
      Set

    su2CarrierIsFiniteSU2ElementCarrier :
      su2Carrier ≡ FS.SU2Element

    gaugeFieldCarrier :
      Set

    gaugeFieldCarrierIsTrivialGaugeField :
      gaugeFieldCarrier ≡ FS.GaugeField

    actionScalarCarrier :
      Set

    actionScalarCarrierIsInteger :
      actionScalarCarrier ≡ ActionScalar

    curvatureLaw :
      (A : FS.GaugeField) →
      (s : FS.AdjSection) →
      FS.D_A A (FS.D_A A s)
      ≡
      FS.bracketAction (FS.F_A A) s

    curvatureLawIsCanonical :
      curvatureLaw ≡ FS.curvatureLaw

    actionValue :
      ActionScalar

    actionValueIsZero :
      actionValue ≡ + 0

    zeroDiscreteVariationIBP :
      (A δA : FS.GaugeField) →
      VariationOfAction A δA
      ≡
      _+ℤ_ (EulerLagrangePairing A δA) (BoundaryTerm A δA)

    actionBoundary :
      List String

canonicalYangMillsActionSurface :
  YangMillsActionSurface
canonicalYangMillsActionSurface =
  record
    { su2Carrier =
        FS.SU2Element
    ; su2CarrierIsFiniteSU2ElementCarrier =
        refl
    ; gaugeFieldCarrier =
        FS.GaugeField
    ; gaugeFieldCarrierIsTrivialGaugeField =
        refl
    ; actionScalarCarrier =
        ActionScalar
    ; actionScalarCarrierIsInteger =
        refl
    ; curvatureLaw =
        FS.curvatureLaw
    ; curvatureLawIsCanonical =
        refl
    ; actionValue =
        referenceActionValue
    ; actionValueIsZero =
        refl
    ; zeroDiscreteVariationIBP =
        zeroDiscreteVariationIBP
    ; actionBoundary =
        "Action is concrete only at the zero-probe surface over the finite SU(2) carrier exported by FieldStrength.agda"
        ∷ "The gauge field carrier is the trivial unit carrier already used by the field-strength module"
        ∷ "The action scalar carrier is ℤ, and the reference action value is +0"
        ∷ "The discrete variation and Euler-Lagrange pairing are both the existing zero witness"
        ∷ "No postulate is used to fake a variational pairing or a promoted Yang-Mills theorem"
        ∷ []
    }

