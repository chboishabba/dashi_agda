module DASHI.Core.P11EquivariantOddFieldGate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Core.OddSSP369FieldGate using
  ( fieldResidueProjection
  ; oddFieldExtractor
  )
open import DASHI.Core.SuperSSP369EquivariantOddGate as Equiv using
  ( actOnField )
open import DASHI.Core.SuperSSP369Field using
  ( SuperSSP369Field
  ; depth3Field
  ; focusParity
  ; focusPrimeLane
  ; focusResidueSurface
  ; rootField
  ; evenParity
  )
open import DASHI.Foundations.P11UnitGroupC10Witness using
  ( P11UnitClass
  ; p11UnitGenerator
  ; p11UnitHalfTurnElement
  ; p11UnitIdentity
  ; toStep
  )
open import DASHI.TrackedPrimes using (p11)

actOnP11Field :
  ∀ {d : Nat} →
  P11UnitClass →
  SuperSSP369Field d →
  SuperSSP369Field d
actOnP11Field q f = actOnField p11 (toStep q) f

record P11EquivariantOddFieldGateReceipt (d : Nat) : Set where
  constructor mkP11EquivariantOddFieldGateReceipt
  field
    quotientElement : P11UnitClass
    sourceField : SuperSSP369Field d
    transportedField : SuperSSP369Field d
    transportedFieldMatches :
      transportedField ≡ actOnP11Field quotientElement sourceField
    focusedPrimePreserved :
      focusPrimeLane transportedField ≡ focusPrimeLane sourceField
    focusedResidueSurfacePreserved :
      focusResidueSurface transportedField ≡ focusResidueSurface sourceField
    oddFieldExtractorCommutes :
      oddFieldExtractor transportedField ≡ oddFieldExtractor sourceField
    residueProjectionCommutes :
      fieldResidueProjection transportedField ≡ fieldResidueProjection sourceField

open P11EquivariantOddFieldGateReceipt public

p11EquivariantOddFieldGateReceipt :
  ∀ {d : Nat} →
  P11UnitClass →
  SuperSSP369Field d →
  P11EquivariantOddFieldGateReceipt d
p11EquivariantOddFieldGateReceipt q f =
  mkP11EquivariantOddFieldGateReceipt
    q
    f
    (actOnP11Field q f)
    refl
    refl
    refl
    refl
    refl

rootFieldIdentityOddGate :
  P11EquivariantOddFieldGateReceipt zero
rootFieldIdentityOddGate =
  p11EquivariantOddFieldGateReceipt p11UnitIdentity rootField

depth3FieldGeneratorOddGate :
  P11EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
depth3FieldGeneratorOddGate =
  p11EquivariantOddFieldGateReceipt p11UnitGenerator depth3Field

depth3FieldHalfTurnOddGate :
  P11EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
depth3FieldHalfTurnOddGate =
  p11EquivariantOddFieldGateReceipt p11UnitHalfTurnElement depth3Field

depth3FieldHalfTurnFlipsParity :
  focusParity (transportedField depth3FieldHalfTurnOddGate) ≡ evenParity
depth3FieldHalfTurnFlipsParity = refl
