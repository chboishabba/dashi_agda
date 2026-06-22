module DASHI.Core.P13EquivariantOddFieldGate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Core.OddSSP369FieldGate using
  ( fieldResidueProjection
  ; oddFieldExtractor
  )
open import DASHI.Core.SuperSSP369EquivariantOddGate as Equiv using
  ( actOnField
  )
open import DASHI.Core.SuperSSP369Field using
  ( SuperSSP369Field
  ; depth3Field
  ; evenParity
  ; focusParity
  ; focusPrimeLane
  ; focusResidueSurface
  ; oddParity
  ; rootField
  )
open import DASHI.Foundations.P13UnitGroupC12Witness using
  ( P13UnitClass
  ; p13UnitGenerator
  ; p13UnitHalfTurnElement
  ; p13UnitIdentity
  ; toStep
  )
open import DASHI.TrackedPrimes using (p13)

actOnP13Field :
  ∀ {d : Nat} →
  P13UnitClass →
  SuperSSP369Field d →
  SuperSSP369Field d
actOnP13Field q f = actOnField p13 (toStep q) f

record P13EquivariantOddFieldGateReceipt (d : Nat) : Set where
  constructor mkP13EquivariantOddFieldGateReceipt
  field
    quotientElement : P13UnitClass
    sourceField : SuperSSP369Field d
    transportedField : SuperSSP369Field d
    transportedFieldMatches :
      transportedField ≡ actOnP13Field quotientElement sourceField
    focusedPrimePreserved :
      focusPrimeLane transportedField ≡ focusPrimeLane sourceField
    focusedResidueSurfacePreserved :
      focusResidueSurface transportedField ≡ focusResidueSurface sourceField
    oddFieldExtractorCommutes :
      oddFieldExtractor transportedField ≡ oddFieldExtractor sourceField
    residueProjectionCommutes :
      fieldResidueProjection transportedField ≡ fieldResidueProjection sourceField

open P13EquivariantOddFieldGateReceipt public

p13EquivariantOddFieldGateReceipt :
  ∀ {d : Nat} →
  P13UnitClass →
  SuperSSP369Field d →
  P13EquivariantOddFieldGateReceipt d
p13EquivariantOddFieldGateReceipt q f =
  mkP13EquivariantOddFieldGateReceipt
    q
    f
    (actOnP13Field q f)
    refl
    refl
    refl
    refl
    refl

rootFieldIdentityOddGate :
  P13EquivariantOddFieldGateReceipt zero
rootFieldIdentityOddGate =
  p13EquivariantOddFieldGateReceipt p13UnitIdentity rootField

depth3FieldGeneratorOddGate :
  P13EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
depth3FieldGeneratorOddGate =
  p13EquivariantOddFieldGateReceipt p13UnitGenerator depth3Field

depth3FieldSixthOddGate :
  P13EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
depth3FieldSixthOddGate =
  p13EquivariantOddFieldGateReceipt p13UnitHalfTurnElement depth3Field

rootFieldIdentityPreservesParity :
  focusParity (transportedField rootFieldIdentityOddGate) ≡ evenParity
rootFieldIdentityPreservesParity = refl

depth3FieldGeneratorFlipsParity :
  focusParity (transportedField depth3FieldGeneratorOddGate) ≡ evenParity
depth3FieldGeneratorFlipsParity = refl

depth3FieldSixthPreservesParity :
  focusParity (transportedField depth3FieldSixthOddGate) ≡ oddParity
depth3FieldSixthPreservesParity = refl

depth3FieldGeneratorOddExtractorCommutes :
  oddFieldExtractor (transportedField depth3FieldGeneratorOddGate)
  ≡ oddFieldExtractor depth3Field
depth3FieldGeneratorOddExtractorCommutes =
  oddFieldExtractorCommutes depth3FieldGeneratorOddGate

depth3FieldSixthOddExtractorCommutes :
  oddFieldExtractor (transportedField depth3FieldSixthOddGate)
  ≡ oddFieldExtractor depth3Field
depth3FieldSixthOddExtractorCommutes =
  oddFieldExtractorCommutes depth3FieldSixthOddGate
