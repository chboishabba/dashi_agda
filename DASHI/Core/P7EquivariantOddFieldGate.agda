module DASHI.Core.P7EquivariantOddFieldGate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Core.OddSSP369FieldGate using
  ( fieldResidueProjection
  ; oddFieldExtractor
  )
open import DASHI.Core.SuperSSP369EquivariantOddGate as Equiv using
  ( actOnField
  ; actOnFieldParity
  ; actOnSupervoxel
  )
open import DASHI.Core.SuperSSP369Field using
  ( SSPFieldParity
  ; SuperSSP369Field
  ; depth3Field
  ; depth3P7Supervoxel
  ; evenParity
  ; focus
  ; focusParity
  ; focusPrimeLane
  ; focusResidueSurface
  ; oddParity
  ; rootField
  )
open import DASHI.Foundations.P7HexTruthActionQuotient using ()
open import DASHI.Foundations.P7UnitGroupC6Witness using ()
open import DASHI.Foundations.SSPPrimeLaneUnitGroup using
  ( P7UnitClass
  ; p7UnitGenerator
  ; p7UnitIdentity
  ; p7UnitMobiusElement
  ; toStep
  )
open import DASHI.TrackedPrimes using (p7)

actOnP7Field :
  ∀ {d : Nat} →
  P7UnitClass →
  SuperSSP369Field d →
  SuperSSP369Field d
actOnP7Field q f = actOnField p7 (toStep q) f

record P7EquivariantOddFieldGateReceipt (d : Nat) : Set where
  constructor mkP7EquivariantOddFieldGateReceipt
  field
    quotientElement : P7UnitClass
    sourceField : SuperSSP369Field d
    transportedField : SuperSSP369Field d
    transportedFieldMatches :
      transportedField ≡ actOnP7Field quotientElement sourceField
    focusedPrimePreserved :
      focusPrimeLane transportedField ≡ focusPrimeLane sourceField
    focusedResidueSurfacePreserved :
      focusResidueSurface transportedField ≡ focusResidueSurface sourceField
    oddFieldExtractorCommutes :
      oddFieldExtractor transportedField ≡ oddFieldExtractor sourceField
    residueProjectionCommutes :
      fieldResidueProjection transportedField ≡ fieldResidueProjection sourceField

open P7EquivariantOddFieldGateReceipt public

p7EquivariantOddFieldGateReceipt :
  ∀ {d : Nat} →
  P7UnitClass →
  SuperSSP369Field d →
  P7EquivariantOddFieldGateReceipt d
p7EquivariantOddFieldGateReceipt q f =
  mkP7EquivariantOddFieldGateReceipt
    q
    f
    (actOnP7Field q f)
    refl
    refl
    refl
    refl
    refl

rootFieldIdentityOddGate :
  P7EquivariantOddFieldGateReceipt zero
rootFieldIdentityOddGate =
  p7EquivariantOddFieldGateReceipt p7UnitIdentity rootField

depth3FieldGeneratorOddGate :
  P7EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
depth3FieldGeneratorOddGate =
  p7EquivariantOddFieldGateReceipt p7UnitGenerator depth3Field

depth3FieldMobiusOddGate :
  P7EquivariantOddFieldGateReceipt (suc (suc (suc zero)))
depth3FieldMobiusOddGate =
  p7EquivariantOddFieldGateReceipt p7UnitMobiusElement depth3Field

rootFieldIdentityPreservesParity :
  focusParity (transportedField rootFieldIdentityOddGate) ≡ evenParity
rootFieldIdentityPreservesParity = refl

depth3FieldGeneratorFlipsParity :
  focusParity (transportedField depth3FieldGeneratorOddGate) ≡ evenParity
depth3FieldGeneratorFlipsParity = refl

depth3FieldMobiusFlipsParity :
  focusParity (transportedField depth3FieldMobiusOddGate) ≡ evenParity
depth3FieldMobiusFlipsParity = refl

depth3FieldMobiusOddExtractorCommutes :
  oddFieldExtractor (transportedField depth3FieldMobiusOddGate)
  ≡ oddFieldExtractor depth3Field
depth3FieldMobiusOddExtractorCommutes =
  oddFieldExtractorCommutes depth3FieldMobiusOddGate
