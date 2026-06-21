module DASHI.Core.OddSSP369FieldGate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)

open import DASHI.Core.SuperSSP369Field using
  ( SuperSSP369Field
  ; rootField
  ; depth3Field
  ; bodyField
  ; residueField
  )
open import DASHI.Foundations.FifteenSSP369Forest using
  ( FifteenSSP369Forest
  )
open import DASHI.Foundations.FifteenSSPSurface using
  ( FifteenSSPSurface
  )

------------------------------------------------------------------------
-- Typed field-level odd SSP gate.
--
-- The body and residue field split is explicit, and the odd extractor
-- returns the residue field.

fieldBodyProjection :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  FifteenSSP369Forest FifteenSSPSurface
fieldBodyProjection =
  bodyField

fieldResidueProjection :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  FifteenSSP369Forest FifteenSSPSurface
fieldResidueProjection =
  residueField

oddFieldExtractor :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  FifteenSSP369Forest FifteenSSPSurface
oddFieldExtractor =
  residueField

oddFieldDerivative :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  FifteenSSP369Forest FifteenSSPSurface
oddFieldDerivative =
  residueField

berezinIntegral :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  FifteenSSP369Forest FifteenSSPSurface
berezinIntegral =
  residueField

record OddSSP369FieldGateReceipt (d : Nat) : Set where
  constructor mkOddSSP369FieldGateReceipt
  field
    sourceField :
      SuperSSP369Field d

    bodyProjection :
      FifteenSSP369Forest FifteenSSPSurface

    oddProjection :
      FifteenSSP369Forest FifteenSSPSurface

    bodyProjectionMatches :
      bodyProjection ≡ fieldBodyProjection sourceField

    oddProjectionMatches :
      oddProjection ≡ fieldResidueProjection sourceField

    extractorMatchesOddProjection :
      oddFieldExtractor sourceField ≡ oddProjection

    derivativeMatchesOddProjection :
      oddFieldDerivative sourceField ≡ oddProjection

    integralMatchesOddProjection :
      berezinIntegral sourceField ≡ oddProjection

open OddSSP369FieldGateReceipt public

canonicalOddSSP369FieldGateReceipt :
  OddSSP369FieldGateReceipt zero
canonicalOddSSP369FieldGateReceipt =
  mkOddSSP369FieldGateReceipt
    rootField
    (fieldBodyProjection rootField)
    (fieldResidueProjection rootField)
    refl
    refl
    refl
    refl
    refl

rootFieldOddProjection :
  oddFieldExtractor rootField ≡ fieldResidueProjection rootField
rootFieldOddProjection =
  refl

depth3FieldOddProjection :
  oddFieldExtractor depth3Field ≡ fieldResidueProjection depth3Field
depth3FieldOddProjection =
  refl

oddFieldDerivativeCollapsesToOddFieldExtractor :
  oddFieldDerivative rootField ≡ oddFieldExtractor rootField
oddFieldDerivativeCollapsesToOddFieldExtractor =
  refl

berezinIntegralCollapsesToOddFieldExtractor :
  berezinIntegral rootField ≡ oddFieldExtractor rootField
berezinIntegralCollapsesToOddFieldExtractor =
  refl

oddFieldDerivativeCollapsesToBerezinIntegral :
  oddFieldDerivative rootField ≡ berezinIntegral rootField
oddFieldDerivativeCollapsesToBerezinIntegral =
  refl
