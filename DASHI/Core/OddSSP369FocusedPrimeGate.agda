module DASHI.Core.OddSSP369FocusedPrimeGate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import MonsterOntos using (SSP)

open import DASHI.Core.OddSSP369FieldGate using
  ( fieldResidueProjection
  ; oddFieldExtractor
  )
open import DASHI.Core.SuperSSP369Field using
  ( SuperSSP369Field
  ; SuperSSP369Supervoxel
  ; depth3Field
  ; depth3P7Supervoxel
  ; focus
  ; focusPrimeLane
  ; focusRefinementAddress
  ; focusResidueSurface
  ; rootField
  ; rootP3Supervoxel
  )
open import DASHI.Foundations.SSPPrimeLane369Refinement using
  ( Lane369Address
  )
open import DASHI.Foundations.FifteenSSP369Forest using
  ( FifteenSSP369Forest
  )
open import DASHI.Foundations.FifteenSSPSurface using
  ( FifteenSSPSurface
  )

------------------------------------------------------------------------
-- Focused prime gate over the 369 field carrier.
--
-- This module exposes the focused prime lane, focused depth address, and
-- focused odd residue extraction surface while keeping the canonical field
-- focus and supervoxel witnesses visible in the receipts.

focusedPrimeLane :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  SSP
focusedPrimeLane =
  focusPrimeLane

focusedDepthAddress :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  Lane369Address d
focusedDepthAddress =
  focusRefinementAddress

focusedOddResidueExtractionSurface :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  FifteenSSPSurface
focusedOddResidueExtractionSurface =
  focusResidueSurface

focusedOddResidueProjection :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  FifteenSSP369Forest FifteenSSPSurface
focusedOddResidueProjection =
  fieldResidueProjection

record OddSSP369FocusedPrimeGateReceipt (d : Nat) : Set where
  constructor mkOddSSP369FocusedPrimeGateReceipt
  field
    sourceField :
      SuperSSP369Field d

    sourceSupervoxel :
      SuperSSP369Supervoxel d

    primeLaneValue :
      SSP

    depthAddressValue :
      Lane369Address d

    oddResidueExtractionSurfaceValue :
      FifteenSSPSurface

    oddResidueSurfaceValue :
      FifteenSSP369Forest FifteenSSPSurface

    sourceFocusMatchesSupervoxel :
      focus sourceField ≡ sourceSupervoxel

    primeLaneValueMatchesFieldFocus :
      primeLaneValue ≡ focusPrimeLane sourceField

    depthAddressValueMatchesFieldFocus :
      depthAddressValue ≡ focusRefinementAddress sourceField

    oddResidueExtractionSurfaceValueMatchesFieldFocus :
      oddResidueExtractionSurfaceValue ≡ focusResidueSurface sourceField

    oddResidueSurfaceValueMatchesFieldFocus :
      oddResidueSurfaceValue ≡ fieldResidueProjection sourceField

    oddFieldExtractorMatchesOddResidueSurfaceValue :
      oddFieldExtractor sourceField ≡ oddResidueSurfaceValue

open OddSSP369FocusedPrimeGateReceipt public

rootFieldFocusedPrimeGateReceipt :
  OddSSP369FocusedPrimeGateReceipt zero
rootFieldFocusedPrimeGateReceipt =
  mkOddSSP369FocusedPrimeGateReceipt
    rootField
    rootP3Supervoxel
    (focusedPrimeLane rootField)
    (focusedDepthAddress rootField)
    (focusedOddResidueExtractionSurface rootField)
    (focusedOddResidueProjection rootField)
    refl
    refl
    refl
    refl
    refl
    refl

depth3FieldFocusedPrimeGateReceipt :
  OddSSP369FocusedPrimeGateReceipt (suc (suc (suc zero)))
depth3FieldFocusedPrimeGateReceipt =
  mkOddSSP369FocusedPrimeGateReceipt
    depth3Field
    depth3P7Supervoxel
    (focusedPrimeLane depth3Field)
    (focusedDepthAddress depth3Field)
    (focusedOddResidueExtractionSurface depth3Field)
    (focusedOddResidueProjection depth3Field)
    refl
    refl
    refl
    refl
    refl
    refl

rootFieldFocusedPrimeLaneMatchesFocus :
  primeLaneValue rootFieldFocusedPrimeGateReceipt ≡ focusPrimeLane rootField
rootFieldFocusedPrimeLaneMatchesFocus = refl

rootFieldFocusedOddResidueMatchesFocus :
  oddResidueSurfaceValue rootFieldFocusedPrimeGateReceipt
  ≡
  fieldResidueProjection rootField
rootFieldFocusedOddResidueMatchesFocus = refl

rootFieldFocusedOddResidueExtractionSurfaceMatchesFocus :
  oddResidueExtractionSurfaceValue rootFieldFocusedPrimeGateReceipt
  ≡
  focusResidueSurface rootField
rootFieldFocusedOddResidueExtractionSurfaceMatchesFocus = refl

depth3FieldFocusedPrimeLaneMatchesFocus :
  primeLaneValue depth3FieldFocusedPrimeGateReceipt ≡
  focusPrimeLane depth3Field
depth3FieldFocusedPrimeLaneMatchesFocus = refl

depth3FieldFocusedOddResidueMatchesFocus :
  oddResidueSurfaceValue depth3FieldFocusedPrimeGateReceipt
  ≡
  fieldResidueProjection depth3Field
depth3FieldFocusedOddResidueMatchesFocus = refl

depth3FieldFocusedOddResidueExtractionSurfaceMatchesFocus :
  oddResidueExtractionSurfaceValue depth3FieldFocusedPrimeGateReceipt
  ≡
  focusResidueSurface depth3Field
depth3FieldFocusedOddResidueExtractionSurfaceMatchesFocus = refl
