module DASHI.Core.SuperSSP369EquivariantOddGate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; false; true)

open import DASHI.Core.OddSSP369FieldGate using
  ( oddFieldExtractor
  ; fieldResidueProjection
  )
open import DASHI.Core.SuperSSP369Field using
  ( SSPFieldParity
  ; SuperSSP369Field
  ; SuperSSP369Supervoxel
  ; bodyField
  ; depth3Field
  ; depth3P7Supervoxel
  ; evenParity
  ; focus
  ; focusPrimeLane
  ; focusRefinementAddress
  ; focusResidueSurface
  ; oddParity
  ; parity
  ; primeLane
  ; promoted
  ; promotedIsFalse
  ; residueField
  ; rootField
  ; rootP3Supervoxel
  ; signature
  ; symmetryMatchesPrime
  ; symmetryProfile
  ; bodySurface
  ; residueSurface
  ; refinementMatchesPrime
  ; mkSuperSSP369Field
  ; mkSuperSSP369Supervoxel
  ; refinement
  ; signatureMatchesPrime
  )
open import DASHI.Foundations.FifteenSSP369Forest using
  ( FifteenSSP369Forest )
open import DASHI.Foundations.FifteenSSPSurface using
  ( FifteenSSPSurface )
open import DASHI.Foundations.SSPPrimeLaneUnitAction as Action using
  ( UnitActionStep
  ; actOnRefinement
  ; canonicalGeneratorStep
  ; flipsPolarity
  )
open import DASHI.TrackedPrimes using (SSP; p3; p7)

flipFieldParity : SSPFieldParity → SSPFieldParity
flipFieldParity evenParity = oddParity
flipFieldParity oddParity = evenParity

actOnFieldParity : SSP → UnitActionStep → SSPFieldParity → SSPFieldParity
actOnFieldParity p step fieldParity with flipsPolarity p step
... | false = fieldParity
... | true = flipFieldParity fieldParity

actOnSupervoxel :
  ∀ {d : Nat} →
  SSP →
  UnitActionStep →
  SuperSSP369Supervoxel d →
  SuperSSP369Supervoxel d
actOnSupervoxel p step v =
  mkSuperSSP369Supervoxel
    (primeLane v)
    (signature v)
    (signatureMatchesPrime v)
    (actOnRefinement (primeLane v) step (refinement v))
    (refinementMatchesPrime v)
    (symmetryProfile v)
    (symmetryMatchesPrime v)
    (actOnFieldParity (primeLane v) step (parity v))
    (bodySurface v)
    (residueSurface v)

actOnField :
  ∀ {d : Nat} →
  SSP →
  UnitActionStep →
  SuperSSP369Field d →
  SuperSSP369Field d
actOnField p step f =
  mkSuperSSP369Field
    (bodyField f)
    (residueField f)
    (actOnSupervoxel p step (focus f))
    (promoted f)
    (promotedIsFalse f)

record SuperSSP369EquivariantOddGateReceipt (d : Nat) : Set where
  constructor mkSuperSSP369EquivariantOddGateReceipt
  field
    sourceField : SuperSSP369Field d
    primeLaneStep : SSP
    rawStep : UnitActionStep
    transportedField : SuperSSP369Field d
    transportedFieldMatches :
      transportedField ≡ actOnField primeLaneStep rawStep sourceField
    focusedPrimePreserved :
      focusPrimeLane transportedField ≡ focusPrimeLane sourceField
    focusedOddSurfacePreserved :
      focusResidueSurface transportedField ≡ focusResidueSurface sourceField
    oddFieldExtractorCommutes :
      oddFieldExtractor transportedField ≡ oddFieldExtractor sourceField
    residueProjectionCommutes :
      fieldResidueProjection transportedField ≡ fieldResidueProjection sourceField

open SuperSSP369EquivariantOddGateReceipt public

equivariantOddGateReceipt :
  ∀ {d : Nat} →
  SSP →
  UnitActionStep →
  SuperSSP369Field d →
  SuperSSP369EquivariantOddGateReceipt d
equivariantOddGateReceipt p step f =
  mkSuperSSP369EquivariantOddGateReceipt
    f
    p
    step
    (actOnField p step f)
    refl
    refl
    refl
    refl
    refl

canonicalRootFieldEquivariantOddGateReceipt :
  SuperSSP369EquivariantOddGateReceipt zero
canonicalRootFieldEquivariantOddGateReceipt =
  equivariantOddGateReceipt p3 canonicalGeneratorStep rootField

canonicalDepth3FieldEquivariantOddGateReceipt :
  SuperSSP369EquivariantOddGateReceipt (suc (suc (suc zero)))
canonicalDepth3FieldEquivariantOddGateReceipt =
  equivariantOddGateReceipt p7 canonicalGeneratorStep depth3Field

canonicalRootFieldPrimePreserved :
  focusPrimeLane
    (transportedField canonicalRootFieldEquivariantOddGateReceipt)
  ≡ focusPrimeLane rootField
canonicalRootFieldPrimePreserved =
  focusedPrimePreserved canonicalRootFieldEquivariantOddGateReceipt

canonicalDepth3FieldPrimePreserved :
  focusPrimeLane
    (transportedField canonicalDepth3FieldEquivariantOddGateReceipt)
  ≡ focusPrimeLane depth3Field
canonicalDepth3FieldPrimePreserved =
  focusedPrimePreserved canonicalDepth3FieldEquivariantOddGateReceipt

canonicalRootFieldOddExtractorCommutes :
  oddFieldExtractor
    (transportedField canonicalRootFieldEquivariantOddGateReceipt)
  ≡ oddFieldExtractor rootField
canonicalRootFieldOddExtractorCommutes =
  oddFieldExtractorCommutes canonicalRootFieldEquivariantOddGateReceipt

canonicalDepth3FieldOddExtractorCommutes :
  oddFieldExtractor
    (transportedField canonicalDepth3FieldEquivariantOddGateReceipt)
  ≡ oddFieldExtractor depth3Field
canonicalDepth3FieldOddExtractorCommutes =
  oddFieldExtractorCommutes canonicalDepth3FieldEquivariantOddGateReceipt
