module DASHI.Moonshine.OggSSP2BEquivariantWeldLastEquationCompressionExact where

------------------------------------------------------------------------
-- EQUIVARIANT-WELD COMPRESSION OF THE TERMINAL C' EQUATION
--
-- The previous terminal owner exposed one literal equation
--
--   g_actual = e^-1 . g_model . e
--
-- on the source-native Tate cokernel.  The new Lean compiler proves that this
-- equality is not an independent source/same-object acquisition: if the
-- literal Tate -> exterior/duad equivalence e is equivariant for the selected
-- centralizer element, the conjugation equality follows automatically.
--
-- A second Lean compiler shows that one representation of the selected 2B
-- centralizer on the source carrier, together with the defining commutation
-- relation with the selected involution a, automatically descends through
-- range(1+a) to the Tate quotient.  Hence separate hand-written plus/minus/
-- cokernel actions are not independent formal leaves either.
--
-- ATTRIBUTION
--   * Carnahan owns the external Monster-stable self-dual integral action.
--   * ATLAS/CTblLib/AtlasRep own the finite local/module data and outer J2^5
--     model used downstream.
--   * Mathlib owns the generic quotient-representation construction.
--   * DASHI owns only the compiler reductions from centralizer commutation and
--     equivariance to quotient action/conjugation equality.
--
-- FIREWALL
-- This file does NOT assert that the external Moonshine centralizer action has
-- already been instantiated as a formal carrier/action, nor that the literal
-- norm/exterior equivalence has already been proved equivariant.  Those are now
-- the same remaining formal source-action/equivariance seam.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggSSP2BOuterActionLastEquationExact as Old
import DASHI.Moonshine.OggSSP2BSourceActionLastLeafCompressionExact as Source

record EquivariantWeldCompressionStatus : Set where
  constructor equivariant-weld-compression-status
  field
    quotientActionFromCentralizerCommutationCompilerImplemented : Bool
    weldEquivarianceImpliesConjugationEquationCompilerImplemented : Bool
    finalCoreFromEquivariantWeldCompilerImplemented : Bool

    externalMonsterStableIntegralActionSourced : Bool
    formalSourceNativeCentralizerActionObjectInstantiated : Bool
    literalTateExteriorWeldEquivariancePaid : Bool

    independentOuterActionEquationStillNeeded : Bool
    actualStableQ10AndCompletionPaid : Bool

    remainingScientificRepresentationDiscoveryLeaves : Nat
    remainingFormalSourceActionEquivarianceLeaves : Nat
    remainingIndependentOuterActionEquations : Nat
    remainingDefectSourceBits : Nat
    nextResidual : String

canonicalEquivariantWeldCompressionStatus :
  EquivariantWeldCompressionStatus
canonicalEquivariantWeldCompressionStatus =
  equivariant-weld-compression-status
    true true true
    true false false
    false false
    0 1 0 2
    "Instantiate the sourced C_M(2B)/Co1 action once on the formal source-native norm carrier and prove the already-constructed Tate/exterior equivalence is equivariant. Quotient actions and the old terminal conjugation equation then compile automatically. After that only the two independently sourced Mode5/2T provenance bits remain before the original 2B core compiler can close."

oldEquationCountWasOne :
  Old.OuterActionLastEquationStatus.remainingOuterActionSameObjectEquations
    Old.canonicalOuterActionLastEquationStatus
  ≡ 1
oldEquationCountWasOne = Old.oneOuterSameObjectEquationRemains

representationDiscoveryAlreadyClosed :
  Source.SourceActionLastLeafCompressionStatus.remainingScientificRepresentationDiscoveryLeaves
    Source.canonicalSourceActionLastLeafCompressionStatus
  ≡ 0
representationDiscoveryAlreadyClosed =
  Source.noScientificRepresentationDiscoveryLeafRemains

noIndependentOuterEquationRemains :
  EquivariantWeldCompressionStatus.remainingIndependentOuterActionEquations
    canonicalEquivariantWeldCompressionStatus
  ≡ 0
noIndependentOuterEquationRemains = refl

oneSourceActionEquivarianceLeafRemains :
  EquivariantWeldCompressionStatus.remainingFormalSourceActionEquivarianceLeaves
    canonicalEquivariantWeldCompressionStatus
  ≡ 1
oneSourceActionEquivarianceLeafRemains = refl

formalSourceActionStillOpen :
  EquivariantWeldCompressionStatus.formalSourceNativeCentralizerActionObjectInstantiated
    canonicalEquivariantWeldCompressionStatus
  ≡ false
formalSourceActionStillOpen = refl

weldEquivarianceStillOpen :
  EquivariantWeldCompressionStatus.literalTateExteriorWeldEquivariancePaid
    canonicalEquivariantWeldCompressionStatus
  ≡ false
weldEquivarianceStillOpen = refl

defectSourceBitsRemainTwo :
  EquivariantWeldCompressionStatus.remainingDefectSourceBits
    canonicalEquivariantWeldCompressionStatus
  ≡ 2
defectSourceBitsRemainTwo = refl
