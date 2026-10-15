module DASHI.Biology.AtomicLineageTargetRecognitionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.AtomicMolecularReactionLineageHyperfabricExact as Lineage
import DASHI.Biology.TargetRelativeRecognitionFibreExact as Recognition

------------------------------------------------------------------------
-- ATOMIC/MOLECULAR LINEAGE -> TARGET-RELATIVE RECOGNITION
--
-- This is the generic substitution probe.  It does not invent a new mimicry or
-- counterfactual ontology: it attaches the repo's persistent fine lineage to
-- the existing target-relative recognition fibre.
------------------------------------------------------------------------

record AtomicSubstitutionProbe : Set where
  constructor atomicSubstitutionProbe
  field
    nativeLineage : Lineage.AtomicLineage
    candidateLineage : Lineage.AtomicLineage
    recognitionFibre : Recognition.TargetRelativeRecognitionFibre
    fineIdentityReference : String
    overlappingRecognitionReference : String
    separatingRecognitionReference : String
    downstreamConsumerReference : String
    refinementReference : String
    fineAtomicIdentitySeparated : Bool
    fineAtomicIdentitySeparatedIsTrue : fineAtomicIdentitySeparated ≡ true
    targetOverlapMayPermitSubstitution : Bool
    targetOverlapMayPermitSubstitutionIsTrue :
      targetOverlapMayPermitSubstitution ≡ true
    substitutionImpliesChemicalIdentity : Bool
    substitutionImpliesChemicalIdentityIsFalse :
      substitutionImpliesChemicalIdentity ≡ false
    substitutionImpliesSameDownstreamFunction : Bool
    substitutionImpliesSameDownstreamFunctionIsFalse :
      substitutionImpliesSameDownstreamFunction ≡ false

open AtomicSubstitutionProbe public

record MolecularSubstitutionProbe : Set where
  constructor molecularSubstitutionProbe
  field
    nativeMolecule : Lineage.MolecularLineageState
    candidateMolecule : Lineage.MolecularLineageState
    recognitionFibre : Recognition.TargetRelativeRecognitionFibre
    molecularFineStateReference : String
    observerCollisionReference : String
    separatingCoordinateReference : String
    downstreamReauditReference : String
    targetOverlapImpliesWholeMoleculeIdentity : Bool
    targetOverlapImpliesWholeMoleculeIdentityIsFalse :
      targetOverlapImpliesWholeMoleculeIdentity ≡ false

open MolecularSubstitutionProbe public

record AtomicLineageTargetRecognitionBoundary : Set where
  constructor atomicLineageTargetRecognitionBoundary
  field
    fineLineageMayRefineTargetRecognition : Bool
    fineLineageMayRefineTargetRecognitionIsTrue :
      fineLineageMayRefineTargetRecognition ≡ true
    targetRecognitionMayIgnoreSomeFineCoordinates : Bool
    targetRecognitionMayIgnoreSomeFineCoordinatesIsTrue :
      targetRecognitionMayIgnoreSomeFineCoordinates ≡ true
    targetRelativeOverlapEqualsFineIdentity : Bool
    targetRelativeOverlapEqualsFineIdentityIsFalse :
      targetRelativeOverlapEqualsFineIdentity ≡ false
    newSeparatingCoordinateReopensDownstreamConsumers : Bool
    newSeparatingCoordinateReopensDownstreamConsumersIsTrue :
      newSeparatingCoordinateReopensDownstreamConsumers ≡ true

open AtomicLineageTargetRecognitionBoundary public

canonicalAtomicLineageTargetRecognitionBoundary :
  AtomicLineageTargetRecognitionBoundary
canonicalAtomicLineageTargetRecognitionBoundary =
  atomicLineageTargetRecognitionBoundary true refl true refl false refl true refl
