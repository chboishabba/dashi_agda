module DASHI.Analysis.CanonicalDASHIRealBackendExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Foundations.LegacyDASHIRealEquivalenceAuthorityExact as LegacyEquivalence
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Stable DASHI facade with explicit backend selection.
--
-- This module does not rewrite RealAnalysisAxioms in place.  It supplies the
-- migration object required to make that old module a facade after downstream
-- equality-sensitive consumers have been audited.
------------------------------------------------------------------------

data RealBackendKind : Set where
  bishopRegularSequenceBackend : RealBackendKind
  dashiFastCauchyBackend : RealBackendKind
  cubicalHoTTExperimentalBackend : RealBackendKind

record CanonicalRealBackendSelection : Set₁ where
  field
    selectedKind : RealBackendKind
    selectedBackend : Spine.ConstructiveRealBackend

    legacyFacadeRequired : Bool
    legacyFacadeModule : String
    legacyEquivalenceAuthority : Set

    mathematicalEqualityIsExplicit : Bool
    propositionalEqualityIdentifiedSilently : Bool
    rationalCertificateComputationRemainsSeparate : Bool
    arbitraryRealDecidableOrderAssumed : Bool

open CanonicalRealBackendSelection public

bishopFirstMigrationSelection :
  Spine.ConstructiveRealBackend → CanonicalRealBackendSelection
bishopFirstMigrationSelection backend = record
  { selectedKind = bishopRegularSequenceBackend
  ; selectedBackend = backend
  ; legacyFacadeRequired = true
  ; legacyFacadeModule = "DASHI.Foundations.RealAnalysisAxioms"
  ; legacyEquivalenceAuthority = LegacyEquivalence.LegacyRealEquivalenceAuthority
  ; mathematicalEqualityIsExplicit = true
  ; propositionalEqualityIdentifiedSilently = false
  ; rationalCertificateComputationRemainsSeparate = true
  ; arbitraryRealDecidableOrderAssumed = false
  }

record RealEqualityAudit : Set₁ where
  field
    definitionalEqualitiesReviewed : Set
    mathematicalRealEqualitiesMovedToSetoid : Set
    realFunctionEqualitiesMadePointwise : Set
    rationalConfigurationEqualitiesRetained : Set
    solverCallsClassifiedByCarrier : Set
    inverseCallsCarryApartness : Set

open RealEqualityAudit public

record LegacyFacadeMigration
    (selection : CanonicalRealBackendSelection) : Set₁ where
  field
    equalityAudit : RealEqualityAudit
    elementaryFunctionConsumersMigrated : Set
    quaternionConsumersMigrated : Set
    hessianGreenConsumersMigrated : Set
    measureConsumersMigrated : Set
    oldPostulateSurfaceNoLongerCanonical : Set
    facadePreservesLegacyModulePath : Set

open LegacyFacadeMigration public

canonicalBackendSelectionDefinitionLevel : ProofLevel
canonicalBackendSelectionDefinitionLevel = machineChecked

legacyFacadeMigrationInputsLevel : ProofLevel
legacyFacadeMigrationInputsLevel = conditional
