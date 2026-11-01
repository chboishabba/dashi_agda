module DASHI.Cognition.ExistingFibreRefinementAdapters where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Biology.ObserverPerceptualManifoldResidual as Observer
import DASHI.Core.SuperSSP369Field as Super
import DASHI.Physics.ShiftWaveRefinementSeam as ShiftWave
import DASHI.Reasoning.CarryMemorySubvoxelReceipt as Carry

------------------------------------------------------------------------
-- Explicit adapters to existing repository formalisms.  These records prevent
-- the new reflexive/clopen layer from silently replacing its source carriers.
------------------------------------------------------------------------

record SupervoxelRefinementAdapter (depth : Nat) : Set₁ where
  field
    sourceSupervoxel : Super.SuperSSP369Supervoxel depth
    coarseConstraintRecord : Set
    fineCompletionRecord : Set
    coarseRecordExtractedFromFine : fineCompletionRecord → coarseConstraintRecord
    sourceAddressRetained : Set

open SupervoxelRefinementAdapter public

record CarryMemoryPsychologyAdapter : Setω where
  field
    sourceReceipt : Carry.CarryMemorySubvoxelReceipt
    HiddenMemoryState : Set
    embedCarryMemory :
      Carry.SubvoxelMemoryStatus →
      HiddenMemoryState
    runtimeCarryAuthoritySupplied : Bool
    empiricalPsychologyAuthoritySupplied : Bool
    runtimeCarryAuthoritySuppliedIsFalse :
      runtimeCarryAuthoritySupplied ≡ false
    empiricalPsychologyAuthoritySuppliedIsFalse :
      empiricalPsychologyAuthoritySupplied ≡ false

open CarryMemoryPsychologyAdapter public

record ObserverManifoldPsychologyAdapter : Set₁ where
  field
    sourceManifold : Observer.SharedLatentTransportManifold
    HiddenPsychologicalState : Set
    projectLatentState :
      Observer.LatentState sourceManifold →
      HiddenPsychologicalState
    phenomenalIdentityPromoted : Bool
    phenomenalIdentityPromotedIsFalse :
      phenomenalIdentityPromoted ≡ false

open ObserverManifoldPsychologyAdapter public

record ShiftWavePresentationAdapter : Set₁ where
  field
    coarseSurface : Set
    fineSurface : Set
    projectFineToCoarse : fineSurface → coarseSurface

    projectionAgreement : Set
    projectionAgreementWitness : projectionAgreement

    phaseAndWaveRetainedAtFineSurface : Set
    phaseAndWaveRetainedAtFineSurfaceWitness :
      phaseAndWaveRetainedAtFineSurface

open ShiftWavePresentationAdapter public

canonicalShiftWavePresentationAdapter : ShiftWavePresentationAdapter
canonicalShiftWavePresentationAdapter =
  record
    { coarseSurface = ShiftWave.CoarseObservation
    ; fineSurface = ShiftWave.FineObservation
    ; projectFineToCoarse = ShiftWave.projectFine
    ; projectionAgreement = ShiftWave.projectFineAgreement
    ; projectionAgreementWitness = ShiftWave.projectFineAgreement-witness
    ; phaseAndWaveRetainedAtFineSurface = ShiftWave.waveShadowAgreement
    ; phaseAndWaveRetainedAtFineSurfaceWitness =
        ShiftWave.waveShadowAgreement-witness
    }

record ExistingAdapterBoundary : Set where
  constructor existingAdapterBoundary
  field
    sourceCarriersReused : Bool
    clinicalAuthorityImportedFromAdapters : Bool
    clinicalAuthorityImportedFromAdaptersIsFalse :
      clinicalAuthorityImportedFromAdapters ≡ false

canonicalExistingAdapterBoundary : ExistingAdapterBoundary
canonicalExistingAdapterBoundary =
  existingAdapterBoundary true false refl
