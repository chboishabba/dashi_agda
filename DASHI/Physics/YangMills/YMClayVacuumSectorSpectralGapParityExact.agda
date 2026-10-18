{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayVacuumSectorSpectralGapParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact as Atlas

------------------------------------------------------------------------
-- Exact Agda parity surface for the verified Lean donor theorem
-- RequestProject/YangMills/VacuumSectorSpectralGap.lean.
--
-- Important authority boundary:
--   the theorem is paid by the supplied Lean worker receipt;
--   this file records its exact input/output type shape for Agda consumers;
--   it does NOT claim that the analytic proof has been re-kernelled by Agda.
------------------------------------------------------------------------

record VacuumGapDatum
    (Hamiltonian Vacuum Gap : Set) : Set₁ where
  field
    op : Hamiltonian
    vacuum : Vacuum
    gap : Gap

    SelfAdjoint : Set
    selfAdjoint : SelfAdjoint

    VacuumInDomain : Set
    vacuumInDomain : VacuumInDomain

    VacuumUnit : Set
    vacuumUnit : VacuumUnit

    VacuumGround : Set
    vacuumGround : VacuumGround

    GapPositive : Set
    gapPositive : GapPositive

    VacuumFormGap : Set
    vacuumFormGap : VacuumFormGap

open VacuumGapDatum public

record VacuumSectorSpectralConsequences
    {Hamiltonian Vacuum Gap : Set}
    (datum : VacuumGapDatum Hamiltonian Vacuum Gap) : Set₁ where
  field
    NoEigenvalueBelowGap : Set
    noEigenvalueBelowGap : NoEigenvalueBelowGap

    UniqueVacuumSectorSolvability : Set
    uniqueVacuumSectorSolvability : UniqueVacuumSectorSolvability

    QuantitativeResolventBound : Set
    quantitativeResolventBound : QuantitativeResolventBound

open VacuumSectorSpectralConsequences public

record VacuumSectorLeanArtifactBundle : Set where
  field
    uniqueSolutionArtifact : Atlas.LeanTheoremArtifact
    resolventBoundArtifact : Atlas.LeanTheoremArtifact
    eigenvalueExclusionArtifact : Atlas.LeanTheoremArtifact

open VacuumSectorLeanArtifactBundle public

canonicalVacuumSectorLeanArtifacts : VacuumSectorLeanArtifactBundle
canonicalVacuumSectorLeanArtifacts = record
  { uniqueSolutionArtifact = Atlas.vacuumSectorUniqueSolutionLean
  ; resolventBoundArtifact = Atlas.vacuumSectorResolventBoundLean
  ; eigenvalueExclusionArtifact = Atlas.vacuumSectorEigenvalueExclusionLean
  }

-- Cross-prover theorem receipt: exact theorem authority is retained separately
-- from the Agda proposition carrier.
record VacuumSectorLeanTheoremReceipt
    {Hamiltonian Vacuum Gap : Set}
    (datum : VacuumGapDatum Hamiltonian Vacuum Gap) : Set₁ where
  field
    artifacts : VacuumSectorLeanArtifactBundle
    consequences : VacuumSectorSpectralConsequences datum

    exactLeanSourceMatchesDatumShape : Bool
    exactLeanSourceMatchesDatumShapeIsTrue : exactLeanSourceMatchesDatumShape ≡ true

open VacuumSectorLeanTheoremReceipt public

vacuumSectorConsequencesFromLeanReceipt :
  ∀ {Hamiltonian Vacuum Gap}
    {datum : VacuumGapDatum Hamiltonian Vacuum Gap} →
  VacuumSectorLeanTheoremReceipt datum →
  VacuumSectorSpectralConsequences datum
vacuumSectorConsequencesFromLeanReceipt = consequences

-- `standardImported` means theorem authority is external to this Agda kernel;
-- it is deliberately not labelled machineChecked here.
vacuumSectorSpectralMathematicsLeanLevel : ProofLevel
vacuumSectorSpectralMathematicsLeanLevel = standardImported

vacuumSectorSpectralNativeAgdaKernelLevel : ProofLevel
vacuumSectorSpectralNativeAgdaKernelLevel = conditional

vacuumSectorResolventStillPhysicalGap : Bool
vacuumSectorResolventStillPhysicalGap = false

vacuumSectorResolventStillPhysicalGapIsFalse :
  vacuumSectorResolventStillPhysicalGap ≡ false
vacuumSectorResolventStillPhysicalGapIsFalse = refl

data VacuumSectorLeanDonorPresent : Set where
  vacuumSectorLeanDonorPresent : VacuumSectorLeanDonorPresent

vacuumSectorLeanDonorWitness : VacuumSectorLeanDonorPresent
vacuumSectorLeanDonorWitness = vacuumSectorLeanDonorPresent
