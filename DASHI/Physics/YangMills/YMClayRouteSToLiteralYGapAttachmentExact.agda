{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSToLiteralYGapAttachmentExact where

open import Agda.Builtin.Equality using (_≡_; subst)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five

------------------------------------------------------------------------
-- B4 / EXACT ROUTE-S PHYSICAL GAP -> LITERAL-Y ATTACHMENT.
--
-- Do not accept an opaque CutoffUniformPhysicalMassGap Y as the cross-prover
-- bridge.  The source object is a physical gap certificate on the reconstructed
-- Hamiltonian.  The integration theorem must attach that exact Hamiltonian and
-- exact gap value to Y and interpret its positivity/spectral content as the
-- literal endpoint predicates.
------------------------------------------------------------------------

record RouteSPhysicalGapToLiteralYAttachment
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    certificate : ∀ G →
      OS.PhysicalMassGapCertificate (Top.Hamiltonian C) ℚ

    sameHamiltonian : ∀ G →
      OS.hamiltonian (certificate G) ≡ Top.hamiltonian Y G

    sameGap : ∀ G →
      OS.gap (certificate G) ≡ Top.massGap Y G

    vacuumSectorAndPositiveEnergyComplement : ∀ G →
      Top.IsVacuumSectorAndPositiveEnergyComplement S
        (Top.hilbertSpace Y G) (Top.hamiltonian Y G) (Top.vacuum Y G)

    certificatePositivityMeansLiteralPositiveGap : ∀ G →
      OS.Positive (certificate G) (OS.gap (certificate G)) →
      Top.IsStrictlyPositiveFiniteMassGap S
        (Top.hamiltonian Y G) (Top.massGap Y G)

    physicalScaleLowerBoundUniform : ∀ G →
      Top.PhysicalScaleLowerBoundUniform S G (Top.massGap Y G)

    certificateSpectrumMeansNoPollution : ∀ G →
      OS.SpectrumAboveVacuumGap (certificate G) →
      Top.NoSpectralPollutionBelowGap S G
        (Top.hamiltonian Y G) (Top.massGap Y G)

    gapAndClusteringDerived : ∀ G →
      Top.GapAndClusteringAreDerivedNotAssumed S G

open RouteSPhysicalGapToLiteralYAttachment public

routeSPhysicalGapBuildsLiteralYGap :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  RouteSPhysicalGapToLiteralYAttachment Y →
  Five.CutoffUniformPhysicalMassGap Y
routeSPhysicalGapBuildsLiteralYGap attachment = record
  { Five.CutoffUniformPhysicalMassGap.vacuumSectorAndPositiveEnergyComplement =
      vacuumSectorAndPositiveEnergyComplement attachment
  ; Five.CutoffUniformPhysicalMassGap.strictlyPositiveFiniteMassGap =
      λ G →
        certificatePositivityMeansLiteralPositiveGap attachment G
          (OS.gapPositive (certificate attachment G))
  ; Five.CutoffUniformPhysicalMassGap.physicalScaleLowerBoundUniform =
      physicalScaleLowerBoundUniform attachment
  ; Five.CutoffUniformPhysicalMassGap.noSpectralPollutionBelowGap =
      λ G →
        certificateSpectrumMeansNoPollution attachment G
          (OS.spectrumAboveVacuumGap (certificate attachment G))
  ; Five.CutoffUniformPhysicalMassGap.gapAndClusteringDerived =
      gapAndClusteringDerived attachment
  }

routeSPhysicalGapLiteralYAttachmentCompilerLevel : ProofLevel
routeSPhysicalGapLiteralYAttachmentCompilerLevel = machineChecked
