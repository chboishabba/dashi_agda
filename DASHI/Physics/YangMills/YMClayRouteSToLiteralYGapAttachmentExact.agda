{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSToLiteralYGapAttachmentExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five

------------------------------------------------------------------------
-- B4 / EXACT ROUTE-S PHYSICAL GAP -> LITERAL-Y ATTACHMENT.
--
-- The source predicates below are stated on the certificate's OWN Hamiltonian
-- and gap.  The compiler must transport them through sameHamiltonian/sameGap;
-- merely storing equalities beside already-literal predicates is not accepted.
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

    certificatePositivityMeaning : ∀ G →
      OS.Positive (certificate G) (OS.gap (certificate G)) →
      Top.IsStrictlyPositiveFiniteMassGap S
        (OS.hamiltonian (certificate G))
        (OS.gap (certificate G))

    certificatePhysicalScaleLowerBound : ∀ G →
      Top.PhysicalScaleLowerBoundUniform S G
        (OS.gap (certificate G))

    certificateSpectrumMeaning : ∀ G →
      OS.SpectrumAboveVacuumGap (certificate G) →
      Top.NoSpectralPollutionBelowGap S G
        (OS.hamiltonian (certificate G))
        (OS.gap (certificate G))

    gapAndClusteringDerived : ∀ G →
      Top.GapAndClusteringAreDerivedNotAssumed S G

open RouteSPhysicalGapToLiteralYAttachment public

literalPositiveGap :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (attachment : RouteSPhysicalGapToLiteralYAttachment Y) G →
  Top.IsStrictlyPositiveFiniteMassGap S
    (Top.hamiltonian Y G) (Top.massGap Y G)
literalPositiveGap attachment G =
  let
    source =
      certificatePositivityMeaning attachment G
        (OS.gapPositive (certificate attachment G))

    gapTransported :
      Top.IsStrictlyPositiveFiniteMassGap _
        (OS.hamiltonian (certificate attachment G))
        (Top.massGap _ G)
    gapTransported =
      subst
        (Top.IsStrictlyPositiveFiniteMassGap _
          (OS.hamiltonian (certificate attachment G)))
        (sameGap attachment G)
        source
  in
  subst
    (λ h →
      Top.IsStrictlyPositiveFiniteMassGap _
        h (Top.massGap _ G))
    (sameHamiltonian attachment G)
    gapTransported

literalPhysicalScaleLowerBound :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (attachment : RouteSPhysicalGapToLiteralYAttachment Y) G →
  Top.PhysicalScaleLowerBoundUniform S G (Top.massGap Y G)
literalPhysicalScaleLowerBound attachment G =
  subst
    (Top.PhysicalScaleLowerBoundUniform _ G)
    (sameGap attachment G)
    (certificatePhysicalScaleLowerBound attachment G)

literalNoSpectralPollution :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (attachment : RouteSPhysicalGapToLiteralYAttachment Y) G →
  Top.NoSpectralPollutionBelowGap S G
    (Top.hamiltonian Y G) (Top.massGap Y G)
literalNoSpectralPollution attachment G =
  let
    source =
      certificateSpectrumMeaning attachment G
        (OS.spectrumAboveVacuumGap (certificate attachment G))

    gapTransported :
      Top.NoSpectralPollutionBelowGap _ G
        (OS.hamiltonian (certificate attachment G))
        (Top.massGap _ G)
    gapTransported =
      subst
        (Top.NoSpectralPollutionBelowGap _ G
          (OS.hamiltonian (certificate attachment G)))
        (sameGap attachment G)
        source
  in
  subst
    (λ h →
      Top.NoSpectralPollutionBelowGap _ G
        h (Top.massGap _ G))
    (sameHamiltonian attachment G)
    gapTransported

routeSPhysicalGapBuildsLiteralYGap :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  RouteSPhysicalGapToLiteralYAttachment Y →
  Five.CutoffUniformPhysicalMassGap Y
routeSPhysicalGapBuildsLiteralYGap attachment = record
  { Five.CutoffUniformPhysicalMassGap.vacuumSectorAndPositiveEnergyComplement =
      vacuumSectorAndPositiveEnergyComplement attachment
  ; Five.CutoffUniformPhysicalMassGap.strictlyPositiveFiniteMassGap =
      literalPositiveGap attachment
  ; Five.CutoffUniformPhysicalMassGap.physicalScaleLowerBoundUniform =
      literalPhysicalScaleLowerBound attachment
  ; Five.CutoffUniformPhysicalMassGap.noSpectralPollutionBelowGap =
      literalNoSpectralPollution attachment
  ; Five.CutoffUniformPhysicalMassGap.gapAndClusteringDerived =
      gapAndClusteringDerived attachment
  }

routeSPhysicalGapLiteralYAttachmentCompilerLevel : ProofLevel
routeSPhysicalGapLiteralYAttachmentCompilerLevel = machineChecked
