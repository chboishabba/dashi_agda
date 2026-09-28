{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsDirectSourceOSSameHGapExact where

------------------------------------------------------------------------
-- H1 + H2(ii) + H3 SAME-H APPLICATION ON THE LITERAL Y.
--
-- This removes the last broad "massGapAttachment" selection from the direct
-- source/OS capstone.  For each compact-simple group G we carry:
--
--   * the exact finite measure/observable carrier of Y;
--   * the R467 literal published CMP116 application;
--   * the selected expectation/limit closure;
--   * positivity of the selected gap coordinate;
--   * a physical spectral interpretation;
--   * SAME-OBJECT equalities identifying that Hamiltonian and gap with
--     Y.hamiltonian G and Y.massGap G.
--
-- The transfer-gap core and physical mass-gap certificate are constructed.
-- Only interpretation into the opaque literal endpoint semantic predicates
-- remains explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralSelectedRound467Exact as R467
import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralSelectedGapExact as H1Gap
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.YMClayR387PhysicalSpectrumExact as Spectrum

record LiteralGroupDirectSourceSameHGap
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (G : Top.CompactSimpleGroup C)
    : Set₂ where
  field
    --------------------------------------------------------------------
    -- Selected finite family, on the literal endpoint carriers.
    --------------------------------------------------------------------
    dataSet :
      Gram.PhysicalMeasureConvergenceData
        (Top.FiniteMeasure C)
        (Top.Observable C)
        ℚ

    literalFiniteFamily :
      ∀ cutoff →
      Gram.measureSequence dataSet cutoff
      ≡ Top.finiteMeasure Y G cutoff

    extension :
      R278.ScalarCovarianceConvergenceExtension dataSet

    base :
      R318.UnlocalizedT5StateFamilyJPresentation dataSet extension

    tests :
      R278.SelectedConnectedCovarianceTests dataSet

    spectrumSource :
      R281.ContinuumCovarianceSpectrumData
        {SpectralObservable = Top.Observable C}
        {Energy = ℚ}
        dataSet extension tests

    --------------------------------------------------------------------
    -- H1: literal CMP116 application on this selected family.
    --------------------------------------------------------------------
    literalCMP116 :
      R467.PublishedLiteralSelectedLocalization
        base tests spectrumSource

    --------------------------------------------------------------------
    -- H2(ii): selected covariance limit/order closure.
    --------------------------------------------------------------------
    selectedLimitClosure :
      R342.SelectedLimitUpperClosure {dataSet = dataSet}

    positiveCandidateGap :
      Gap.PositiveEnergy
        (R281.asReconstructedClusteringSpectrum spectrumSource)
        (Gap.gapCandidate
          (R281.asReconstructedClusteringSpectrum spectrumSource))

    --------------------------------------------------------------------
    -- H3: the spectrum is the SAME reconstructed physical Hamiltonian.
    --------------------------------------------------------------------
    physicalSpectrum :
      Spectrum.PhysicalSpectrumInterpretation
        {Hamiltonian = Top.Hamiltonian C}
        (R281.asReconstructedClusteringSpectrum spectrumSource)

    physicalHamiltonianIsLiteral :
      Spectrum.physicalHamiltonian physicalSpectrum
      ≡ Top.hamiltonian Y G

    selectedGapIsLiteral :
      Gap.gapCandidate
        (R281.asReconstructedClusteringSpectrum spectrumSource)
      ≡ Top.massGap Y G

    --------------------------------------------------------------------
    -- Endpoint interpretation only.  No estimate is hidden here.
    --------------------------------------------------------------------
    certificateMeansVacuumSector :
      (certificate : OSGap.PhysicalMassGapCertificate (Top.Hamiltonian C) ℚ) →
      OSGap.hamiltonian certificate ≡ Top.hamiltonian Y G →
      OSGap.gap certificate ≡ Top.massGap Y G →
      Top.IsVacuumSectorAndPositiveEnergyComplement S
        (Top.hilbertSpace Y G)
        (Top.hamiltonian Y G)
        (Top.vacuum Y G)

    certificateMeansStrictLiteralGap :
      (certificate : OSGap.PhysicalMassGapCertificate (Top.Hamiltonian C) ℚ) →
      OSGap.hamiltonian certificate ≡ Top.hamiltonian Y G →
      OSGap.gap certificate ≡ Top.massGap Y G →
      Top.IsStrictlyPositiveFiniteMassGap S
        (Top.hamiltonian Y G)
        (Top.massGap Y G)

    certificateMeansUniformPhysicalScale :
      (certificate : OSGap.PhysicalMassGapCertificate (Top.Hamiltonian C) ℚ) →
      OSGap.gap certificate ≡ Top.massGap Y G →
      Top.PhysicalScaleLowerBoundUniform S G
        (Top.massGap Y G)

    certificateMeansNoSubgapPollution :
      (certificate : OSGap.PhysicalMassGapCertificate (Top.Hamiltonian C) ℚ) →
      OSGap.hamiltonian certificate ≡ Top.hamiltonian Y G →
      OSGap.gap certificate ≡ Top.massGap Y G →
      Top.NoSpectralPollutionBelowGap S G
        (Top.hamiltonian Y G)
        (Top.massGap Y G)

    clusteringAndGapAreDerived :
      Top.GapAndClusteringAreDerivedNotAssumed S G

open LiteralGroupDirectSourceSameHGap public

transferGapCore :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    {G : Top.CompactSimpleGroup C}
    (input :
      LiteralGroupDirectSourceSameHGap
        {C = C} {S = S} Y G) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum
      (spectrumSource input))
transferGapCore input =
  H1Gap.literalPublishedSelectedBuildsPositiveTransferGap
    (literalCMP116 input)
    (selectedLimitClosure input)
    (positiveCandidateGap input)

physicalMassGapCertificate :
  ∀ {C S Y G}
    (input :
      LiteralGroupDirectSourceSameHGap
        {C = C} {S = S} Y G) →
  OSGap.PhysicalMassGapCertificate
    (Top.Hamiltonian C) ℚ
physicalMassGapCertificate input =
  Spectrum.physicalMassGapCertificateFromTransferGapCore
    (physicalSpectrum input)
    (transferGapCore input)


certificateHamiltonianIsLiteral :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    {G : Top.CompactSimpleGroup C}
    (input :
      LiteralGroupDirectSourceSameHGap
        {C = C} {S = S} Y G) →
  OSGap.hamiltonian (physicalMassGapCertificate input)
  ≡ Top.hamiltonian Y G
certificateHamiltonianIsLiteral input =
  physicalHamiltonianIsLiteral input

certificateGapIsLiteral :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    {G : Top.CompactSimpleGroup C}
    (input :
      LiteralGroupDirectSourceSameHGap
        {C = C} {S = S} Y G) →
  OSGap.gap (physicalMassGapCertificate input)
  ≡ Top.massGap Y G
certificateGapIsLiteral input =
  selectedGapIsLiteral input

record LiteralDirectSourceSameHMassGap
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    : Set₂ where
  field
    forGroup :
      ∀ G →
      LiteralGroupDirectSourceSameHGap Y G

open LiteralDirectSourceSameHMassGap public

asCutoffUniformPhysicalMassGap :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  LiteralDirectSourceSameHMassGap Y →
  Five.CutoffUniformPhysicalMassGap Y
asCutoffUniformPhysicalMassGap direct = record
  { Five.CutoffUniformPhysicalMassGap.vacuumSectorAndPositiveEnergyComplement =
      λ G →
        certificateMeansVacuumSector (forGroup direct G)
          (physicalMassGapCertificate (forGroup direct G))
          (certificateHamiltonianIsLiteral (forGroup direct G))
          (certificateGapIsLiteral (forGroup direct G))
  ; Five.CutoffUniformPhysicalMassGap.strictlyPositiveFiniteMassGap =
      λ G →
        certificateMeansStrictLiteralGap (forGroup direct G)
          (physicalMassGapCertificate (forGroup direct G))
          (certificateHamiltonianIsLiteral (forGroup direct G))
          (certificateGapIsLiteral (forGroup direct G))
  ; Five.CutoffUniformPhysicalMassGap.physicalScaleLowerBoundUniform =
      λ G →
        certificateMeansUniformPhysicalScale (forGroup direct G)
          (physicalMassGapCertificate (forGroup direct G))
          (certificateGapIsLiteral (forGroup direct G))
  ; Five.CutoffUniformPhysicalMassGap.noSpectralPollutionBelowGap =
      λ G →
        certificateMeansNoSubgapPollution (forGroup direct G)
          (physicalMassGapCertificate (forGroup direct G))
          (certificateHamiltonianIsLiteral (forGroup direct G))
          (certificateGapIsLiteral (forGroup direct G))
  ; Five.CutoffUniformPhysicalMassGap.gapAndClusteringDerived =
      λ G →
        clusteringAndGapAreDerived (forGroup direct G)
  }

directSourceSameHGapCompilerLevel : ProofLevel
directSourceSameHGapCompilerLevel = machineChecked

-- The mathematical H1 -> transfer-gap -> physical-certificate chain is
-- compiler-owned.  Remaining physical content is exactly the R467 application,
-- H2 selected convergence/limit closure, H3 spectral same-object attachment,
-- and interpretation of that constructed certificate in the literal endpoint
-- semantic vocabulary.
directSourceSameHGapPhysicalInstantiationLevel : ProofLevel
directSourceSameHGapPhysicalInstantiationLevel = conditional
