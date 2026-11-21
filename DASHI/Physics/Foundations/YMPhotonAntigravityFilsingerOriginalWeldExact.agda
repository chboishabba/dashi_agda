module DASHI.Physics.Foundations.YMPhotonAntigravityFilsingerOriginalWeldExact where

------------------------------------------------------------------------
-- 21 Nov 2026 | Source-native Maxwell/Cartan -> physical experiment weld
--
-- The user's YM/EM finding has TWO different scopes:
-- (i) EXISTING proved SU2 Cartan U1 Lie-bracket reduction, which gives the
--     ordinary EM-compatible gauge architecture;
-- (ii) separately source-conditional original E6 Higgs 27 / residual U(3)
--      electromagnetic direction (KK source owns its assumptions).
--
-- NEITHER proves a strictly positive gap of 4D continuum pure SU(N)
-- Yang--Mills, the mass of the photon, Maxwell experimental calibration,
-- or any change to gravity.
--
-- Critically, experiments already have repository OWNERS:
-- AntigravityExperimentPortfolioExact (4 alternative designs);
-- SuperconductingGravityExperimentDesignProofSearchCrossPollinationExact
-- (source-only versus constitutive worlds);
-- AmyEskridgeAntigravityExperimentBindingExact (consumer channel);
-- AntigravityClaimScopedExperimentalCutExact (claim-scope calibration);
-- SmithFilsingerSourceMaxwellBoundaryWeldExact and
-- SmithFilsingerMaxwellMaterialEnergyCutExact (signed natural/drive/
-- modulation work on the same selected original source/port).
-- This module REUSES, never fabricates, those original-scoped owners.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact as YM
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as EM
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as SU2
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Bracket
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityExperimentPortfolioExact as Portfolio
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentDesignProofSearchCrossPollinationExact as SC
import DASHI.Core.DiscriminatorSynthesisExact as Disc
import DASHI.Culture.AmyEskridgeAntigravityExperimentBindingExact as Amy
import DASHI.Physics.ExoticGravity.AntigravityClaimScopedExperimentalCutExact as ClaimCut
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as FSource
import DASHI.Physics.Motors.SmithFilsingerMaxwellMaterialEnergyCutExact as FEnergy

------------------------------------------------------------------------
-- Y0. Reuse ORIGINAL non-Abelian / Abelian Lie algebra identity, without
-- equating a Maxwell massless mode with an interacting mass gap.
------------------------------------------------------------------------

selectedU1EmbeddedYangMillsBracketIsZero :
  (a b : YM.U1LieAlgebra) →
  Bracket.lieBracket (YM.embedU1Lie a) (YM.embedU1Lie b)
    ≡ SU2.lieZero
selectedU1EmbeddedYangMillsBracketIsZero =
  YM.u1EmbeddedLieBracketZero

nonAbelianClayGapDoesNotFollowFromU1Restriction :
  YM.clayMassGapAutomaticallyProvesMaxwell ≡ false
nonAbelianClayGapDoesNotFollowFromU1Restriction = refl

ordinaryMaxwellApplicationNeedsSourceValidation :
  EM.applicationReductionNeedsIndependentValidation
    EM.canonicalU1ElectromagneticBoundary ≡ true
ordinaryMaxwellApplicationNeedsSourceValidation =
  EM.U1ElectromagneticBoundary.applicationReductionNeedsIndependentValidationIsTrue
    EM.canonicalU1ElectromagneticBoundary

------------------------------------------------------------------------
-- Y1. Existing antigravity portfolio retains four different experiments.
-- This is an EXACT source-owner projection, not a claimed measurement.
------------------------------------------------------------------------

originalAntigravityPortfolioCoverage :
  Portfolio.AntigravityExperimentCandidate →
  Portfolio.DiscriminationCoverage
originalAntigravityPortfolioCoverage = Portfolio.coverage

fourChannelExperimentDiscriminatesMetricVsNonmetric :
  Portfolio.metricVsNonmetric
    (Portfolio.coverage Portfolio.matchedFourChannelExperiment)
  ≡ true
fourChannelExperimentDiscriminatesMetricVsNonmetric =
  Portfolio.matchedFourChannelCoversMetricDiscrimination

weightOnlyDoesNotDiscriminateMetric :
  Portfolio.metricVsNonmetric
    (Portfolio.coverage Portfolio.weightOnlyExperiment)
  ≡ false
weightOnlyDoesNotDiscriminateMetric =
  Portfolio.weightOnlyDoesNotCoverMetricDiscrimination

-- The original source-only and constitutive-excess hypotheses can share
-- an apparent field signal. The native bundle can separate the two
-- MODEL worlds, but its existence does not measure either in the lab.
sameCoarseSignalInTwoExistingGravityWorlds :
  SC.coarseSignalObserver SC.sourceOnlyWorld
    ≡ SC.coarseSignalObserver SC.constitutiveExcessWorld
sameCoarseSignalInTwoExistingGravityWorlds = refl

originalJointDiscriminatorSeparatesModelWorlds :
  Disc.BundleSeparates
    SC.sourceNormalisedBundle
    SC.sourceOnlyWorld
    SC.constitutiveExcessWorld
originalJointDiscriminatorSeparatesModelWorlds =
  SC.sourceVsConstitutiveSeparated

claimRequiresOriginalChannel :
  (claim : Anti.AntigravityClaim) →
  Anti.RequiredDiscriminator
claimRequiresOriginalChannel = Anti.requiredDiscriminator

-- In particular Amy's two already source-owned consumer demands do not
-- collapse simply because their historical hypothesis family overlaps.
amyFreeFallAndRemoteMassDemandDifferentChannels :
  Amy.observationChannel Amy.amyLiTorrFreeFallExperimentDemand
    ≡ Amy.observationChannel Amy.amyLiTorrRemoteFieldExperimentDemand
    → ⊥
amyFreeFallAndRemoteMassDemandDifferentChannels =
  Amy.freeFallAndRemoteExperimentChannelsDistinct

-- Experimental designs and source/phase model separation DO NOT create
-- an actually executed, calibrated claim-scoped experimental cut.
claimScopedCalibrationDoesNotPromoteByNaming :
  ClaimCut.ClaimScopedCutBoundary.claimScopedCutAutomaticallyProvesClaim
    ClaimCut.canonicalClaimScopedCutBoundary ≡ false
claimScopedCalibrationDoesNotPromoteByNaming = refl

------------------------------------------------------------------------
-- Y2. A Filsinger original source and an ordinary electromagnetic
-- application require an explicit original-source E/H/port identity.
-- The signed-source work owner is not rebuilt.
------------------------------------------------------------------------

record OriginalFilsingerU1FieldMethodComparison
    (boundary : FSource.SelectedBoundary) : Set₂ where
  field
    originalU1Application : EM.U1ApplicationReduction
    selectedFieldPort : FSource.FormalFieldToPort boundary
    selectedSourceCycle :
      FSource.SignedSourceCycleWeld boundary selectedFieldPort
    selectedFieldMaterialWork :
      FEnergy.FieldMaterialEnergyWeld boundary
        selectedFieldPort selectedSourceCycle

    -- The source owner's field-port and energy records retain their
    -- UNPAID physical Maxwell/Poynting identification fields.  This
    -- wrapper adds no vacuous Set-valued "calibration witness".

open OriginalFilsingerU1FieldMethodComparison

-- Same original physical gate, with the already proved field+material
-- internal port cancellation from the source owner.
originalFilsingerConditionalSameSourceWork :
  (boundary : FSource.SelectedBoundary)
  (w : OriginalFilsingerU1FieldMethodComparison boundary) →
  ((FEnergy.FieldMaterialEnergyWeld.naturalInput
      (selectedFieldMaterialWork w)
    + FEnergy.FieldMaterialEnergyWeld.driverInput
      (selectedFieldMaterialWork w))
    + FEnergy.FieldMaterialEnergyWeld.modulationInput
        (selectedFieldMaterialWork w))
    +
    (FEnergy.FieldMaterialEnergyWeld.fieldStoredInitially
      (selectedFieldMaterialWork w)
    + FEnergy.FieldMaterialEnergyWeld.materialStoredInitially
        (selectedFieldMaterialWork w))
  ≡
  FEnergy.FieldMaterialEnergyWeld.usefulLoad
    (selectedFieldMaterialWork w)
  +
  (FEnergy.FieldMaterialEnergyWeld.fieldDissipationAndOutgoing
    (selectedFieldMaterialWork w)
  +
    (FEnergy.FieldMaterialEnergyWeld.materialDissipation
      (selectedFieldMaterialWork w)
    +
      (FEnergy.FieldMaterialEnergyWeld.modulationRecovery
        (selectedFieldMaterialWork w)
      +
        (FEnergy.FieldMaterialEnergyWeld.fieldStoredFinally
          (selectedFieldMaterialWork w)
        + FEnergy.FieldMaterialEnergyWeld.materialStoredFinally
            (selectedFieldMaterialWork w)))))
originalFilsingerSameSourceFieldMaterialWork boundary w =
  FEnergy.fieldMaterialCombinedWork
    boundary (selectedFieldPort w) (selectedSourceCycle w)
    (selectedFieldMaterialWork w)

------------------------------------------------------------------------
-- Y3. Antigravity and Filsinger are DISTINCT real experiments by default.
-- They can reuse the same EM differential/gauge methods without being the
-- same hardware, force channel, stress tensor or source reservoir.
------------------------------------------------------------------------

record CrossExperimentYMFieldMethodComparison
    (filsinger : FSource.SelectedBoundary)
    (gravityClaim : Anti.AntigravityClaim) : Set₂ where
  field
    selectedU1Gauge : YM.U1InsideSU2YangMills
    sourceEMSocket : EM.U1ApplicationReduction
    filsingerOriginal : OriginalFilsingerU1FieldMethodComparison filsinger

    gravityExperimentDesign : Portfolio.AntigravityExperimentCandidate
    gravityRequiredChannel : Anti.RequiredDiscriminator
    channelReallyMatchesClaim :
      gravityRequiredChannel ≡ Anti.requiredDiscriminator gravityClaim

    -- This records a method crosswalk only.  It asserts NO equation
    -- between Filsinger and gravity apparatus, E/H fields, source
    -- currents, measured force, or metric response.  Those belong in
    -- existing claim-scoped calibrated experiment and real port owners.

-- No global postulate, no fabricated gravitation, no claim that pure
-- SU(N) YM is Maxwell, and no measured antigravity event asserted.
