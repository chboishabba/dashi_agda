module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoIndependentTheoryCrossValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.CondensedMatter.FlatBandObservableFibreExact as Flat

------------------------------------------------------------------------
-- INDEPENDENT THEORY CROSS-VALIDATION, NOT A SUBSTITUTE HAMILTONIAN
--
-- Same chemical stoichiometry:
--   CoTa4Se8 = 4 * (Co1/4 TaSe2).
--
-- Independent source:
--   A. Sah et al., "Altermagnetism, kagome flat band, and Weyl fermion states
--   in magnetically intercalated transition metal dichalcogenides",
--   npj Quantum Materials 11, 63 (2026), DOI 10.1038/s41535-026-00885-5.
--
-- The source independently treats CoTa4Se8 in a 2x2x1 intercalated-TMD
-- calculation and reports the same high-level altermagnetic geometry:
--   * spin-degenerate kz=0 nodal plane;
--   * pronounced off-nodal splitting at kz=pi/(2c), including Gamma'-M';
--   * SOC mixes spin channels but preserves symmetry-constrained nodal
--     degeneracy while enhancing off-nodal splitting;
--   * CoTa4Se8 has the largest splitting in the studied AM subset,
--     approximately 110 meV at EF and 154 meV at -0.25 eV.
--
-- It also gives a four-site Y-sublattice tight-binding mechanism for the
-- hexagonal -> kagome-like -> kagome interpolation, with a distinguished site
-- below the intercalant, and reports analogous kagome-derived flat-band
-- features for Co-intercalated TaSe2.
--
-- The source is an INDEPENDENT THEORY TARGET.  Its numerical bands are not a
-- same-object replacement for the Sprague ARPES/DFT calculation or for a
-- repository-native Ta/Se/Co + SOC/exchange Hamiltonian.
------------------------------------------------------------------------

record IndependentTheorySource : Set where
  constructor independent-theory-source
  field
    doi : String
    compoundLabel : String
    sameStoichiometricFormulaAsCoQuarterTaSeTwo : Bool
    dftVASP : Bool
    pbeGGA : Bool
    pawCoreValence : Bool
    cutoff450eV : Bool
    mesh9x9x4 : Bool
    supercell2x2x1 : Bool
    ggaPlusURobustnessScan0to3eV : Bool

open IndependentTheorySource public

sah2026 : IndependentTheorySource
sah2026 = independent-theory-source
  "10.1038/s41535-026-00885-5"
  "CoTa4Se8"
  true true true true true true true true

record IndependentAltermagnetTargets : Set where
  constructor independent-altermagnet-targets
  field
    kzZeroNodalPlane : Bool
    kzPiOver2cOffNodalPlane : Bool
    gammaPrimeMPrimeSplit : Bool
    SOCIncluded : Bool
    SOCMixesPureSpinChannels : Bool
    symmetryConstrainedNodalDegeneracyWithSOC : Bool
    offNodalSOCEnhancedSplitting : Bool
    fermiLevelSplitMeVApprox : Nat
    minusQuarterEVSplitMeVApprox : Nat

open IndependentAltermagnetTargets public

sahCoTa4Se8Targets : IndependentAltermagnetTargets
sahCoTa4Se8Targets = independent-altermagnet-targets
  true true true true true true true
  110 154

record KagomeLikeMechanism : Set where
  constructor kagome-like-mechanism
  field
    fourYSitesPerTBCell : Bool
    oneIntercalantAlignedSiteDistinguished : Bool
    threeRemainingSitesFormEffectiveKagome : Bool
    nearestNeighbourModelPublished : Bool
    intercalantAlignedHoppingRatioTenths : Nat
    intercalantAlignedOnsiteRatioTenths : Nat
    analogousFeatureReportedForCoTa4Se8 : Bool
    mechanismIdentifiedWithTwistAngleMoiré : Bool

open KagomeLikeMechanism public

publishedKagomeLikeMechanism : KagomeLikeMechanism
publishedKagomeLikeMechanism = kagome-like-mechanism
  true true true true
  4 22
  true false

existingFlatBandBoundary : Flat.FlatBandPromotionBoundary
existingFlatBandBoundary = Flat.canonicalFlatBandPromotionBoundary

record WannierProducerRoute : Set where
  constructor wannier-producer-route
  field
    priorIntercalatedTMDLiteratureUsesSpinDFT : Bool
    priorIntercalatedTMDLiteratureBuildsWannierTB : Bool
    priorIntercalatedTMDLiteratureDerivesExchangeFromWannierTB : Bool
    routeIsMaterialSpecificArtifactAlreadyAcquiredHere : Bool

-- Hatanaka, Nomoto & Arita, PRB 107, 184429 (2023), DOI
-- 10.1103/PhysRevB.107.184429, supplies this producer architecture for a broad
-- intercalated-TMD family.  It is a METHOD DONOR only until executed for this
-- exact CoTa4Se8 state/basis with archived artifacts.
hatanaka2023ProducerRoute : WannierProducerRoute
hatanaka2023ProducerRoute = wannier-producer-route true true true false

record CrossValidationPromotionBoundary : Set where
  constructor cross-validation-promotion-boundary
  field
    independentTheoryPaysSameObjectHamiltonian : Bool
    agreementOfNodalPatternPaysRawARPES : Bool
    approximatePublishedSplittingPaysQuantitativeFit : Bool
    kagomeTBPaysFullTaSeCoSOCModel : Bool
    independentTheoryAddsMaterialAcceptanceTargets : Bool
    wannierRouteReducesProducerDesignDebt : Bool

canonicalCrossValidationPromotionBoundary : CrossValidationPromotionBoundary
canonicalCrossValidationPromotionBoundary =
  cross-validation-promotion-boundary
    false false false false true true
