module DASHI.Moonshine.OggSSPPBGreenRingSectorSpeciesCutsetExact where

------------------------------------------------------------------------
-- pB GREEN-RING / DVR SECTOR SPECIES CUTSET
--
-- EXTERNAL SOURCES
--
-- Scott Carnahan and Satoru Urano,
-- "Monstrous Moonshine for Integral Group Rings", IMRN 2024:
--
--   * formulates a representation/Green-ring -> Hauptmodul principle for
--     self-dual integral forms of V^natural;
--   * proves that principle in selected cases;
--   * DOES NOT prove the p=2B / p=3B prime=level Igusa-sector localization
--     required below.
--
-- Satoru Urano, SIGMA 2021:
--
--   * generalized Brauer characters for arbitrary finite-length DVR modules;
--   * additivity through composition factors;
--   * Tate super-Brauer characters are trace-function combinations;
--   * DOES NOT assign the integral pB Tate object to the DASHI geometric
--     sectors or prove the sector lengths 3,3,2,1,1 / 1,1.
--
-- DASHI PURPOSE
--
-- Replace the vague final wall with one target-independent payment:
--
--   construct sectorwise finite-length classes of the SAME integral pB object,
--   prove their normalized DVR lengths match the independently owned geometric
--   weights, and prove the resulting additive species is the bad-level
--   Green-ring/Hauptmodul observable.
--
-- Once this record is inhabited, an adapter constructs the already-owned
-- PBLocalizedDVRPreferredPaymentAuthority.  No Monster order or 10/2 target is
-- permitted as an input.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPPBLocalizedDVRPreferredPaymentCutsetExact as Payment
import DASHI.Moonshine.OggSSPSmallPrimePBIntegralTateCohomologyBridgeExact as Tate
import DASHI.Moonshine.OggSSPSmallPrimeDVRLengthBrauerCutsetExact as DVR
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as P2Inertia
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3

------------------------------------------------------------------------
-- 1. Source atlas.
------------------------------------------------------------------------

carnahanUranoIntegralGroupRings : Source.AttributedSource
carnahanUranoIntegralGroupRings =
  Source.mkDOISource
    "Scott Carnahan and Satoru Urano"
    "Monstrous Moonshine for Integral Group Rings"
    "International Mathematics Research Notices 2024(4), 2748-2789"
    "2024"
    "10.1093/imrn/rnad028"
    "https://doi.org/10.1093/imrn/rnad028"
    Source.academicArticleSource
    "formulates the Green/representation-ring to Hauptmodul principle for self-dual integral Moonshine forms and proves selected cases; used here only as the source framework for a possible sectorwise species, not as authority for pB Igusa localization or the DASHI sector weights"
    Source.publicAttribution

greenRingSectorSpeciesSourceAtlas : Source.AttributedSourceAtlas
greenRingSectorSpeciesSourceAtlas =
  Source.mkSourceAtlas
    "pB Green-ring / DVR sector-species cutset"
    "DASHI.Moonshine.OggSSPPBGreenRingSectorSpeciesCutsetExact"
    (carnahanUranoIntegralGroupRings ∷ DVR.uranoCompositeOrder ∷ [])
    "Carnahan-Urano own the integral-group-ring/Hauptmodul framework and Urano owns finite-length DVR Brauer theory; DASHI owns the proposed prime=level Igusa-sector specialization and all geometric weights"

------------------------------------------------------------------------
-- 2. Minimal semiring/species interface.
--
-- This is deliberately abstract.  It does not assert that normalized
-- composition length is automatically multiplicative.  A real inhabitant must
-- pay both additive and multiplicative compatibility for the particular
-- species used to invoke the Green-ring/Hauptmodul framework.
------------------------------------------------------------------------

record SectorGreenSpecies : Set₁ where
  field
    ModuleClass : Set

    zeroClass :
      ModuleClass

    directSum :
      ModuleClass ->
      ModuleClass ->
      ModuleClass

    tensorProduct :
      ModuleClass ->
      ModuleClass ->
      ModuleClass

    speciesValue :
      ModuleClass ->
      Nat

    speciesZero :
      speciesValue zeroClass ≡ 0

    speciesAdditive :
      (left right : ModuleClass) ->
      speciesValue (directSum left right)
      ≡
      speciesValue left + speciesValue right

    speciesMultiplicative :
      (left right : ModuleClass) ->
      speciesValue (tensorProduct left right)
      ≡
      speciesValue left * speciesValue right

open SectorGreenSpecies public

------------------------------------------------------------------------
-- 3. Target-independent pB localization/species authority.
------------------------------------------------------------------------

record PBGreenRingSectorSpeciesAuthority : Set₁ where
  field
    species :
      SectorGreenSpecies

    p2SectorClass :
      Preferred.Sector Preferred.p2PreferredPresentation ->
      ModuleClass species

    p3SectorClass :
      Preferred.Sector Preferred.p3PreferredPresentation ->
      ModuleClass species

    normalizedDVRLength :
      ModuleClass species ->
      Nat

    speciesValueIsNormalizedDVRLength :
      (moduleClass : ModuleClass species) ->
      speciesValue species moduleClass
      ≡
      normalizedDVRLength moduleClass

    p2LengthMatchesIndependentGeometricWeight :
      (sector : Preferred.Sector Preferred.p2PreferredPresentation) ->
      normalizedDVRLength (p2SectorClass sector)
      ≡
      Preferred.weight Preferred.p2PreferredPresentation sector

    p3LengthMatchesIndependentGeometricWeight :
      (sector : Preferred.Sector Preferred.p3PreferredPresentation) ->
      normalizedDVRLength (p3SectorClass sector)
      ≡
      Preferred.weight Preferred.p3PreferredPresentation sector

    classesComeFromCarnahanIntegralPBTateObject :
      Bool
    classesComeFromCarnahanIntegralPBTateObjectIsTrue :
      classesComeFromCarnahanIntegralPBTateObject ≡ true

    classesComeFromPrimeEqualsLevelIgusaWildLocalization :
      Bool
    classesComeFromPrimeEqualsLevelIgusaWildLocalizationIsTrue :
      classesComeFromPrimeEqualsLevelIgusaWildLocalization ≡ true

    decompositionPreservesPBMonsterLocalCentralizerAction :
      Bool
    decompositionPreservesPBMonsterLocalCentralizerActionIsTrue :
      decompositionPreservesPBMonsterLocalCentralizerAction ≡ true

    generalizedBrauerCharacterCompatibleWithSectorDecomposition :
      Bool
    generalizedBrauerCharacterCompatibleWithSectorDecompositionIsTrue :
      generalizedBrauerCharacterCompatibleWithSectorDecomposition ≡ true

    normalizedLengthIsUranoCompositionLength :
      Bool
    normalizedLengthIsUranoCompositionLengthIsTrue :
      normalizedLengthIsUranoCompositionLength ≡ true

    moduleClassesAreFiniteLengthDVRModules :
      Bool
    moduleClassesAreFiniteLengthDVRModulesIsTrue :
      moduleClassesAreFiniteLengthDVRModules ≡ true

    generalizedBrauerCharacterAgreesWithPBTrace :
      Bool
    generalizedBrauerCharacterAgreesWithPBTraceIsTrue :
      generalizedBrauerCharacterAgreesWithPBTrace ≡ true

    sectorSpeciesFactorsThroughRelevantGreenRing :
      Bool
    sectorSpeciesFactorsThroughRelevantGreenRingIsTrue :
      sectorSpeciesFactorsThroughRelevantGreenRing ≡ true

    carnahanUranoHauptmodulSpecializationProvedForThisSpecies :
      Bool
    carnahanUranoHauptmodulSpecializationProvedForThisSpeciesIsTrue :
      carnahanUranoHauptmodulSpecializationProvedForThisSpecies ≡ true

    resultingHauptmodulObservableIsBadLevelCorrectedObservable :
      Bool
    resultingHauptmodulObservableIsBadLevelCorrectedObservableIsTrue :
      resultingHauptmodulObservableIsBadLevelCorrectedObservable ≡ true

    constructionUsesNoMonsterOrderTarget :
      Bool
    constructionUsesNoMonsterOrderTargetIsTrue :
      constructionUsesNoMonsterOrderTarget ≡ true

    constructionUsesNoDuncanSwisherResidualTarget :
      Bool
    constructionUsesNoDuncanSwisherResidualTargetIsTrue :
      constructionUsesNoDuncanSwisherResidualTarget ≡ true

open PBGreenRingSectorSpeciesAuthority public

------------------------------------------------------------------------
-- 4. Adapter to the existing preferred DVR payment wall.
------------------------------------------------------------------------

asLocalizedDVRPreferredPaymentAuthority :
  PBGreenRingSectorSpeciesAuthority ->
  Payment.PBLocalizedDVRPreferredPaymentAuthority
asLocalizedDVRPreferredPaymentAuthority A =
  record
    { Payment.LocalizedPiece =
        ModuleClass (species A)
    ; Payment.p2Piece =
        p2SectorClass A
    ; Payment.p3Piece =
        p3SectorClass A
    ; Payment.normalizedDVRLength =
        normalizedDVRLength A
    ; Payment.p2LengthMatchesIndependentGeometricWeight =
        p2LengthMatchesIndependentGeometricWeight A
    ; Payment.p3LengthMatchesIndependentGeometricWeight =
        p3LengthMatchesIndependentGeometricWeight A
    ; Payment.piecesComeFromCarnahanIntegralPBTateObject =
        classesComeFromCarnahanIntegralPBTateObject A
    ; Payment.piecesComeFromCarnahanIntegralPBTateObjectIsTrue =
        classesComeFromCarnahanIntegralPBTateObjectIsTrue A
    ; Payment.piecesComeFromPrimeEqualsLevelIgusaWildLocalization =
        classesComeFromPrimeEqualsLevelIgusaWildLocalization A
    ; Payment.piecesComeFromPrimeEqualsLevelIgusaWildLocalizationIsTrue =
        classesComeFromPrimeEqualsLevelIgusaWildLocalizationIsTrue A
    ; Payment.decompositionPreservesPBMonsterLocalCentralizerAction =
        decompositionPreservesPBMonsterLocalCentralizerAction A
    ; Payment.decompositionPreservesPBMonsterLocalCentralizerActionIsTrue =
        decompositionPreservesPBMonsterLocalCentralizerActionIsTrue A
    ; Payment.generalizedBrauerCharacterCompatibleWithSectorDecomposition =
        generalizedBrauerCharacterCompatibleWithSectorDecomposition A
    ; Payment.generalizedBrauerCharacterCompatibleWithSectorDecompositionIsTrue =
        generalizedBrauerCharacterCompatibleWithSectorDecompositionIsTrue A
    ; Payment.lengthIsUranoNormalizedCompositionLength =
        normalizedLengthIsUranoCompositionLength A
    ; Payment.lengthIsUranoNormalizedCompositionLengthIsTrue =
        normalizedLengthIsUranoCompositionLengthIsTrue A
    ; Payment.constructionUsesNoMonsterOrderTarget =
        constructionUsesNoMonsterOrderTarget A
    ; Payment.constructionUsesNoMonsterOrderTargetIsTrue =
        constructionUsesNoMonsterOrderTargetIsTrue A
    ; Payment.constructionUsesNoDuncanSwisherResidualTarget =
        constructionUsesNoDuncanSwisherResidualTarget A
    ; Payment.constructionUsesNoDuncanSwisherResidualTargetIsTrue =
        constructionUsesNoDuncanSwisherResidualTargetIsTrue A
    }

------------------------------------------------------------------------
-- 4b. Adapter to the existing preferred analytic-valuation authority.
--
-- The Green-ring authority is target-independent: its sector classes and
-- lengths are constructed without Monster-order or Duncan--Swisher residual
-- targets.  After that theorem is paid, the already-owned Preferred module
-- supplies the independent arithmetic equalities showing that the sector
-- totals are the 10/2 gaps.  Thus the downstream recognition is derived rather
-- than used to define the local species.
------------------------------------------------------------------------

asPreferredCorrectedValuationAuthority :
  PBGreenRingSectorSpeciesAuthority ->
  Preferred.PreferredCorrectedValuationAuthority
asPreferredCorrectedValuationAuthority A =
  record
    { Preferred.AnalyticLocalTerm =
        ModuleClass (species A)
    ; Preferred.p2AnalyticTerm =
        p2SectorClass A
    ; Preferred.p3AnalyticTerm =
        p3SectorClass A
    ; Preferred.analyticMultiplicity =
        normalizedDVRLength A
    ; Preferred.p2WeightsAreActualLocalValuations =
        λ sector ->
          sym (p2LengthMatchesIndependentGeometricWeight A sector)
    ; Preferred.p3WeightsAreActualLocalValuations =
        λ sector ->
          sym (p3LengthMatchesIndependentGeometricWeight A sector)
    ; Preferred.localTermsAssembleIntoCorrectedHauptmodulValuation =
        resultingHauptmodulObservableIsBadLevelCorrectedObservable A
    ; Preferred.localTermsAssembleIntoCorrectedHauptmodulValuationIsTrue =
        resultingHauptmodulObservableIsBadLevelCorrectedObservableIsTrue A
    ; Preferred.correctedValuationPaysDuncanSwisherP2Gap =
        true
    ; Preferred.correctedValuationPaysDuncanSwisherP2GapIsTrue =
        refl
    ; Preferred.correctedValuationPaysDuncanSwisherP3Gap =
        true
    ; Preferred.correctedValuationPaysDuncanSwisherP3GapIsTrue =
        refl
    }

p2GapEquationAfterGreenSpecies :
  (A : PBGreenRingSectorSpeciesAuthority) ->
  Preferred.total Preferred.p2PreferredPresentation ≡ 10
p2GapEquationAfterGreenSpecies A =
  Preferred.p2PreferredTotalIsTen

p3GapEquationAfterGreenSpecies :
  (A : PBGreenRingSectorSpeciesAuthority) ->
  Preferred.total Preferred.p3PreferredPresentation ≡ 2
p3GapEquationAfterGreenSpecies A =
  Preferred.p3PreferredTotalIsTwo

------------------------------------------------------------------------
-- 4c. Fold the sector pieces into the global localized DVR modules.
------------------------------------------------------------------------

normalizedLengthDirectSum :
  (A : PBGreenRingSectorSpeciesAuthority) ->
  (left right : ModuleClass (species A)) ->
  normalizedDVRLength A
    (directSum (species A) left right)
  ≡
  normalizedDVRLength A left
  + normalizedDVRLength A right
normalizedLengthDirectSum A left right =
  trans
    (sym
      (speciesValueIsNormalizedDVRLength A
        (directSum (species A) left right)))
    (trans
      (speciesAdditive (species A) left right)
      (cong₂ _+_
        (speciesValueIsNormalizedDVRLength A left)
        (speciesValueIsNormalizedDVRLength A right)))

p2CombinedLocalizedClass :
  PBGreenRingSectorSpeciesAuthority ->
  ModuleClass ∘ species
p2CombinedLocalizedClass A =
  directSum (species A)
    (p2SectorClass A P2Inertia.identityInertiaOrbit)
    (directSum (species A)
      (p2SectorClass A P2Inertia.centralMinusOneInertiaOrbit)
      (directSum (species A)
        (p2SectorClass A P2Inertia.orderFourInertiaOrbit)
        (directSum (species A)
          (p2SectorClass A P2Inertia.orderThreePairInertiaOrbit)
          (p2SectorClass A P2Inertia.orderSixPairInertiaOrbit))))

p3CombinedLocalizedClass :
  PBGreenRingSectorSpeciesAuthority ->
  ModuleClass ∘ species
p3CombinedLocalizedClass A =
  directSum (species A)
    (p3SectorClass A P3.nodeOrbit)
    (p3SectorClass A P3.branchOrbit)

p2CombinedLengthIsTen :
  (A : PBGreenRingSectorSpeciesAuthority) ->
  normalizedDVRLength A (p2CombinedLocalizedClass A) ≡ 10
p2CombinedLengthIsTen A =
  trans
    (normalizedLengthDirectSum A
      (p2SectorClass A P2Inertia.identityInertiaOrbit)
      (directSum (species A)
        (p2SectorClass A P2Inertia.centralMinusOneInertiaOrbit)
        (directSum (species A)
          (p2SectorClass A P2Inertia.orderFourInertiaOrbit)
          (directSum (species A)
            (p2SectorClass A P2Inertia.orderThreePairInertiaOrbit)
            (p2SectorClass A P2Inertia.orderSixPairInertiaOrbit)))))
    (trans
      (cong₂ _+_
        (p2LengthMatchesIndependentGeometricWeight A
          P2Inertia.identityInertiaOrbit)
        (trans
          (normalizedLengthDirectSum A
            (p2SectorClass A P2Inertia.centralMinusOneInertiaOrbit)
            (directSum (species A)
              (p2SectorClass A P2Inertia.orderFourInertiaOrbit)
              (directSum (species A)
                (p2SectorClass A P2Inertia.orderThreePairInertiaOrbit)
                (p2SectorClass A P2Inertia.orderSixPairInertiaOrbit))))
          (cong₂ _+_
            (p2LengthMatchesIndependentGeometricWeight A
              P2Inertia.centralMinusOneInertiaOrbit)
            (trans
              (normalizedLengthDirectSum A
                (p2SectorClass A P2Inertia.orderFourInertiaOrbit)
                (directSum (species A)
                  (p2SectorClass A P2Inertia.orderThreePairInertiaOrbit)
                  (p2SectorClass A P2Inertia.orderSixPairInertiaOrbit)))
              (cong₂ _+_
                (p2LengthMatchesIndependentGeometricWeight A
                  P2Inertia.orderFourInertiaOrbit)
                (trans
                  (normalizedLengthDirectSum A
                    (p2SectorClass A P2Inertia.orderThreePairInertiaOrbit)
                    (p2SectorClass A P2Inertia.orderSixPairInertiaOrbit))
                  (cong₂ _+_
                    (p2LengthMatchesIndependentGeometricWeight A
                      P2Inertia.orderThreePairInertiaOrbit)
                    (p2LengthMatchesIndependentGeometricWeight A
                      P2Inertia.orderSixPairInertiaOrbit))))))))
      refl)

p3CombinedLengthIsTwo :
  (A : PBGreenRingSectorSpeciesAuthority) ->
  normalizedDVRLength A (p3CombinedLocalizedClass A) ≡ 2
p3CombinedLengthIsTwo A =
  trans
    (normalizedLengthDirectSum A
      (p3SectorClass A P3.nodeOrbit)
      (p3SectorClass A P3.branchOrbit))
    (trans
      (cong₂ _+_
        (p3LengthMatchesIndependentGeometricWeight A P3.nodeOrbit)
        (p3LengthMatchesIndependentGeometricWeight A P3.branchOrbit))
      refl)

asGlobalLocalizedDVRBrauerAuthority :
  PBGreenRingSectorSpeciesAuthority ->
  DVR.PBLocalizedDVRBrauerAuthority
asGlobalLocalizedDVRBrauerAuthority A =
  record
    { DVR.LocalizedTateModule =
        ModuleClass (species A)
    ; DVR.p2LocalizedModule =
        p2CombinedLocalizedClass A
    ; DVR.p3LocalizedModule =
        p3CombinedLocalizedClass A
    ; DVR.isFiniteLengthOverRelevantDVR =
        λ prime moduleClass -> moduleClassesAreFiniteLengthDVRModules A
    ; DVR.p2FiniteLength =
        moduleClassesAreFiniteLengthDVRModulesIsTrue A
    ; DVR.p3FiniteLength =
        moduleClassesAreFiniteLengthDVRModulesIsTrue A
    ; DVR.comesFromCarnahanPBIntegralTateObject =
        classesComeFromCarnahanIntegralPBTateObject A
    ; DVR.comesFromCarnahanPBIntegralTateObjectIsTrue =
        classesComeFromCarnahanIntegralPBTateObjectIsTrue A
    ; DVR.localizedAtPrimeEqualsLevelIgusaObject =
        classesComeFromPrimeEqualsLevelIgusaWildLocalization A
    ; DVR.localizedAtPrimeEqualsLevelIgusaObjectIsTrue =
        classesComeFromPrimeEqualsLevelIgusaWildLocalizationIsTrue A
    ; DVR.preservesPBMonsterLocalCentralizerAction =
        decompositionPreservesPBMonsterLocalCentralizerAction A
    ; DVR.preservesPBMonsterLocalCentralizerActionIsTrue =
        decompositionPreservesPBMonsterLocalCentralizerActionIsTrue A
    ; DVR.generalizedBrauerCharacterAgreesWithPBTrace =
        generalizedBrauerCharacterAgreesWithPBTrace A
    ; DVR.generalizedBrauerCharacterAgreesWithPBTraceIsTrue =
        generalizedBrauerCharacterAgreesWithPBTraceIsTrue A
    ; DVR.lengthFunctional =
        λ prime moduleClass -> normalizedDVRLength A moduleClass
    ; DVR.p2LengthPaysResidual =
        trans (p2CombinedLengthIsTen A) refl
    ; DVR.p3LengthPaysResidual =
        trans (p3CombinedLengthIsTwo A) refl
    ; DVR.lengthFunctionalDerivedWithoutReadingTarget =
        constructionUsesNoDuncanSwisherResidualTarget A
    ; DVR.lengthFunctionalDerivedWithoutReadingTargetIsTrue =
        constructionUsesNoDuncanSwisherResidualTargetIsTrue A
    }

------------------------------------------------------------------------
-- 5. Source receipts and attribution firewalls.
------------------------------------------------------------------------

integralTateBoundary :
  Tate.PBIntegralTateBridgeBoundary
integralTateBoundary =
  Tate.canonicalPBIntegralTateBridgeBoundary

dvrBrauerBoundary :
  DVR.DVRLengthBrauerCutsetBoundary
dvrBrauerBoundary =
  DVR.canonicalDVRLengthBrauerCutsetBoundary

data CarnahanUranoGeneralConjectureProvesPBSpecies : Set where
data GreenRingFrameworkDeterminesSectorDecomposition : Set where
data DVRLengthAutomaticallyDefinesRingSpecies : Set where
data SectorWeightsMayBeImportedFromMonsterGap : Set where
data SelectedCaseProofCoversTwoBThreeBBadLevel : Set where

carnahanUranoGeneralConjectureDoesNotProvePBSpecies :
  CarnahanUranoGeneralConjectureProvesPBSpecies -> ⊥
carnahanUranoGeneralConjectureDoesNotProvePBSpecies ()

greenRingFrameworkDoesNotDetermineSectorDecomposition :
  GreenRingFrameworkDeterminesSectorDecomposition -> ⊥
greenRingFrameworkDoesNotDetermineSectorDecomposition ()

dvrLengthDoesNotAutomaticallyDefineRingSpecies :
  DVRLengthAutomaticallyDefinesRingSpecies -> ⊥
dvrLengthDoesNotAutomaticallyDefineRingSpecies ()

sectorWeightsMayNotBeImportedFromMonsterGap :
  SectorWeightsMayBeImportedFromMonsterGap -> ⊥
sectorWeightsMayNotBeImportedFromMonsterGap ()

selectedCaseProofDoesNotCoverTwoBThreeBBadLevel :
  SelectedCaseProofCoversTwoBThreeBBadLevel -> ⊥
selectedCaseProofDoesNotCoverTwoBThreeBBadLevel ()

------------------------------------------------------------------------
-- 6. Live theorem wall.
------------------------------------------------------------------------

data PBGreenRingSectorSpeciesAuthorityInhabited : Set where

pbGreenRingSectorSpeciesStillOpen :
  PBGreenRingSectorSpeciesAuthorityInhabited -> ⊥
pbGreenRingSectorSpeciesStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record PBGreenRingSectorSpeciesCutsetBoundary : Set where
  constructor pb-green-ring-sector-species-cutset-boundary
  field
    integralGroupRingHauptmodulFrameworkSourced : Bool
    frameworkIsGeneralConjectureRatherThanFullTheorem : Bool
    selectedCaseProofDoesNotCoverRequiredPBLocalization : Bool
    uranoFiniteLengthBrauerFrameworkSourced : Bool
    sectorSpeciesAuthoritySpecified : Bool
    adapterToPreferredDVRPaymentOwned : Bool
    adapterToPreferredCorrectedValuationOwned : Bool
    adapterToGlobalDVRBrauerAuthorityOwned : Bool
    sectorSpeciesAuthorityInhabited : Bool
    carnahanUranoCreditedWithDASHISectorWeights : Bool
    uranoCreditedWithIgusaSectorDecomposition : Bool
    targetNumbersUsedToDefineSpecies : Bool
    attributionFirewallPreserved : Bool

canonicalPBGreenRingSectorSpeciesCutsetBoundary :
  PBGreenRingSectorSpeciesCutsetBoundary
canonicalPBGreenRingSectorSpeciesCutsetBoundary =
  pb-green-ring-sector-species-cutset-boundary
    true true true true true true true true false false false false true
