module DASHI.Moonshine.OggSSPPBLocalizationSourceCoverageAuditExact where

------------------------------------------------------------------------
-- pB LOCALIZATION SOURCE-COVERAGE AUDIT
--
-- This owner answers a provenance question only:
--
--   which pieces of the terminal pB localization theorem are actually present
--   in the cited literature, and which remain DASHI proof obligations?
--
-- SOURCED:
--
--   Carnahan:
--     integral Monster-stable self-dual form;
--     pB Tate-cohomology / Brauer trace formulas;
--     explicit 2B formula;
--     for 3B, an order-9 3B-pure subgroup decomposition used to embed pieces
--     equivariantly into 3B-fixed vectors.
--
--   Urano:
--     finite-length DVR generalized Brauer characters;
--     composition-factor definition / additivity;
--     Tate super-Brauer character as trace-function combination.
--
--   Carnahan--Urano:
--     Green/representation-ring -> Hauptmodul framework/conjecture;
--     selected proved cases, not the required 2B/3B bad-level sector theorem.
--
-- NOT SOURCED BY THOSE RESULTS:
--
--   integral pB Tate object -> prime=level Igusa/inertia sectors;
--   sector pieces -> lengths 3,3,2,1,1 and 1,1;
--   those sector lengths -> corrected Duncan--Swisher Hauptmodul valuation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPSmallPrimePBIntegralTateCohomologyBridgeExact as Tate
import DASHI.Moonshine.OggSSPSmallPrimeDVRLengthBrauerCutsetExact as DVR
import DASHI.Moonshine.OggSSPPBGreenRingSectorSpeciesCutsetExact as Green
import DASHI.Moonshine.OggSSP2BIntegralTateTraceValuationAuditExact as TwoB
import DASHI.Moonshine.OggSSP3B6BIntegralTateTraceValuationAuditExact as ThreeB
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution
import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano2B
import DASHI.Moonshine.OggSSP3BCarnahanOrderNineFixedVectorRefinementExact as Carnahan3B

------------------------------------------------------------------------
-- 1. Existing source-backed receipts.
------------------------------------------------------------------------

integralTateBoundary :
  Tate.PBIntegralTateBridgeBoundary
integralTateBoundary =
  Tate.canonicalPBIntegralTateBridgeBoundary

dvrBrauerBoundary :
  DVR.DVRLengthBrauerCutsetBoundary
dvrBrauerBoundary =
  DVR.canonicalDVRLengthBrauerCutsetBoundary

greenRingBoundary :
  Green.PBGreenRingSectorSpeciesCutsetBoundary
greenRingBoundary =
  Green.canonicalPBGreenRingSectorSpeciesCutsetBoundary

twoBTateAuditBoundary :
  TwoB.TwoBIntegralTateTraceValuationAuditBoundary
twoBTateAuditBoundary =
  TwoB.canonicalTwoBIntegralTateTraceValuationAuditBoundary

threeBTateAuditBoundary :
  ThreeB.ThreeBIntegralTateTraceValuationAuditBoundary
threeBTateAuditBoundary =
  ThreeB.canonicalThreeBIntegralTateTraceValuationAuditBoundary


uranoTwoBParityBoundary :
  Urano2B.TwoBUranoIntegralModuleParityBoundary
uranoTwoBParityBoundary =
  Urano2B.canonicalTwoBUranoIntegralModuleParityBoundary

carnahanThreeBRefinementBoundary :
  Carnahan3B.ThreeBCarnahanOrderNineRefinementBoundary
carnahanThreeBRefinementBoundary =
  Carnahan3B.canonicalThreeBCarnahanOrderNineRefinementBoundary

------------------------------------------------------------------------
-- 2. Unsupported promotions are explicit empty types.
------------------------------------------------------------------------

data CarnahanTraceFormulaIsIgusaSectorDecomposition : Set where
data ThreeBPureOrderNineDecompositionIsNodeBranchDecomposition : Set where
data UranoCompositionFactorTheoryDeterminesDASHISectorLengths : Set where
data GreenRingConjectureProvesPBLocalizedSpecies : Set where
data RawTateCoefficientDepthIsSectorCompositionLength : Set where

carnahanTraceFormulaDoesNotCreateIgusaSectors :
  CarnahanTraceFormulaIsIgusaSectorDecomposition -> ⊥
carnahanTraceFormulaDoesNotCreateIgusaSectors ()

threeBPureOrderNineDoesNotCreateNodeBranchDecomposition :
  ThreeBPureOrderNineDecompositionIsNodeBranchDecomposition -> ⊥
threeBPureOrderNineDoesNotCreateNodeBranchDecomposition ()

uranoTheoryDoesNotDetermineDASHISectorLengths :
  UranoCompositionFactorTheoryDeterminesDASHISectorLengths -> ⊥
uranoTheoryDoesNotDetermineDASHISectorLengths ()

greenRingConjectureDoesNotProvePBLocalizedSpecies :
  GreenRingConjectureProvesPBLocalizedSpecies -> ⊥
greenRingConjectureDoesNotProvePBLocalizedSpecies ()

rawCoefficientDepthDoesNotBecomeSectorLength :
  RawTateCoefficientDepthIsSectorCompositionLength -> ⊥
rawCoefficientDepthDoesNotBecomeSectorLength ()

------------------------------------------------------------------------
-- 3. Exact source-coverage matrix.
------------------------------------------------------------------------

record PBLocalizationSourceCoverage : Set where
  constructor pb-localization-source-coverage
  field
    carnahanIntegralMonsterFormSourced : Bool
    carnahanPBIntegralTateObjectSourced : Bool
    carnahanTwoBTraceFormulaSourced : Bool
    carnahanThreeBTraceFormulaSourced : Bool
    carnahanThreeBPureOrderNineDecompositionSourced : Bool
    carnahanThreeBFixedVectorEquivariantRefinementSourced : Bool
    uranoTwoBParityExclusionsSourced : Bool
    uranoTwoBGreenFunctionalT4ASourced : Bool

    uranoFiniteLengthDVRBrauerTheorySourced : Bool
    uranoCompositionFactorAdditivitySourced : Bool
    uranoTateTraceCombinationSourced : Bool

    carnahanUranoGreenRingHauptmodulFrameworkSourced : Bool
    carnahanUranoGeneralStatementIsConjectural : Bool
    carnahanUranoSelectedCasesDoNotPayPBLocalization : Bool

    integralTateToPrimeLevelIgusaSectorLocalizationSourced : Bool
    p2SectorLengthsThreeThreeTwoOneOneSourced : Bool
    p3SectorLengthsOneOneSourced : Bool
    sectorLengthGreenSpeciesForBadLevelHauptmodulSourced : Bool
    correctedDuncanSwisherValuationAssemblySourced : Bool

    attributionFirewallPreserved : Bool

canonicalPBLocalizationSourceCoverage :
  PBLocalizationSourceCoverage
canonicalPBLocalizationSourceCoverage =
  pb-localization-source-coverage
    true true true true true true true true
    true true true
    true true true
    false false false false false
    true

------------------------------------------------------------------------
-- 4. The live missing source/proof surface.
------------------------------------------------------------------------

record PBLocalizationMissingProofSurface : Set where
  constructor pb-localization-missing-proof-surface
  field
    needIntegralTateToIgusaSectorFunctor : Bool
    needTwoBSourcePieceToInertiaSectorRefinement : Bool
    needThreeBH3PieceToNodeBranchRefinement : Bool
    needSectorwiseFiniteLengthComputation : Bool
    needGreenSpeciesCompatibility : Bool
    needBadLevelHauptmodulAssembly : Bool

canonicalPBLocalizationMissingProofSurface :
  PBLocalizationMissingProofSurface
canonicalPBLocalizationMissingProofSurface =
  pb-localization-missing-proof-surface
    true true true true true true

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction
