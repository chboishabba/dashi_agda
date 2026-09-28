module DASHI.Moonshine.OggSSPPBTerminalLocalizationPrimewiseGapExact where

------------------------------------------------------------------------
-- PRIMEWISE GAP ANALYSIS FOR THE TERMINAL pB LOCALIZATION THEOREM
--
-- This module does NOT add a new localization ontology.  It decomposes the
-- single terminal theorem wall by source coverage.
--
-- p=2 source side:
--   sourced:
--     * integral 2B setting;
--     * Urano parity exclusions;
--     * Urano T_4A Green functional;
--     * finite-length DVR Brauer theory.
--   not sourced:
--     * refinement from 2B source pieces to five inertia sectors;
--     * sector lengths 3,3,2,1,1;
--     * prime-level Igusa/inertia localization.
--
-- p=3 source side:
--   sourced:
--     * integral 3B setting;
--     * Carnahan pure-order-nine/H_3 refinement;
--     * equivariant embedding into 3B fixed vectors;
--     * finite-length DVR Brauer theory.
--   not sourced:
--     * refinement from H_3 pieces to node/branch sectors;
--     * sector lengths 1,1 as source composition lengths;
--     * prime-level Igusa/Deligne--Rapoport localization.
--
-- Therefore p=3 is strictly closer at the source-piece level, but BOTH primes
-- still need the same kind of target-independent geometric localization theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPPBLocalizationSourceCoverageAuditExact as Coverage
import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano2B
import DASHI.Moonshine.OggSSP3BCarnahanOrderNineFixedVectorRefinementExact as Carnahan3B
import DASHI.Moonshine.OggSSP3BCarnahanTateSigmaSplitExact as Tate3B
import DASHI.Moonshine.OggSSP3BTateSigmaDeligneRapoportRecognitionExact as SigmaDR
import DASHI.Moonshine.OggSSPP3H3TateSigmaPartitionFactorizationExact as P3Factor
import DASHI.Moonshine.OggSSPSmallPrimeDVRLengthBrauerCutsetExact as DVR
import DASHI.Moonshine.OggSSPPBTerminalPrimeLevelLocalizationTheoremExact as Terminal
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Primewise source-payment ledgers.
------------------------------------------------------------------------

record P2TerminalSourceGap : Set where
  constructor p2-terminal-source-gap
  field
    integralTwoBSourceObjectSourced : Bool
    uranoParityExclusionsSourced : Bool
    uranoT4AGreenFunctionalSourced : Bool
    finiteLengthDVRBrauerTheorySourced : Bool

    twoBToFiveInertiaSectorRefinementSourced : Bool
    p2SectorCompositionLengthsThreeThreeTwoOneOneSourced : Bool
    p2PrimeLevelGeometricLocalizationSourced : Bool

canonicalP2TerminalSourceGap :
  P2TerminalSourceGap
canonicalP2TerminalSourceGap =
  p2-terminal-source-gap
    true true true true
    false false false

record P3TerminalSourceGap : Set where
  constructor p3-terminal-source-gap
  field
    integralThreeBSourceObjectSourced : Bool
    carnahanH3RefinementSourced : Bool
    carnahanFixedVectorEmbeddingSourced : Bool
    finiteLengthDVRBrauerTheorySourced : Bool

    h3ToNodeBranchRefinementSourced : Bool
    p3SectorCompositionLengthsOneOneSourced : Bool
    p3PrimeLevelGeometricLocalizationSourced : Bool

canonicalP3TerminalSourceGap :
  P3TerminalSourceGap
canonicalP3TerminalSourceGap =
  p3-terminal-source-gap
    true true true true
    false false false

------------------------------------------------------------------------
-- 2. p=3 has a strictly richer sourced refinement surface.
------------------------------------------------------------------------

data P2AlreadyHasSourceBackedSectorRefinement : Set where
data P3AlreadyHasSourceBackedNodeBranchRefinement : Set where
data SourcePieceEvidenceAloneInhabitsTerminalLocalization : Set where

p2SectorRefinementStillOpen :
  P2AlreadyHasSourceBackedSectorRefinement -> ⊥
p2SectorRefinementStillOpen ()

p3NodeBranchRefinementStillOpen :
  P3AlreadyHasSourceBackedNodeBranchRefinement -> ⊥
p3NodeBranchRefinementStillOpen ()

sourcePieceEvidenceDoesNotInhabitTerminalLocalization :
  SourcePieceEvidenceAloneInhabitsTerminalLocalization -> ⊥
sourcePieceEvidenceDoesNotInhabitTerminalLocalization ()

------------------------------------------------------------------------
-- 3. Reuse exact existing source boundaries rather than re-attributing them.
------------------------------------------------------------------------

uranoBoundary :
  Urano2B.TwoBUranoIntegralModuleParityBoundary
uranoBoundary =
  Urano2B.canonicalTwoBUranoIntegralModuleParityBoundary

carnahanBoundary :
  Carnahan3B.ThreeBCarnahanOrderNineRefinementBoundary
carnahanBoundary =
  Carnahan3B.canonicalThreeBCarnahanOrderNineRefinementBoundary

dvrBoundary :
  DVR.DVRLengthBrauerCutsetBoundary
dvrBoundary =
  DVR.canonicalDVRLengthBrauerCutsetBoundary

coverageBoundary :
  Coverage.PBLocalizationSourceCoverage
coverageBoundary =
  Coverage.canonicalPBLocalizationSourceCoverage

terminalBoundary :
  Terminal.PBTerminalPrimeLevelLocalizationBoundary
terminalBoundary =
  Terminal.canonicalPBTerminalPrimeLevelLocalizationBoundary

------------------------------------------------------------------------
-- 4. Highest-alpha acquisition direction.
------------------------------------------------------------------------

data TerminalAcquisitionDirection : Set where
  proveP2IntegralTateToInertiaSectorRefinement :
    TerminalAcquisitionDirection

  proveP3H3ToNodeBranchRefinement :
    TerminalAcquisitionDirection

  proveSharedPrimeLevelGreenLocalization :
    TerminalAcquisitionDirection

-- p=3 has more source-native structure already paid, but the shared theorem
-- still cannot be completed without the actual prime-level localization.
highestAlphaFirstSubproblem :
  TerminalAcquisitionDirection
highestAlphaFirstSubproblem =
  proveP3H3ToNodeBranchRefinement

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record PBTerminalLocalizationPrimewiseGapBoundary : Set where
  constructor pb-terminal-localization-primewise-gap-boundary
  field
    p2ParityAndGreenFunctionalSourced : Bool
    p2FiveSectorRefinementSourced : Bool
    p2SectorLengthsSourced : Bool

    p3H3AndFixedVectorRefinementSourced : Bool
    p3NodeBranchRefinementSourced : Bool
    p3SectorLengthsSourced : Bool

    p3SourceSideStrictlyCloser : Bool
    sharedPrimeLevelLocalizationStillRequired : Bool
    sourceEvidenceAlreadyInhabitsTerminalTheorem : Bool
    attributionFirewallPreserved : Bool

canonicalPBTerminalLocalizationPrimewiseGapBoundary :
  PBTerminalLocalizationPrimewiseGapBoundary
canonicalPBTerminalLocalizationPrimewiseGapBoundary =
  pb-terminal-localization-primewise-gap-boundary
    true false false
    true false false
    true true false true


------------------------------------------------------------------------
-- 5. Refined p=3 gap after the Carnahan Tate-sigma cross-pollination.
------------------------------------------------------------------------

record P3RefinedTerminalSourceGap : Set where
  constructor p3-refined-terminal-source-gap
  field
    carnahanH3DecompositionSourced : Bool
    carnahanFixedVectorEmbeddingSourced : Bool
    carnahanTateH0H1SplitSourced : Bool
    carnahanSigmaPlusMinusActionSourced : Bool

    h3PiecesGradedByTateDegree : Bool
    sigmaDRRecognitionUpToSwapPaid : Bool
    sigmaDRAlignmentSelectedByPrimeLevelGeometry : Bool
    localizedDVRLengthEqualsSemistableMultiplicity : Bool

    monsterResidualUsedToPayAnyMissingBit : Bool
    base369UsedToPayAnyMissingBit : Bool
    attributionFirewallPreserved : Bool

canonicalP3RefinedTerminalSourceGap :
  P3RefinedTerminalSourceGap
canonicalP3RefinedTerminalSourceGap =
  p3-refined-terminal-source-gap
    true true true true
    false true false false
    false false true

tateSigmaBoundary :
  Tate3B.ThreeBTateSigmaSplitBoundary
tateSigmaBoundary =
  Tate3B.canonicalThreeBTateSigmaSplitBoundary

sigmaDRBoundary :
  SigmaDR.ThreeBTateSigmaDRRecognitionBoundary
sigmaDRBoundary =
  SigmaDR.canonicalThreeBTateSigmaDRRecognitionBoundary

p3PartitionFactorBoundary :
  P3Factor.P3H3TateSigmaPartitionFactorizationBoundary
p3PartitionFactorBoundary =
  P3Factor.canonicalP3H3TateSigmaPartitionFactorizationBoundary
