module DASHI.Moonshine.OggSSP3BCarnahanTateSigmaSplitExact where

------------------------------------------------------------------------
-- 3B CARNAHAN TATE SIGMA SPLIT
--
-- EXTERNAL SOURCE
--
-- Scott Carnahan, "A Self-Dual Integral Form of the Moonshine Module",
-- SIGMA 15 (2019), 030, Corollary 3.25.
--
-- For pB classes with p in {3,5,7,13}, the modular-moonshine formula uses the
-- unique involution sigma in C_M(g)/O_p(C_M(g)) which acts as:
--
--   +1 on Tate H^0(g,V)
--   -1 on Tate H^1(g,V).
--
-- For g in 3B this gives an externally sourced BINARY decomposition of the
-- relevant integral/mod-3 Tate object.
--
-- ATTRIBUTION FIREWALL
--
-- Carnahan owns the H^0/H^1 and sigma +/- split.
-- Carnahan does NOT identify + with the Deligne--Rapoport node,
-- - with the branch-pair orbit, or vice versa.
-- Carnahan does NOT state semistable multiplicity / DVR length one for either
-- sigma sector.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution.
------------------------------------------------------------------------

carnahanSelfDualIntegralForm : Source.AttributedSource
carnahanSelfDualIntegralForm =
  Source.mkDOISource
    "Scott Carnahan"
    "A Self-Dual Integral Form of the Moonshine Module"
    "Symmetry, Integrability and Geometry: Methods and Applications 15, 030"
    "2019"
    "10.3842/SIGMA.2019.030"
    "https://doi.org/10.3842/SIGMA.2019.030"
    Source.academicArticleSource
    "Corollary 3.25 supplies the modular-moonshine Tate H^0/H^1 trace formulas and, for pB with p in {3,5,7,13}, the unique involution sigma acting +1 on H^0 and -1 on H^1; does not identify those two Tate sectors with Deligne-Rapoport node/branch geometry"
    Source.publicAttribution

carnahanTateSigmaSplitSourceAtlas : Source.AttributedSourceAtlas
carnahanTateSigmaSplitSourceAtlas =
  Source.mkSourceAtlas
    "Carnahan 3B Tate sigma split"
    "DASHI.Moonshine.OggSSP3BCarnahanTateSigmaSplitExact"
    (carnahanSelfDualIntegralForm ∷ [])
    "external source owns only the binary Tate grading and sigma action; geometric localization and length comparison remain separate DASHI obligations"

------------------------------------------------------------------------
-- 2. Source-native binary Tate grading.
------------------------------------------------------------------------

data ThreeBTateDegree : Set where
  tateH0 :
    ThreeBTateDegree
  tateH1 :
    ThreeBTateDegree

data SigmaEigenvalue : Set where
  sigmaPlus :
    SigmaEigenvalue
  sigmaMinus :
    SigmaEigenvalue

sigmaEigenvalueOfDegree :
  ThreeBTateDegree ->
  SigmaEigenvalue
sigmaEigenvalueOfDegree tateH0 = sigmaPlus
sigmaEigenvalueOfDegree tateH1 = sigmaMinus

data ThreeBTateSector : Set where
  threeBTateSector :
    ThreeBTateDegree ->
    ThreeBTateSector

sectorDegree :
  ThreeBTateSector ->
  ThreeBTateDegree
sectorDegree (threeBTateSector degree) = degree

sectorSigma :
  ThreeBTateSector ->
  SigmaEigenvalue
sectorSigma sector =
  sigmaEigenvalueOfDegree (sectorDegree sector)

h0Sector : ThreeBTateSector
h0Sector = threeBTateSector tateH0

h1Sector : ThreeBTateSector
h1Sector = threeBTateSector tateH1

h0SigmaIsPlus :
  sectorSigma h0Sector ≡ sigmaPlus
h0SigmaIsPlus = refl

h1SigmaIsMinus :
  sectorSigma h1Sector ≡ sigmaMinus
h1SigmaIsMinus = refl

h0SectorNotH1Sector :
  h0Sector ≡ h1Sector -> ⊥
h0SectorNotH1Sector ()

------------------------------------------------------------------------
-- 3. Exact source-owned scope.
------------------------------------------------------------------------

record CarnahanThreeBTateSigmaReceipt : Set where
  constructor carnahan-three-b-tate-sigma-receipt
  field
    threeBUsesPrimeBFormula :
      Bool
    threeBUsesPrimeBFormulaIsTrue :
      threeBUsesPrimeBFormula ≡ true

    tateH0SectorExists :
      Bool
    tateH0SectorExistsIsTrue :
      tateH0SectorExists ≡ true

    tateH1SectorExists :
      Bool
    tateH1SectorExistsIsTrue :
      tateH1SectorExists ≡ true

    uniqueCentralizerQuotientInvolutionUsed :
      Bool
    uniqueCentralizerQuotientInvolutionUsedIsTrue :
      uniqueCentralizerQuotientInvolutionUsed ≡ true

    sigmaActsPlusOnH0 :
      Bool
    sigmaActsPlusOnH0IsTrue :
      sigmaActsPlusOnH0 ≡ true

    sigmaActsMinusOnH1 :
      Bool
    sigmaActsMinusOnH1IsTrue :
      sigmaActsMinusOnH1 ≡ true

    sourceIdentifiesSigmaSectorsWithDRNodeBranch :
      Bool

    sourceProvesSigmaSectorLengthOne :
      Bool

canonicalCarnahanThreeBTateSigmaReceipt :
  CarnahanThreeBTateSigmaReceipt
canonicalCarnahanThreeBTateSigmaReceipt =
  carnahan-three-b-tate-sigma-receipt
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false
    false

------------------------------------------------------------------------
-- 4. Explicit non-promotion rules.
------------------------------------------------------------------------

data SigmaPlusIsDeligneRapoportNodeBySource : Set where
data SigmaMinusIsDeligneRapoportBranchBySource : Set where
data SigmaSplitDeterminesSemistableMultiplicity : Set where
data TateDegreeDeterminesIgusaLocalization : Set where

sigmaPlusNotIdentifiedWithNodeByCarnahan :
  SigmaPlusIsDeligneRapoportNodeBySource -> ⊥
sigmaPlusNotIdentifiedWithNodeByCarnahan ()

sigmaMinusNotIdentifiedWithBranchByCarnahan :
  SigmaMinusIsDeligneRapoportBranchBySource -> ⊥
sigmaMinusNotIdentifiedWithBranchByCarnahan ()

sigmaSplitDoesNotDetermineSemistableMultiplicity :
  SigmaSplitDeterminesSemistableMultiplicity -> ⊥
sigmaSplitDoesNotDetermineSemistableMultiplicity ()

tateDegreeDoesNotDetermineIgusaLocalization :
  TateDegreeDeterminesIgusaLocalization -> ⊥
tateDegreeDoesNotDetermineIgusaLocalization ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record ThreeBTateSigmaSplitBoundary : Set where
  constructor three-b-tate-sigma-split-boundary
  field
    carnahanExplicitlyAttributed : Bool
    tateH0H1BinarySplitSourced : Bool
    sigmaPlusMinusActionSourced : Bool
    sourceNativeTwoSectorClassifierAvailable : Bool
    nodeBranchIdentificationSourced : Bool
    sectorLengthOneSourced : Bool
    attributionFirewallPreserved : Bool

canonicalThreeBTateSigmaSplitBoundary :
  ThreeBTateSigmaSplitBoundary
canonicalThreeBTateSigmaSplitBoundary =
  three-b-tate-sigma-split-boundary
    true true true true false false true
