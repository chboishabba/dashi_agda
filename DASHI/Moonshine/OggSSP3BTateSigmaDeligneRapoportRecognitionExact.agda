module DASHI.Moonshine.OggSSP3BTateSigmaDeligneRapoportRecognitionExact where

------------------------------------------------------------------------
-- 3B TATE SIGMA <-> DELIGNE--RAPOPORT TWO-SECTOR RECOGNITION
--
-- SOURCE INPUTS
--
-- Carnahan:
--   H^0 / H^1 Tate split, with sigma eigenvalues + / -.
--
-- Deligne--Rapoport:
--   two coarse local orbit sectors at p=3:
--     node orbit,
--     Frobenius/Verschiebung branch-pair orbit.
--
-- DASHI RESULT
--
-- Both sides are exact two-element classifiers, hence there are exactly two
-- source-compatible bijective alignments:
--
--   direct : H^0 -> node,   H^1 -> branch
--   swapped: H^0 -> branch, H^1 -> node.
--
-- The currently cited sources do NOT choose between these alignments.
-- Therefore the binary recognition is paid only UP TO SWAP.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.OggSSP3BCarnahanTateSigmaSplitExact as Tate
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as DR
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Exactly two alignment choices.
------------------------------------------------------------------------

data SigmaDRAlignment : Set where
  directAlignment :
    SigmaDRAlignment
  swappedAlignment :
    SigmaDRAlignment

tateToDR :
  SigmaDRAlignment ->
  Tate.ThreeBTateDegree ->
  DR.P3LocalOrbit
tateToDR directAlignment Tate.tateH0 = DR.nodeOrbit
tateToDR directAlignment Tate.tateH1 = DR.branchOrbit
tateToDR swappedAlignment Tate.tateH0 = DR.branchOrbit
tateToDR swappedAlignment Tate.tateH1 = DR.nodeOrbit

drToTate :
  SigmaDRAlignment ->
  DR.P3LocalOrbit ->
  Tate.ThreeBTateDegree
drToTate directAlignment DR.nodeOrbit = Tate.tateH0
drToTate directAlignment DR.branchOrbit = Tate.tateH1
drToTate swappedAlignment DR.nodeOrbit = Tate.tateH1
drToTate swappedAlignment DR.branchOrbit = Tate.tateH0

tateRoundTrip :
  (alignment : SigmaDRAlignment) ->
  (degree : Tate.ThreeBTateDegree) ->
  drToTate alignment (tateToDR alignment degree) ≡ degree
tateRoundTrip directAlignment Tate.tateH0 = refl
tateRoundTrip directAlignment Tate.tateH1 = refl
tateRoundTrip swappedAlignment Tate.tateH0 = refl
tateRoundTrip swappedAlignment Tate.tateH1 = refl

drRoundTrip :
  (alignment : SigmaDRAlignment) ->
  (sector : DR.P3LocalOrbit) ->
  tateToDR alignment (drToTate alignment sector) ≡ sector
drRoundTrip directAlignment DR.nodeOrbit = refl
drRoundTrip directAlignment DR.branchOrbit = refl
drRoundTrip swappedAlignment DR.nodeOrbit = refl
drRoundTrip swappedAlignment DR.branchOrbit = refl

------------------------------------------------------------------------
-- 2. Each alignment is a complete two-sector recognition.
------------------------------------------------------------------------

directH0ToNode :
  tateToDR directAlignment Tate.tateH0 ≡ DR.nodeOrbit
directH0ToNode = refl

directH1ToBranch :
  tateToDR directAlignment Tate.tateH1 ≡ DR.branchOrbit
directH1ToBranch = refl

swappedH0ToBranch :
  tateToDR swappedAlignment Tate.tateH0 ≡ DR.branchOrbit
swappedH0ToBranch = refl

swappedH1ToNode :
  tateToDR swappedAlignment Tate.tateH1 ≡ DR.nodeOrbit
swappedH1ToNode = refl

------------------------------------------------------------------------
-- 3. Sources do not select the orientation.
------------------------------------------------------------------------

data CarnahanSelectsDirectAlignment : Set where
data CarnahanSelectsSwappedAlignment : Set where
data DeligneRapoportSelectsTateSigmaAlignment : Set where
data CardinalityTwoSelectsAlignment : Set where
data Base369SelectsAlignment : Set where

carnahanDoesNotSelectDirectAlignment :
  CarnahanSelectsDirectAlignment -> ⊥
carnahanDoesNotSelectDirectAlignment ()

carnahanDoesNotSelectSwappedAlignment :
  CarnahanSelectsSwappedAlignment -> ⊥
carnahanDoesNotSelectSwappedAlignment ()

deligneRapoportDoesNotSelectTateSigmaAlignment :
  DeligneRapoportSelectsTateSigmaAlignment -> ⊥
deligneRapoportDoesNotSelectTateSigmaAlignment ()

cardinalityTwoDoesNotSelectAlignment :
  CardinalityTwoSelectsAlignment -> ⊥
cardinalityTwoDoesNotSelectAlignment ()

base369DoesNotSelectAlignment :
  Base369SelectsAlignment -> ⊥
base369DoesNotSelectAlignment ()

------------------------------------------------------------------------
-- 4. A future theorem pays only one bit: which alignment is geometrically
--    correct for the actual localized integral 3B Tate object.
------------------------------------------------------------------------

record SigmaDRAlignmentAuthority : Set where
  constructor sigma-dr-alignment-authority
  field
    alignment :
      SigmaDRAlignment

    alignmentComesFromPrimeLevelLocalization :
      Bool
    alignmentComesFromPrimeLevelLocalizationIsTrue :
      alignmentComesFromPrimeLevelLocalization ≡ true

    alignmentIndependentOfMonsterResidualTwo :
      Bool
    alignmentIndependentOfMonsterResidualTwoIsTrue :
      alignmentIndependentOfMonsterResidualTwo ≡ true

    alignmentIndependentOfBase369Labels :
      Bool
    alignmentIndependentOfBase369LabelsIsTrue :
      alignmentIndependentOfBase369Labels ≡ true

open SigmaDRAlignmentAuthority public

data SigmaDRAlignmentAuthorityInhabited : Set where

alignmentAuthorityStillOpen :
  SigmaDRAlignmentAuthorityInhabited -> ⊥
alignmentAuthorityStillOpen ()

------------------------------------------------------------------------
-- 5. Attribution boundary.
------------------------------------------------------------------------

tateBoundary :
  Tate.ThreeBTateSigmaSplitBoundary
tateBoundary =
  Tate.canonicalThreeBTateSigmaSplitBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record ThreeBTateSigmaDRRecognitionBoundary : Set where
  constructor three-b-tate-sigma-dr-recognition-boundary
  field
    carnahanBinaryTateSplitSourced : Bool
    deligneRapoportBinaryOrbitSurfaceSourced : Bool
    exactDirectBijectionConstructed : Bool
    exactSwappedBijectionConstructed : Bool
    recognitionUpToSwapPaid : Bool
    sourceSelectsAlignment : Bool
    primeLevelLocalizationAlignmentAuthorityInhabited : Bool
    monsterResidualUsedToChooseAlignment : Bool
    base369UsedToChooseAlignment : Bool
    attributionFirewallPreserved : Bool

canonicalThreeBTateSigmaDRRecognitionBoundary :
  ThreeBTateSigmaDRRecognitionBoundary
canonicalThreeBTateSigmaDRRecognitionBoundary =
  three-b-tate-sigma-dr-recognition-boundary
    true true true true true false false false false true
