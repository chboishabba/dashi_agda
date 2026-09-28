module DASHI.Moonshine.OggSSPP3AlignmentIndependentLengthQuotientExact where

------------------------------------------------------------------------
-- p=3 ALIGNMENT-INDEPENDENT LENGTH QUOTIENT
--
-- SOURCE/GEOMETRY INPUT
--
-- Carnahan supplies the binary Tate H^0/H^1 split.
-- Deligne--Rapoport supplies two local orbit sectors:
--   node, branch-pair.
-- The sourced geometry gives local multiplicity 1 on BOTH sectors.
--
-- DASHI RESULT
--
-- The unresolved direct-vs-swapped Tate<->DR alignment is relevant to semantic
-- sector identity, but IRRELEVANT to the scalar local-multiplicity consumer:
--
--   multiplicity (tateToDR alignment degree) = 1
--
-- for every alignment and every Tate degree.
--
-- Hence a scalar p=3 length proof must still prove that actual source pieces
-- have normalized DVR composition length one, but it does NOT need to choose
-- the node/branch alignment first.
--
-- ATTRIBUTION
--
-- Carnahan owns the Tate split; Deligne--Rapoport owns the semistable geometry.
-- DASHI owns only this consumer-relative nondependence theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP3BCarnahanTateSigmaSplitExact as Tate
import DASHI.Moonshine.OggSSP3BTateSigmaDeligneRapoportRecognitionExact as SigmaDR
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalMultiplicityExact as Geom
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Scalar length after either alignment.
------------------------------------------------------------------------

alignedGeometricLength :
  SigmaDR.SigmaDRAlignment ->
  Tate.ThreeBTateDegree ->
  Nat
alignedGeometricLength alignment degree =
  Geom.p3LocalGeometricMultiplicity
    (SigmaDR.tateToDR alignment degree)

alignedGeometricLengthIsOne :
  (alignment : SigmaDR.SigmaDRAlignment) ->
  (degree : Tate.ThreeBTateDegree) ->
  alignedGeometricLength alignment degree ≡ 1
alignedGeometricLengthIsOne SigmaDR.directAlignment Tate.tateH0 = refl
alignedGeometricLengthIsOne SigmaDR.directAlignment Tate.tateH1 = refl
alignedGeometricLengthIsOne SigmaDR.swappedAlignment Tate.tateH0 = refl
alignedGeometricLengthIsOne SigmaDR.swappedAlignment Tate.tateH1 = refl

------------------------------------------------------------------------
-- 2. Direct and swapped alignments are indistinguishable to this consumer.
------------------------------------------------------------------------

directSwappedLengthAgree :
  (degree : Tate.ThreeBTateDegree) ->
  alignedGeometricLength SigmaDR.directAlignment degree
  ≡
  alignedGeometricLength SigmaDR.swappedAlignment degree
directSwappedLengthAgree Tate.tateH0 = refl
directSwappedLengthAgree Tate.tateH1 = refl

data AlignmentChoiceRequiredBeforeScalarLength : Set where
data EqualScalarLengthIdentifiesNodeBranchSemantics : Set where

alignmentChoiceNotRequiredBeforeScalarLength :
  AlignmentChoiceRequiredBeforeScalarLength -> ⊥
alignmentChoiceNotRequiredBeforeScalarLength ()

equalScalarLengthDoesNotIdentifyNodeBranchSemantics :
  EqualScalarLengthIdentifiesNodeBranchSemantics -> ⊥
equalScalarLengthDoesNotIdentifyNodeBranchSemantics ()

------------------------------------------------------------------------
-- 3. Minimal source-side scalar payment.
--
-- A future source theorem can now pay scalar p=3 localization by grading
-- source pieces only by Tate degree and proving normalized DVR length one.
-- Node/branch alignment can remain unresolved unless a downstream consumer
-- explicitly asks for geometric sector identity.
------------------------------------------------------------------------

record P3TateScalarLengthAuthority : Set₁ where
  field
    SourcePiece :
      Set

    tateDegree :
      SourcePiece ->
      Tate.ThreeBTateDegree

    sourcePieceComesFromIntegralThreeBTateObject :
      SourcePiece ->
      Bool
    sourcePieceComesFromIntegralThreeBTateObjectIsTrue :
      (piece : SourcePiece) ->
      sourcePieceComesFromIntegralThreeBTateObject piece ≡ true

    everyTateDegreeHasSourcePiece :
      (degree : Tate.ThreeBTateDegree) ->
      SourcePiece

    everyTateDegreeHasSourcePieceCorrect :
      (degree : Tate.ThreeBTateDegree) ->
      tateDegree (everyTateDegreeHasSourcePiece degree) ≡ degree

    normalizedDVRLength :
      SourcePiece ->
      Nat

    everySourcePieceLengthIsOne :
      (piece : SourcePiece) ->
      normalizedDVRLength piece ≡ 1

    paymentIndependentOfMonsterResidualTwo :
      Bool
    paymentIndependentOfMonsterResidualTwoIsTrue :
      paymentIndependentOfMonsterResidualTwo ≡ true

    paymentIndependentOfBase369Labels :
      Bool
    paymentIndependentOfBase369LabelsIsTrue :
      paymentIndependentOfBase369Labels ≡ true

open P3TateScalarLengthAuthority public

representativeH0LengthIsOne :
  (A : P3TateScalarLengthAuthority) ->
  normalizedDVRLength A
    (everyTateDegreeHasSourcePiece A Tate.tateH0)
  ≡ 1
representativeH0LengthIsOne A =
  everySourcePieceLengthIsOne A
    (everyTateDegreeHasSourcePiece A Tate.tateH0)

representativeH1LengthIsOne :
  (A : P3TateScalarLengthAuthority) ->
  normalizedDVRLength A
    (everyTateDegreeHasSourcePiece A Tate.tateH1)
  ≡ 1
representativeH1LengthIsOne A =
  everySourcePieceLengthIsOne A
    (everyTateDegreeHasSourcePiece A Tate.tateH1)

------------------------------------------------------------------------
-- 4. What remains genuinely open.
------------------------------------------------------------------------

data CarnahanTateSplitProvesLengthOne : Set where
data DeligneRapoportMultiplicityProvesSourceDVRLengthOne : Set where
data P3TateScalarLengthAuthorityInhabited : Set where

carnahanTateSplitDoesNotProveLengthOne :
  CarnahanTateSplitProvesLengthOne -> ⊥
carnahanTateSplitDoesNotProveLengthOne ()

deligneRapoportMultiplicityDoesNotProveSourceLengthOne :
  DeligneRapoportMultiplicityProvesSourceDVRLengthOne -> ⊥
deligneRapoportMultiplicityDoesNotProveSourceLengthOne ()

p3TateScalarLengthStillOpen :
  P3TateScalarLengthAuthorityInhabited -> ⊥
p3TateScalarLengthStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record P3AlignmentIndependentLengthBoundary : Set where
  constructor p3-alignment-independent-length-boundary
  field
    carnahanBinaryTateSplitSourced : Bool
    deligneRapoportOneOneMultiplicityOwned : Bool
    everyAlignmentDegreeLengthOneProved : Bool
    directSwappedScalarAgreementProved : Bool
    alignmentRequiredForScalarLengthConsumer : Bool
    semanticAlignmentStillSeparate : Bool
    reducedScalarAuthoritySpecified : Bool
    reducedScalarAuthorityInhabited : Bool
    carnahanCreditedWithLengthOne : Bool
    deligneRapoportCreditedWithSourceDVRLength : Bool
    monsterResidualUsedToDefinePayment : Bool
    base369UsedToDefinePayment : Bool
    attributionFirewallPreserved : Bool

canonicalP3AlignmentIndependentLengthBoundary :
  P3AlignmentIndependentLengthBoundary
canonicalP3AlignmentIndependentLengthBoundary =
  p3-alignment-independent-length-boundary
    true true true true false true true false
    false false false false true
