module DASHI.Physics.Closure.NSTriadKNStage3ConstructiveSeriesOrientationIntegration where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Martin Lundfall; Zachary Murray; Viktor Csimma; Robbert Krebbers;
-- Bas Spitters; Loukas Grafakos; Rodolfo H. Torres; Terence Tao; Jean-Michel
-- Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; DASHI repository
-- contributors.
-- Title: "Stage-3 constructive-series candidate and literal Schur-shell
-- substitution integration".
-- Venue/year: Reals-in-agda formal development, 2015; Constructive Analysis in
-- the Agda Proof Assistant, 2022; Logical Methods in Computer Science 9(1:1),
-- 2013; Journal of Functional Analysis 187 (2001), 1--24 and 199 (2003),
-- 379--385; Annales scientifiques de l'Ecole Normale Superieure 14 (1981);
-- Springer, 2011; DASHI formal development, 2026.
-- DOI: 10.2168/LMCS-9(1:1)2013; 10.1006/jfan.2001.3804;
-- 10.1016/S0022-1236(02)00098-8; 10.24033/asens.1404;
-- 10.1007/978-3-642-16830-7; Murray arXiv:2205.08354 has no DOI; no DOI
-- located for Reals-in-agda; the integration receipt has no DOI.
-- Uses: constructive-real candidate comparison, literal power-law Schur
-- orientation, the closed physical exponent identity, exact shell substitution,
-- and the symbolic affine epsilon-family substitution.
-- Relationship: closes the three symbolic output-relocation affine rows and all
-- six epsilon slopes, and records Murray/Csimma as the preferred live Agda
-- candidate. It does not claim a constructive-real dyadic-tail theorem, DASHI
-- numeric affine bases/directions, or a positive epsilon interval.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNConstructiveRealCandidateComparison as Reals
import DASHI.Physics.Closure.NSTriadKNGrafakosTorresPowerLawOrientation as Orientation
import DASHI.Physics.Closure.NSTriadKNOutputRelocationWeightedExponentIdentity as Weighted
import DASHI.Physics.Closure.NSTriadKNOutputRelocationLiteralShellSubstitution as Shells
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAffineFamilySubstitution as AffineRows

record ConstructiveSeriesOrientationReceipt : Set where
  constructor receipt
  field
    bothConstructiveCandidatesRecorded : Reals.bothAgdaCandidatesRecorded ≡ true
    lundfallLegacyPinRecorded : Reals.lundfallLegacyStdlibPinRecorded ≡ true
    lundfallDirectImportDeprioritized : Reals.lundfallDirectImportDeprioritized ≡ true
    murrayPreferredLiveCandidate : Reals.murrayCsimmaPreferredLiveCandidate ≡ true
    coqReferenceArchitectureRecorded : Reals.coqReferenceArchitectureRecorded ≡ true
    candidateComparisonDoesNotPromoteProof : Reals.candidateComparisonChangesProofStatus ≡ false
    physicalExponentIdentityClosed : Weighted.outputRelocationWeightedExponentIdentityClosed ≡ true
    schurSignOrientationClosed : Orientation.grafakosTorresSignOrientationClosed ≡ true
    literalThreeConditionTemplateClosed : Orientation.literalThreeConditionTemplateClosed ≡ true
    literalShellSubstitutionClosed : Shells.outputRelocationLiteralShellSubstitutionClosed ≡ true
    threeConditionAffineRowsClosed : Shells.outputRelocationThreeConditionAffineRowsClosed ≡ true
    affineFamilySubstitutionClosed : AffineRows.outputRelocationAffineFamilySubstitutionClosed ≡ true
    sixEpsilonSlopesClosed : AffineRows.outputRelocationSixEpsilonSlopesClosed ≡ true
    mrChicoImportStillClosedOff : Reals.mrChicoReadyForStage3Import ≡ false
    murrayImportStillOpen : Reals.murrayBishopReadyForStage3Import ≡ false
    constructiveTailStillOpen : Shells.outputRelocationConstructiveDyadicTailClosed ≡ false
    numericBasesDirectionsStillOpen : AffineRows.outputRelocationNumericBasesAndDirectionsSupplied ≡ false
    positiveEpsilonStillOpen : AffineRows.outputRelocationCommonPositiveEpsilonProved ≡ false
    checkAStillOpen : AffineRows.outputRelocationCheckAClosed ≡ false

open ConstructiveSeriesOrientationReceipt public

constructiveSeriesOrientationReceipt : ConstructiveSeriesOrientationReceipt
constructiveSeriesOrientationReceipt = receipt
  Reals.bothAgdaCandidatesRecordedIsTrue
  Reals.lundfallLegacyStdlibPinRecordedIsTrue
  Reals.lundfallDirectImportDeprioritizedIsTrue
  Reals.murrayCsimmaPreferredLiveCandidateIsTrue
  Reals.coqReferenceArchitectureRecordedIsTrue
  Reals.candidateComparisonChangesProofStatusIsFalse
  Weighted.outputRelocationWeightedExponentIdentityClosedIsTrue
  Orientation.grafakosTorresSignOrientationClosedIsTrue
  Orientation.literalThreeConditionTemplateClosedIsTrue
  Shells.outputRelocationLiteralShellSubstitutionClosedIsTrue
  Shells.outputRelocationThreeConditionAffineRowsClosedIsTrue
  AffineRows.outputRelocationAffineFamilySubstitutionClosedIsTrue
  AffineRows.outputRelocationSixEpsilonSlopesClosedIsTrue
  Reals.mrChicoReadyForStage3ImportIsFalse
  Reals.murrayBishopReadyForStage3ImportIsFalse
  Shells.outputRelocationConstructiveDyadicTailClosedIsFalse
  AffineRows.outputRelocationNumericBasesAndDirectionsSuppliedIsFalse
  AffineRows.outputRelocationCommonPositiveEpsilonProvedIsFalse
  AffineRows.outputRelocationCheckAClosedIsFalse

constructiveRealCandidateComparisonClosed : Bool
constructiveRealCandidateComparisonClosed = true

literalOutputRelocationShellSubstitutionClosed : Bool
literalOutputRelocationShellSubstitutionClosed = true

outputRelocationAffineEpsilonSlopesClosed : Bool
outputRelocationAffineEpsilonSlopesClosed = true

nextLeafIsNumericBasesDirectionsAndDyadicTail : Bool
nextLeafIsNumericBasesDirectionsAndDyadicTail = true

outputRelocationCheckAClosed : Bool
outputRelocationCheckAClosed = false

constructiveRealCandidateComparisonClosedIsTrue : constructiveRealCandidateComparisonClosed ≡ true
constructiveRealCandidateComparisonClosedIsTrue = refl

literalOutputRelocationShellSubstitutionClosedIsTrue : literalOutputRelocationShellSubstitutionClosed ≡ true
literalOutputRelocationShellSubstitutionClosedIsTrue = refl

outputRelocationAffineEpsilonSlopesClosedIsTrue : outputRelocationAffineEpsilonSlopesClosed ≡ true
outputRelocationAffineEpsilonSlopesClosedIsTrue = refl

nextLeafIsNumericBasesDirectionsAndDyadicTailIsTrue : nextLeafIsNumericBasesDirectionsAndDyadicTail ≡ true
nextLeafIsNumericBasesDirectionsAndDyadicTailIsTrue = refl

outputRelocationCheckAClosedIsFalse : outputRelocationCheckAClosed ≡ false
outputRelocationCheckAClosedIsFalse = refl
