module DASHI.Physics.Closure.NSTriadKNStage3ConstructiveSeriesOrientationIntegration where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Martin Lundfall; Zachary Murray; Viktor Csimma; Robbert Krebbers;
-- Bas Spitters; Loukas Grafakos; Rodolfo H. Torres; Terence Tao; Minghui Liu;
-- Gabor Pataki; Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael
-- Danchin; DASHI repository contributors.
-- Title: "Stage-3 constructive-series candidate, literal Schur-shell
-- substitution, and affine infeasibility integration".
-- Venue/year: Reals-in-agda formal development, 2015; Constructive Analysis in
-- the Agda Proof Assistant, 2022; Logical Methods in Computer Science 9(1:1),
-- 2013; Journal of Functional Analysis 187 (2001), 1--24 and 199 (2003),
-- 379--385; Mathematical Programming / arXiv, 2015--2017; Annales
-- scientifiques de l'Ecole Normale Superieure 14 (1981); Springer, 2011;
-- DASHI formal development, 2026.
-- DOI: 10.2168/LMCS-9(1:1)2013; 10.1006/jfan.2001.3804;
-- 10.1016/S0022-1236(02)00098-8; 10.48550/arXiv.1507.00290;
-- 10.24033/asens.1404; 10.1007/978-3-642-16830-7; Murray
-- arXiv:2205.08354 has no DOI; no DOI located for Reals-in-agda; the
-- integration receipt has no DOI.
-- Uses: constructive-real candidate comparison, literal power-law Schur
-- orientation, the closed physical exponent identity, exact shell
-- substitution, the symbolic affine epsilon-family substitution, and the
-- exact primal/dual classification of the current homogeneity-preserving
-- ansatz.
-- Relationship: closes the highest-alpha algebraic decision.  The current
-- ansatz is proved infeasible before constructive dyadic summation is built.
-- This does not falsify relaxed, condition-dependent, or non-affine weights.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNConstructiveRealCandidateComparison as Reals
import DASHI.Physics.Closure.NSTriadKNGrafakosTorresPowerLawOrientation as Orientation
import DASHI.Physics.Closure.NSTriadKNOutputRelocationWeightedExponentIdentity as Weighted
import DASHI.Physics.Closure.NSTriadKNOutputRelocationLiteralShellSubstitution as Shells
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAffineFamilySubstitution as AffineRows
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAffineFarkasDecision as Decision

record ConstructiveSeriesOrientationReceipt : Set where
  constructor receipt
  field
    bothConstructiveCandidatesRecorded : Reals.bothAgdaCandidatesRecorded ≡ true
    lundfallLegacyPinRecorded : Reals.lundfallLegacyStdlibPinRecorded ≡ true
    lundfallDirectImportDeprioritized :
      Reals.lundfallDirectImportDeprioritized ≡ true
    murrayPreferredLiveCandidate :
      Reals.murrayCsimmaPreferredLiveCandidate ≡ true
    coqReferenceArchitectureRecorded :
      Reals.coqReferenceArchitectureRecorded ≡ true
    candidateComparisonDoesNotPromoteProof :
      Reals.candidateComparisonChangesProofStatus ≡ false
    physicalExponentIdentityClosed :
      Weighted.outputRelocationWeightedExponentIdentityClosed ≡ true
    schurSignOrientationClosed :
      Orientation.grafakosTorresSignOrientationClosed ≡ true
    literalThreeConditionTemplateClosed :
      Orientation.literalThreeConditionTemplateClosed ≡ true
    literalShellSubstitutionClosed :
      Shells.outputRelocationLiteralShellSubstitutionClosed ≡ true
    threeConditionAffineRowsClosed :
      Shells.outputRelocationThreeConditionAffineRowsClosed ≡ true
    affineFamilySubstitutionClosed :
      AffineRows.outputRelocationAffineFamilySubstitutionClosed ≡ true
    sixEpsilonSlopesClosed :
      AffineRows.outputRelocationSixEpsilonSlopesClosed ≡ true
    baseSystemClassified :
      Decision.outputRelocationBaseSystemClassified ≡ true
    directionSystemClassified :
      Decision.outputRelocationDirectionSystemClassified ≡ true
    commonIntervalComputed :
      Decision.outputRelocationCommonIntervalComputed ≡ true
    currentAffineAnsatzInfeasible :
      Decision.currentHomogeneityPreservingAffineAnsatzInfeasible ≡ true
    noOverbroadFalsificationClaim :
      Decision.allPossibleThreeWeightAnsatzesInfeasible ≡ false
    constructiveTailStillOpen :
      Shells.outputRelocationConstructiveDyadicTailClosed ≡ false
    admissibleNumericFamilyUnavailable :
      AffineRows.outputRelocationNumericBasesAndDirectionsSupplied ≡ false
    positiveIntervalIsEmpty :
      Decision.outputRelocationCommonPositiveIntervalNonempty ≡ false
    symbolicCheckAFails : Decision.outputRelocationSymbolicCheckA ≡ false

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
  Decision.outputRelocationBaseSystemClassifiedIsTrue
  Decision.outputRelocationDirectionSystemClassifiedIsTrue
  Decision.outputRelocationCommonIntervalComputedIsTrue
  Decision.currentHomogeneityPreservingAffineAnsatzInfeasibleIsTrue
  Decision.allPossibleThreeWeightAnsatzesInfeasibleIsFalse
  Shells.outputRelocationConstructiveDyadicTailClosedIsFalse
  AffineRows.outputRelocationNumericBasesAndDirectionsSuppliedIsFalse
  Decision.outputRelocationCommonPositiveIntervalNonemptyIsFalse
  Decision.outputRelocationSymbolicCheckAIsFalse

constructiveRealCandidateComparisonClosed : Bool
constructiveRealCandidateComparisonClosed = true

literalOutputRelocationShellSubstitutionClosed : Bool
literalOutputRelocationShellSubstitutionClosed = true

outputRelocationAffineEpsilonSlopesClosed : Bool
outputRelocationAffineEpsilonSlopesClosed = true

outputRelocationHighestAlphaDecisionClosed : Bool
outputRelocationHighestAlphaDecisionClosed = true

outputRelocationCurrentAffineAnsatzInfeasible : Bool
outputRelocationCurrentAffineAnsatzInfeasible = true

nextLeafIsWeightAnsatzRevision : Bool
nextLeafIsWeightAnsatzRevision = true

nextLeafIsNumericBasesDirectionsAndDyadicTail : Bool
nextLeafIsNumericBasesDirectionsAndDyadicTail = false

outputRelocationCheckAClosed : Bool
outputRelocationCheckAClosed = false

constructiveRealCandidateComparisonClosedIsTrue :
  constructiveRealCandidateComparisonClosed ≡ true
constructiveRealCandidateComparisonClosedIsTrue = refl

literalOutputRelocationShellSubstitutionClosedIsTrue :
  literalOutputRelocationShellSubstitutionClosed ≡ true
literalOutputRelocationShellSubstitutionClosedIsTrue = refl

outputRelocationAffineEpsilonSlopesClosedIsTrue :
  outputRelocationAffineEpsilonSlopesClosed ≡ true
outputRelocationAffineEpsilonSlopesClosedIsTrue = refl

outputRelocationHighestAlphaDecisionClosedIsTrue :
  outputRelocationHighestAlphaDecisionClosed ≡ true
outputRelocationHighestAlphaDecisionClosedIsTrue = refl

outputRelocationCurrentAffineAnsatzInfeasibleIsTrue :
  outputRelocationCurrentAffineAnsatzInfeasible ≡ true
outputRelocationCurrentAffineAnsatzInfeasibleIsTrue = refl

nextLeafIsWeightAnsatzRevisionIsTrue : nextLeafIsWeightAnsatzRevision ≡ true
nextLeafIsWeightAnsatzRevisionIsTrue = refl

nextLeafIsNumericBasesDirectionsAndDyadicTailIsFalse :
  nextLeafIsNumericBasesDirectionsAndDyadicTail ≡ false
nextLeafIsNumericBasesDirectionsAndDyadicTailIsFalse = refl

outputRelocationCheckAClosedIsFalse : outputRelocationCheckAClosed ≡ false
outputRelocationCheckAClosedIsFalse = refl
