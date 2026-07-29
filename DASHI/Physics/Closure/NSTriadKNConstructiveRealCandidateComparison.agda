module DASHI.Physics.Closure.NSTriadKNConstructiveRealCandidateComparison where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Martin Lundfall; Zachary Murray; Viktor Csimma; DASHI repository
-- contributors.
-- Title: "Constructive-real candidate comparison for fixed-base dyadic Stage-3
-- series".
-- Venue/year: Reals-in-agda formal development, 2015; Constructive Analysis in
-- the Agda Proof Assistant, 2022; maintained Bishop continuation, 2026; DASHI
-- formal development, 2026.
-- DOI: no DOI located for Lundfall's Reals-in-agda development; Murray thesis
-- arXiv:2205.08354 has no DOI; the repository comparison has no DOI.
-- Uses: candidate API reconnaissance only.
-- Relationship: neither external tree is imported or promoted.  An
-- authoritative pinned Nix/Agda build and explicit fixed-base-two/geometric-tail
-- adapter remain required before either candidate can discharge Stage 3.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record FixedBaseDyadicSeriesCapability : Set₁ where
  field
    Real : Set
    rationalEmbedding : Set
    strictOrder : Set
    twoToRealExponent : Set
    exponentAdditiveLaw : Set
    positiveDyadicPower : Set
    negativeExponentReciprocalLaw : Set
    ratioStrictlyBetweenZeroAndOne : Set
    geometricSeriesConvergence : Set
    explicitTailBound : Set
    cutoffUniformTailConstant : Set

open FixedBaseDyadicSeriesCapability public

record CandidateCompatibilityAudit : Set₁ where
  field
    namespaceLocated : Bool
    pinnedRevisionRecorded : Bool
    standardLibraryVersionRecorded : Bool
    fixedBaseTwoPowerLocated : Bool
    arbitraryRealExponentLocated : Bool
    geometricSeriesTheoremLocated : Bool
    explicitTailModulusLocated : Bool
    authoritativeAgdaBuildPassed : Bool
    stage3AdapterConstructed : Bool

open CandidateCompatibilityAudit public

-- The older Lundfall/MrChico tree establishes a constructive Cauchy-real
-- development, but the present reconnaissance does not establish the exact
-- fixed-base real-exponent and geometric-tail API required here.
mrChicoRealsInAgdaAudit : CandidateCompatibilityAudit
mrChicoRealsInAgdaAudit = record
  { namespaceLocated = true
  ; pinnedRevisionRecorded = false
  ; standardLibraryVersionRecorded = false
  ; fixedBaseTwoPowerLocated = false
  ; arbitraryRealExponentLocated = false
  ; geometricSeriesTheoremLocated = false
  ; explicitTailModulusLocated = false
  ; authoritativeAgdaBuildPassed = false
  ; stage3AdapterConstructed = false
  }

-- Murray/Csimma is already the better-integrated candidate elsewhere in DASHI,
-- but the exact Stage-3 fixed-base-two adapter is still not closed on this
-- branch.
murrayBishopAudit : CandidateCompatibilityAudit
murrayBishopAudit = record
  { namespaceLocated = true
  ; pinnedRevisionRecorded = true
  ; standardLibraryVersionRecorded = false
  ; fixedBaseTwoPowerLocated = false
  ; arbitraryRealExponentLocated = false
  ; geometricSeriesTheoremLocated = true
  ; explicitTailModulusLocated = false
  ; authoritativeAgdaBuildPassed = false
  ; stage3AdapterConstructed = false
  }

bothCandidatesRecorded : Bool
bothCandidatesRecorded = true

mrChicoReadyForStage3Import : Bool
mrChicoReadyForStage3Import = false

murrayBishopReadyForStage3Import : Bool
murrayBishopReadyForStage3Import = false

candidateComparisonChangesProofStatus : Bool
candidateComparisonChangesProofStatus = false

bothCandidatesRecordedIsTrue : bothCandidatesRecorded ≡ true
bothCandidatesRecordedIsTrue = refl

mrChicoReadyForStage3ImportIsFalse : mrChicoReadyForStage3Import ≡ false
mrChicoReadyForStage3ImportIsFalse = refl

murrayBishopReadyForStage3ImportIsFalse :
  murrayBishopReadyForStage3Import ≡ false
murrayBishopReadyForStage3ImportIsFalse = refl

candidateComparisonChangesProofStatusIsFalse :
  candidateComparisonChangesProofStatus ≡ false
candidateComparisonChangesProofStatusIsFalse = refl
