module DASHI.Physics.Closure.NSTriadKNConstructiveRealCandidateComparison where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Martin Lundfall; Zachary Murray; Viktor Csimma; Robbert
-- Krebbers; Bas Spitters; DASHI repository contributors.
-- Title: "Constructive-real candidate comparison for fixed-base dyadic Stage-3
-- series".
-- Venue/year: Reals-in-agda formal development and Formalizing Real Numbers in
-- Agda, 2015; Constructive Analysis in the Agda Proof Assistant, 2022;
-- maintained Bishop continuation, 2026; Logical Methods in Computer Science
-- 9(1:1), 2013; DASHI formal development, 2026.
-- DOI: no DOI located for Lundfall's Reals-in-agda development; Murray thesis
-- arXiv:2205.08354 has no DOI; Krebbers--Spitters DOI
-- 10.2168/LMCS-9(1:1)2013; the repository comparison has no DOI.
-- Murray thesis commit: 5cd6d3d023279518213f3e58879bfc867bb2503c.
-- Uses: candidate API, source-pin and toolchain reconnaissance only.
-- Relationship: neither external Agda tree is promoted. Lundfall is retained as
-- a mathematical/API comparator but deprioritized as a direct import because
-- its documented target is Agda Standard Library v0.9. Murray's thesis snapshot
-- is now pinned exactly, but source inspection has not located arbitrary-real
-- fixed-base 2^x, a suitable geometric-series theorem or an effective tail
-- modulus. Krebbers--Spitters is a Coq reference architecture only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNMurrayThesisCommitSourceInspection as MurraySource

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
    modernToolchainCompatibilityEstablished : Bool
    fixedBaseTwoPowerLocated : Bool
    arbitraryRealExponentLocated : Bool
    geometricSeriesTheoremLocated : Bool
    explicitTailModulusLocated : Bool
    authoritativeAgdaBuildPassed : Bool
    stage3AdapterConstructed : Bool

open CandidateCompatibilityAudit public

mrChicoRealsInAgdaAudit : CandidateCompatibilityAudit
mrChicoRealsInAgdaAudit = record
  { namespaceLocated = true
  ; pinnedRevisionRecorded = false
  ; standardLibraryVersionRecorded = true
  ; modernToolchainCompatibilityEstablished = false
  ; fixedBaseTwoPowerLocated = false
  ; arbitraryRealExponentLocated = false
  ; geometricSeriesTheoremLocated = false
  ; explicitTailModulusLocated = false
  ; authoritativeAgdaBuildPassed = false
  ; stage3AdapterConstructed = false
  }

murrayBishopAudit : CandidateCompatibilityAudit
murrayBishopAudit = record
  { namespaceLocated = true
  ; pinnedRevisionRecorded = MurraySource.murrayThesisCommitPinned
  ; standardLibraryVersionRecorded = false
  ; modernToolchainCompatibilityEstablished = false
  ; fixedBaseTwoPowerLocated = false
  ; arbitraryRealExponentLocated = false
  ; geometricSeriesTheoremLocated = false
  ; explicitTailModulusLocated = false
  ; authoritativeAgdaBuildPassed = false
  ; stage3AdapterConstructed = false
  }

record ReferenceArchitectureAudit : Set where
  constructor reference-audit
  field
    implementedInAgda : Bool
    suppliesExactRealArithmeticArchitecture : Bool
    suppliesDyadicArithmeticDesignEvidence : Bool
    usableAsDirectStage3Import : Bool

open ReferenceArchitectureAudit public

krebbersSpittersCoqReference : ReferenceArchitectureAudit
krebbersSpittersCoqReference = reference-audit false true true false

bothAgdaCandidatesRecorded : Bool
bothAgdaCandidatesRecorded = true

lundfallLegacyStdlibPinRecorded : Bool
lundfallLegacyStdlibPinRecorded = true

lundfallDirectImportDeprioritized : Bool
lundfallDirectImportDeprioritized = true

murrayThesisRevisionPinned : Bool
murrayThesisRevisionPinned = true

murrayFixedBaseDyadicAPIStillUnconfirmed : Bool
murrayFixedBaseDyadicAPIStillUnconfirmed = true

murrayCsimmaPreferredLiveCandidate : Bool
murrayCsimmaPreferredLiveCandidate = true

coqReferenceArchitectureRecorded : Bool
coqReferenceArchitectureRecorded = true

mrChicoReadyForStage3Import : Bool
mrChicoReadyForStage3Import = false

murrayBishopReadyForStage3Import : Bool
murrayBishopReadyForStage3Import = false

candidateComparisonChangesProofStatus : Bool
candidateComparisonChangesProofStatus = false

bothAgdaCandidatesRecordedIsTrue : bothAgdaCandidatesRecorded ≡ true
bothAgdaCandidatesRecordedIsTrue = refl

lundfallLegacyStdlibPinRecordedIsTrue :
  lundfallLegacyStdlibPinRecorded ≡ true
lundfallLegacyStdlibPinRecordedIsTrue = refl

lundfallDirectImportDeprioritizedIsTrue :
  lundfallDirectImportDeprioritized ≡ true
lundfallDirectImportDeprioritizedIsTrue = refl

murrayThesisRevisionPinnedIsTrue : murrayThesisRevisionPinned ≡ true
murrayThesisRevisionPinnedIsTrue = refl

murrayFixedBaseDyadicAPIStillUnconfirmedIsTrue :
  murrayFixedBaseDyadicAPIStillUnconfirmed ≡ true
murrayFixedBaseDyadicAPIStillUnconfirmedIsTrue = refl

murrayCsimmaPreferredLiveCandidateIsTrue :
  murrayCsimmaPreferredLiveCandidate ≡ true
murrayCsimmaPreferredLiveCandidateIsTrue = refl

coqReferenceArchitectureRecordedIsTrue :
  coqReferenceArchitectureRecorded ≡ true
coqReferenceArchitectureRecordedIsTrue = refl

mrChicoReadyForStage3ImportIsFalse : mrChicoReadyForStage3Import ≡ false
mrChicoReadyForStage3ImportIsFalse = refl

murrayBishopReadyForStage3ImportIsFalse :
  murrayBishopReadyForStage3Import ≡ false
murrayBishopReadyForStage3ImportIsFalse = refl

candidateComparisonChangesProofStatusIsFalse :
  candidateComparisonChangesProofStatus ≡ false
candidateComparisonChangesProofStatusIsFalse = refl
