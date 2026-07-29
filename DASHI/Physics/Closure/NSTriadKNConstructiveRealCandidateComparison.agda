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
-- Uses: candidate API and toolchain reconnaissance only.
-- Relationship: neither external Agda tree is promoted. Lundfall is retained as
-- a mathematical/API comparator but deprioritized as a direct import because
-- its documented target is Agda Standard Library v0.9. Krebbers--Spitters is a
-- Coq reference architecture only and cannot be imported into Agda. An
-- authoritative pinned Nix/Agda build and explicit fixed-base-two/geometric-tail
-- adapter remain required for the Murray/Csimma lane.
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
    modernToolchainCompatibilityEstablished : Bool
    fixedBaseTwoPowerLocated : Bool
    arbitraryRealExponentLocated : Bool
    geometricSeriesTheoremLocated : Bool
    explicitTailModulusLocated : Bool
    authoritativeAgdaBuildPassed : Bool
    stage3AdapterConstructed : Bool

open CandidateCompatibilityAudit public

-- Lundfall explicitly documents Agda Standard Library v0.9.  This converts the
-- earlier soft compatibility unknown into a concrete legacy-toolchain reason to
-- deprioritize direct import.  It does not impugn the mathematics.
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

-- Murray/Csimma is already the better-integrated live candidate elsewhere in
-- DASHI, but the exact Stage-3 fixed-base-two adapter and authoritative build
-- are still not closed on this branch.
murrayBishopAudit : CandidateCompatibilityAudit
murrayBishopAudit = record
  { namespaceLocated = true
  ; pinnedRevisionRecorded = true
  ; standardLibraryVersionRecorded = false
  ; modernToolchainCompatibilityEstablished = false
  ; fixedBaseTwoPowerLocated = false
  ; arbitraryRealExponentLocated = false
  ; geometricSeriesTheoremLocated = true
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

-- Krebbers--Spitters is rigorous and useful for API design, but it is a Coq
-- development and therefore cannot be a direct DASHI build dependency.
krebbersSpittersCoqReference : ReferenceArchitectureAudit
krebbersSpittersCoqReference = reference-audit false true true false

bothAgdaCandidatesRecorded : Bool
bothAgdaCandidatesRecorded = true

lundfallLegacyStdlibPinRecorded : Bool
lundfallLegacyStdlibPinRecorded = true

lundfallDirectImportDeprioritized : Bool
lundfallDirectImportDeprioritized = true

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
