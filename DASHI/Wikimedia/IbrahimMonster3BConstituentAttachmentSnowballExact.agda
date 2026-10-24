module DASHI.Wikimedia.IbrahimMonster3BConstituentAttachmentSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.Monster3BActualKernelCharacterPromotionExact as Actual
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannMultiplicityExact as Multiplicity
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannUniquenessBidiExact as Uniqueness
import DASHI.Wikimedia.IbrahimMonsterCharacterDeterminationMathlibProducerSnowballExact as Mathlib

------------------------------------------------------------------------
-- ACTUAL W_zeta CONSTITUENT ATTACHMENT CUT
--
-- The actual-kernel character owner pays the WHOLE selected-sector character
-- shape as ninety copies of the nonlinear Heisenberg signature once an actual
-- promotion object is supplied.  The multiplicity theorem, however, starts
-- from a literal list of irreducible selected-phase constituents.
--
-- The generic equal-character/simple-representation theorem is now also
-- source-written on the companion Lean branch.  Neither fact constructs the
-- SAME-object direct-sum decomposition of the literal W_zeta sector.
--
-- Historical note: the five fields below are values of type `Set`.  They NAME
-- the exact proposition types that must be paid, but do not themselves contain
-- inhabitants of those propositions.  The separate proof-relevance hardening
-- owner wraps this legacy record and requires explicit witnesses.  This file is
-- retained as the source/coordinate/frontier owner so existing consumers are
-- not silently broken.
------------------------------------------------------------------------

record ActualZetaConstituentAttachment
    (promotion : Actual.ActualKernelCharacterPromotion) : Set₁ where
  field
    decomposition : Multiplicity.ActualZetaSectorStoneVonNeumannDecomposition

    -- Exact obligation TYPES for the SAME actual restricted sector.
    SameActualRestrictedSector : Set
    DirectSumRealisation : Set
    EveryConstituentSelectedCentralPhase : Set
    EveryConstituentIrreducible : Set
    EveryConstituentCharacterMatchesCanonicalSignature : Set

open ActualZetaConstituentAttachment public

------------------------------------------------------------------------
-- The numerical count theorem consumes only the decomposition object.  It
-- proves that any such certified constituent list has length ninety; it does
-- not turn the Set-valued same-object obligations above into witnesses.
------------------------------------------------------------------------

attachedMultiplicityIsNinety :
  {promotion : Actual.ActualKernelCharacterPromotion} →
  (attachment : ActualZetaConstituentAttachment promotion) →
  Multiplicity.constituentCount
    (Multiplicity.constituents (decomposition attachment)) ≡ 90
attachedMultiplicityIsNinety attachment =
  Multiplicity.actualZetaSectorMultiplicityIsNinety
    (decomposition attachment)

------------------------------------------------------------------------
-- Source / attribution snowball.
------------------------------------------------------------------------

serreSource : Attribution.AttributedSource
serreSource = Mathlib.serreMathematicalSource

leanWrapperRepositoryReceipt : Mathlib.LeanWrapperRepositoryReceipt
leanWrapperRepositoryReceipt = Mathlib.canonicalLeanWrapperRepositoryReceipt

terrasSource : Attribution.AttributedSource
terrasSource = Attribution.mkDOISource
  "Audrey Terras"
  "Fourier Analysis on Finite Groups and Applications"
  "Cambridge University Press"
  "1999"
  "10.1017/CBO9780511626265"
  "https://doi.org/10.1017/CBO9780511626265"
  Attribution.academicBookSource
  "finite-group Fourier/representation provenance for character decomposition; citation does not construct the actual Monster constituent attachment"
  Attribution.publicAttribution

barracloughWilsonSource : Attribution.AttributedSource
barracloughWilsonSource = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary Monster 3B-normalizer character-table provenance; does not by itself split the selected phase into literal irreducible constituents"
  Attribution.publicAttribution

serreAttribution = Snowball.canonicalSourceRoleSnowballReceipt serreSource
terrasAttribution = Snowball.canonicalSourceRoleSnowballReceipt terrasSource
barracloughWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilsonSource

record ConstituentAttachmentExternalCoordinates : Set where
  constructor constituent-attachment-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    relevantOEIS : String
    oeisCreatesConstituentDecomposition : Bool
open ConstituentAttachmentExternalCoordinates public

canonicalConstituentAttachmentExternalCoordinates : ConstituentAttachmentExternalCoordinates
canonicalConstituentAttachmentExternalCoordinates =
  constituent-attachment-external-coordinates
    "Q1055807" "Q600043" "Q1057968"
    "512.22" "512.23"
    "A005052 remains only a numerical coordinate for 90 = 10*3^2; DASHIMathOEIS196883AuditRoadmapExact independently records its exact role as the family a(n)=10*3^n and still denies Monster representation semantics"
    false

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data MergedLeanSourceCreatesConstituentAttachment : Set where
data WholeCharacterEqualityCreatesLiteralDirectSum : Set where
data DegreeCountCreatesSameObjectAttachment : Set where
data OEISMultiplicityCreatesRepresentation : Set where
data QidCreatesConstituentIso : Set where

mergedLeanSourceDoesNotCreateConstituentAttachment :
  MergedLeanSourceCreatesConstituentAttachment → ⊥
mergedLeanSourceDoesNotCreateConstituentAttachment ()

wholeCharacterDoesNotCreateDirectSum : WholeCharacterEqualityCreatesLiteralDirectSum → ⊥
wholeCharacterDoesNotCreateDirectSum ()

degreeDoesNotCreateAttachment : DegreeCountCreatesSameObjectAttachment → ⊥
degreeDoesNotCreateAttachment ()

oeisDoesNotCreateRepresentation : OEISMultiplicityCreatesRepresentation → ⊥
oeisDoesNotCreateRepresentation ()

qidDoesNotCreateConstituentIso : QidCreatesConstituentIso → ⊥
qidDoesNotCreateConstituentIso ()

------------------------------------------------------------------------
-- Highest-alpha frontier.
------------------------------------------------------------------------

record ConstituentAttachmentFrontier : Set where
  constructor constituent-attachment-frontier
  field
    wholeActualCharacterCompilerExists : Bool
    constituentListMultiplicityCompilerExists : Bool
    equalIrreducibleCharacterProducerLocated : Bool
    equalIrreducibleCharacterSourceMerged : Bool
    sameObjectConstituentAttachmentExists : Bool
    leanEqualCharacterKernelReceiptObserved : Bool
    actualKernelReplayReceiptObserved : Bool
    actualZetaRecognitionUnlocked : Bool
    nextResidual : String
open ConstituentAttachmentFrontier public

currentConstituentAttachmentFrontier : ConstituentAttachmentFrontier
currentConstituentAttachmentFrontier = constituent-attachment-frontier
  true true true true
  false false false false
  "The dominant payment is no longer a theorem-name or CI leaf. Construct the proof-relevant SAME W_zeta|E direct-sum attachment: a literal decomposition of the selected sector, plus inhabited witnesses that it is the same restricted sector and that every constituent has the selected central phase, is irreducible and has the canonical nonlinear Heisenberg character. The existing multiplicity compiler then forces exactly ninety constituents; the generic equal-character/simple-representation theorem can identify a concretely packaged constituent with the explicit Schrodinger H_zeta after common representation/character transport. Whole-sector character equality, 65610=729*90, A005052, QIDs, Dewey coordinates and citations remain insufficient substitutes."
