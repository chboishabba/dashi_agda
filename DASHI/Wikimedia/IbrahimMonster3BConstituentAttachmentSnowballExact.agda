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
-- The actual-kernel character owner can prove the WHOLE selected-sector
-- character is 90 copies of the Heisenberg character once its execution
-- certificate is supplied.  The multiplicity owner, however, starts from a
-- literal list of irreducible constituents already certified as selected-phase
-- Stone--von Neumann objects.  Repo search found no second semisimple/isotypic
-- compiler connecting those two owners.
--
-- Therefore the next mathematical object is not another dimension identity:
-- it is a SAME-OBJECT constituent attachment for W_zeta|E.
------------------------------------------------------------------------

record ActualZetaConstituentAttachment
    (promotion : Actual.ActualKernelCharacterPromotion) : Set₁ where
  field
    decomposition : Multiplicity.ActualZetaSectorStoneVonNeumannDecomposition

    -- These fields are deliberately proof-relevant rather than Bool metadata.
    -- They express that the constituent list is a decomposition of the SAME
    -- actual restricted sector, not a numerically matching abstract list.
    SameActualRestrictedSector : Set
    DirectSumRealisation : Set
    EveryConstituentSelectedCentralPhase : Set
    EveryConstituentIrreducible : Set
    EveryConstituentCharacterMatchesCanonicalSignature : Set

open ActualZetaConstituentAttachment public

------------------------------------------------------------------------
-- Once attachment exists, the already-owned multiplicity compiler immediately
-- pays the numerical multiplicity 90; no new 729*90 arithmetic is needed.
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
    "A005052 remains only a numerical coordinate for 90 = 10*3^2"
    false

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data WholeCharacterEqualityCreatesLiteralDirectSum : Set where
data DegreeCountCreatesSameObjectAttachment : Set where
data OEISMultiplicityCreatesRepresentation : Set where
data QidCreatesConstituentIso : Set where

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
    sameObjectConstituentAttachmentExists : Bool
    leanEqualCharacterKernelReceiptObserved : Bool
    actualKernelReplayReceiptObserved : Bool
    actualZetaRecognitionUnlocked : Bool
    nextResidual : String
open ConstituentAttachmentFrontier public

currentConstituentAttachmentFrontier : ConstituentAttachmentFrontier
currentConstituentAttachmentFrontier = constituent-attachment-frontier
  true true true false false false false
  "pay the actual MN3B kernel replay and the Lean equal-character kernel receipt; then construct the SAME W_zeta|E constituent decomposition with selected central phase, irreducibility and per-constituent character match. The existing multiplicity compiler then forces exactly 90 constituents. Do not replace this attachment with 65610=729*90, A005052, QIDs, or source citation."
