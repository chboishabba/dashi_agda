module DASHI.Governance.SexedHistoricalCoalitionAssociatorYijingExact where

------------------------------------------------------------------------
-- COALITION ASSOCIATOR / YIJING RELATIONAL-CHANGE BRIDGE
--
-- Highest-alpha seam:
--
--   (F ⋄ M) ⋄ I   ?=   F ⋄ (M ⋄ I)
--
-- Here ⋄ is proof-relevant partial compatible gluing of local descendant
-- fibres, NOT the associative composition law of the formal M/F arrow category.
-- The two bracketings are both admitted from the same local participants but
-- produce different global relational signatures in the finite fixture.
--
-- Yijing cross-pollination is structural only.  We reuse the canonical DASHI
-- Yijing owners for:
--   * six-line initial / moving-mask / resulting-state structure;
--   * lower/upper trigram decomposition;
--   * contextual polarity and ternary unresolved state;
--   * reversal/complement/exchange/nuclear relational operators.
--
-- We do NOT identify woman with yin, man with yang, institution with a trigram,
-- coalition order with a received hexagram meaning, or a structural reading
-- with external prediction/divination authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.DASHIYijingTernaryDivinationExact as Yijing
import DASHI.Biology.DASHIYijingRelationalOperatorsExact as YijingOps
import DASHI.Governance.SexedHistoricalStratifiedCollectiveGluingExact as Gluing
import DASHI.Governance.SexedHistoricalBracketedMultiverseTSFVBridgeExact as Branching

------------------------------------------------------------------------
-- 1. Proof-relevant partial coalition gluing.
------------------------------------------------------------------------

data CoalitionPiece : Set where
  feminineLocal
  masculineLocal
  institutionalLocal
  feminineMasculineCoalition
  masculineInstitutionCoalition
  reciprocalInstitutionalCollective
  institutionMediatedPluralCollective
  : CoalitionPiece

data _⋄_↝_ : CoalitionPiece → CoalitionPiece → CoalitionPiece → Set where
  glueFM :
    feminineLocal ⋄ masculineLocal ↝ feminineMasculineCoalition
  glueMI :
    masculineLocal ⋄ institutionalLocal ↝ masculineInstitutionCoalition
  glueFMI-left :
    feminineMasculineCoalition ⋄ institutionalLocal
      ↝ reciprocalInstitutionalCollective
  glueFMI-right :
    feminineLocal ⋄ masculineInstitutionCoalition
      ↝ institutionMediatedPluralCollective

record LeftBracketedCoalitionPath : Set where
  constructor left-bracketed-coalition-path
  field
    firstGlue : feminineLocal ⋄ masculineLocal ↝ feminineMasculineCoalition
    secondGlue : feminineMasculineCoalition ⋄ institutionalLocal
      ↝ reciprocalInstitutionalCollective

record RightBracketedCoalitionPath : Set where
  constructor right-bracketed-coalition-path
  field
    firstGlue : masculineLocal ⋄ institutionalLocal ↝ masculineInstitutionCoalition
    secondGlue : feminineLocal ⋄ masculineInstitutionCoalition
      ↝ institutionMediatedPluralCollective

canonicalLeftBracketedPath : LeftBracketedCoalitionPath
canonicalLeftBracketedPath = left-bracketed-coalition-path glueFM glueFMI-left

canonicalRightBracketedPath : RightBracketedCoalitionPath
canonicalRightBracketedPath = right-bracketed-coalition-path glueMI glueFMI-right

leftBracketedGlobal : CoalitionPiece
leftBracketedGlobal = reciprocalInstitutionalCollective

rightBracketedGlobal : CoalitionPiece
rightBracketedGlobal = institutionMediatedPluralCollective

coalitionAssociatorDefect :
  leftBracketedGlobal ≡ rightBracketedGlobal → ⊥
coalitionAssociatorDefect ()

------------------------------------------------------------------------
-- 2. Associator residual: not equality, but an explicit relation between the
-- two admitted bracketed results.
------------------------------------------------------------------------

data CoalitionAssociatorResidual : CoalitionPiece → CoalitionPiece → Set where
  retainedCoalitionAssociator :
    CoalitionAssociatorResidual
      reciprocalInstitutionalCollective
      institutionMediatedPluralCollective

canonicalCoalitionAssociator :
  CoalitionAssociatorResidual leftBracketedGlobal rightBracketedGlobal
canonicalCoalitionAssociator = retainedCoalitionAssociator

------------------------------------------------------------------------
-- 3. Same local participant family does not recover coalition bracketing.
------------------------------------------------------------------------

data CoalitionBracketHistory : Set where
  leftBracketHistory rightBracketHistory : CoalitionBracketHistory

data ParticipantInventory : Set where
  sameFeminineMasculineInstitutionInventory : ParticipantInventory

data CoalitionGlobalOutcome : Set where
  reciprocalInstitutionalOutcome pluralMediatedOutcome : CoalitionGlobalOutcome

participantInventory : CoalitionBracketHistory → ParticipantInventory
participantInventory _ = sameFeminineMasculineInstitutionInventory

coalitionOutcome : CoalitionBracketHistory → CoalitionGlobalOutcome
coalitionOutcome leftBracketHistory = reciprocalInstitutionalOutcome
coalitionOutcome rightBracketHistory = pluralMediatedOutcome

sameParticipantsCannotRecoverCoalitionOutcome :
  INF.FactorsThrough participantInventory coalitionOutcome → ⊥
sameParticipantsCannotRecoverCoalitionOutcome =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      leftBracketHistory rightBracketHistory refl (λ ()))

------------------------------------------------------------------------
-- 4. Yijing-style six-line relational signatures.
--
-- These are DASHI structural signatures only.  They are not received hexagram
-- identifications or historical predictions.
------------------------------------------------------------------------

commonCoalitionInitial : Yijing.TernaryHexagram
commonCoalitionInitial =
  Triadic.negativeTrit vcons
  Triadic.zeroTrit vcons
  Triadic.positiveTrit vcons
  Triadic.positiveTrit vcons
  Triadic.zeroTrit vcons
  Triadic.negativeTrit vcons
  vnil

leftBracketMovingMask : Vec Bool 6
leftBracketMovingMask =
  true vcons
  false vcons
  false vcons
  true vcons
  false vcons
  false vcons
  vnil

rightBracketMovingMask : Vec Bool 6
rightBracketMovingMask =
  false vcons
  true vcons
  false vcons
  false vcons
  true vcons
  false vcons
  vnil

leftBracketSignature : Yijing.TernaryHexagram
leftBracketSignature =
  Yijing.applyMovingMask leftBracketMovingMask commonCoalitionInitial

rightBracketSignature : Yijing.TernaryHexagram
rightBracketSignature =
  Yijing.applyMovingMask rightBracketMovingMask commonCoalitionInitial

leftBracketSignatureExact :
  leftBracketSignature ≡
  (Triadic.positiveTrit vcons
   Triadic.zeroTrit vcons
   Triadic.positiveTrit vcons
   Triadic.negativeTrit vcons
   Triadic.zeroTrit vcons
   Triadic.negativeTrit vcons
   vnil)
leftBracketSignatureExact = refl

rightBracketSignatureExact :
  rightBracketSignature ≡
  (Triadic.negativeTrit vcons
   Triadic.zeroTrit vcons
   Triadic.positiveTrit vcons
   Triadic.positiveTrit vcons
   Triadic.zeroTrit vcons
   Triadic.negativeTrit vcons
   vnil)
rightBracketSignatureExact = refl

coalitionBracketProducesDifferentRelationalSignature :
  leftBracketSignature ≡ rightBracketSignature → ⊥
coalitionBracketProducesDifferentRelationalSignature ()

------------------------------------------------------------------------
-- 5. Lower/upper trigram decomposition remains exact and gives a useful local /
-- relational partition without assigning fixed social meanings to trigrams.
------------------------------------------------------------------------

leftLower : Yijing.TernaryTrigram
leftLower = YijingOps.lowerTrigram leftBracketSignature

leftUpper : Yijing.TernaryTrigram
leftUpper = YijingOps.upperTrigram leftBracketSignature

rightLower : Yijing.TernaryTrigram
rightLower = YijingOps.lowerTrigram rightBracketSignature

rightUpper : Yijing.TernaryTrigram
rightUpper = YijingOps.upperTrigram rightBracketSignature

leftSplitRecomposes :
  YijingOps.composeTrigrams leftLower leftUpper ≡ leftBracketSignature
leftSplitRecomposes = YijingOps.splitThenCompose leftBracketSignature

rightSplitRecomposes :
  YijingOps.composeTrigrams rightLower rightUpper ≡ rightBracketSignature
rightSplitRecomposes = YijingOps.splitThenCompose rightBracketSignature

------------------------------------------------------------------------
-- 6. Moving-mask provenance is retained separately from resulting signature.
------------------------------------------------------------------------

record CoalitionChangeReceipt : Set where
  constructor coalition-change-receipt
  field
    initial : Yijing.TernaryHexagram
    movingMask : Vec Bool 6
    resulting : Yijing.TernaryHexagram

leftCoalitionChange : CoalitionChangeReceipt
leftCoalitionChange =
  coalition-change-receipt
    commonCoalitionInitial leftBracketMovingMask leftBracketSignature

rightCoalitionChange : CoalitionChangeReceipt
rightCoalitionChange =
  coalition-change-receipt
    commonCoalitionInitial rightBracketMovingMask rightBracketSignature

------------------------------------------------------------------------
-- 7. Continuity with the actual stratified gluing owner.
------------------------------------------------------------------------

sameLocalReciprocalFamilyStillNeedsInstitutionalCompatibility :
  Gluing.CompatibleFamily Gluing.blockedCollectiveFamily → ⊥
sameLocalReciprocalFamilyStillNeedsInstitutionalCompatibility =
  Gluing.blockedCollectiveFamilyCannotGlue

canonicalCompatibilityThresholdStillExists :
  Gluing.MinimalCompatibilityExtension
canonicalCompatibilityThresholdStillExists =
  Gluing.canonicalMinimalCompatibilityExtension

samePresentStillDoesNotRecoverDescendantFuture :
  INF.FactorsThrough Branching.coarsePresent Branching.branchFutureCone → ⊥
samePresentStillDoesNotRecoverDescendantFuture =
  Branching.samePresentCannotRecoverDescendantFuture

------------------------------------------------------------------------
-- 8. Source / interpretation boundaries.
------------------------------------------------------------------------

data WomanIsYin : Set where

data ManIsYang : Set where

data InstitutionIsUpperTrigram : Set where

data CoalitionSignatureIsReceivedHexagramMeaning : Set where

data CoalitionAssociatorIsYijingPrediction : Set where

data StructuralReadingEntailsExternalPrediction : Set where

data SameParticipantsGuaranteeSameCoalition : Set where

data EveryCompatibleGlueIsAssociative : Set where

data AssociatorResidualIsGaugeCurvature : Set where

data YijingMovingLineIsHistoricalCausalMechanism : Set where

womanIsNotIdentifiedWithYin : WomanIsYin → ⊥
womanIsNotIdentifiedWithYin ()

manIsNotIdentifiedWithYang : ManIsYang → ⊥
manIsNotIdentifiedWithYang ()

institutionIsNotIdentifiedWithUpperTrigram : InstitutionIsUpperTrigram → ⊥
institutionIsNotIdentifiedWithUpperTrigram ()

coalitionSignatureIsNotReceivedHexagramMeaning :
  CoalitionSignatureIsReceivedHexagramMeaning → ⊥
coalitionSignatureIsNotReceivedHexagramMeaning ()

coalitionAssociatorIsNotYijingPrediction : CoalitionAssociatorIsYijingPrediction → ⊥
coalitionAssociatorIsNotYijingPrediction ()

structuralReadingDoesNotEntailExternalPrediction :
  StructuralReadingEntailsExternalPrediction → ⊥
structuralReadingDoesNotEntailExternalPrediction ()

sameParticipantsDoNotGuaranteeSameCoalition :
  SameParticipantsGuaranteeSameCoalition → ⊥
sameParticipantsDoNotGuaranteeSameCoalition ()

compatibleGluingIsNotDeclaredUniversallyAssociative :
  EveryCompatibleGlueIsAssociative → ⊥
compatibleGluingIsNotDeclaredUniversallyAssociative ()

coalitionAssociatorIsNotGaugeCurvature : AssociatorResidualIsGaugeCurvature → ⊥
coalitionAssociatorIsNotGaugeCurvature ()

yijingMovingLineIsNotHistoricalCausalMechanism :
  YijingMovingLineIsHistoricalCausalMechanism → ⊥
yijingMovingLineIsNotHistoricalCausalMechanism ()

record CoalitionAssociatorYijingBoundary : Set where
  constructor coalition-associator-yijing-boundary
  field
    bothBracketingsAdmitted : Bool
    sameParticipantsDetermineSameGlobalCoalition : Bool
    associatorResidualRetained : Bool
    movingMaskRetainedAsChangeProvenance : Bool
    lowerUpperTrigramDecompositionExact : Bool
    yinYangAssignedDirectlyToSexedSubjects : Bool
    yijingStructureCreatesPredictionAuthority : Bool
    associatorEqualsGaugeCurvature : Bool

canonicalCoalitionAssociatorYijingBoundary : CoalitionAssociatorYijingBoundary
canonicalCoalitionAssociatorYijingBoundary =
  coalition-associator-yijing-boundary
    true false true true true false false false
