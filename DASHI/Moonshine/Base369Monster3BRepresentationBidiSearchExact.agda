module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchExact where

------------------------------------------------------------------------
-- CONSUMER-FIRST MONSTER 3B REPRESENTATION BIDI SEARCH FRONTIER
--
-- The repository now already contains a fail-closed GAP/CTblLib producer for
-- the actual M -> MN3B restriction.  It checks the stored class fusion,
-- decomposes the 196883 character, reconstructs all target class values,
-- isolates the central 3B class with trace 53, and checks that the paired
-- nontrivial central-phase constituents yield the 12 and 78 multiplicity
-- quotients after division by 2 * 729.
--
-- Therefore the first missing scientific receipt is no longer "write a
-- restriction algorithm".  The live frontier is:
--
--   exact-head replay of the existing CTblLib restriction certificate
--   -> identify the certified 729 factor with the concrete finite-Heisenberg
--      representation (finite Stone-von Neumann / explicit action authority)
--   -> actual 729 x 90 tensor constituent identification
--   -> Base369 periodic-fibre intertwiner
--   -> audit whether the +53 invariant excess is carried by the structured
--      54 -> 53 zeta/ternary carrier
--   -> only then consider larger Monster-level promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Moonshine.Monster3BNormalizerBridge as Normalizer
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Heisenberg
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Fibre
import DASHI.Moonshine.Base369PeriodicHeisenbergFibreEquivarianceExact as Periodic
import DASHI.Moonshine.Base369ZetaHeisenbergFiftyFourCarrierExact as Zeta54
import DASHI.Moonshine.Base369MonsterFineCarrierEquivarianceAuditExact as Fine

------------------------------------------------------------------------
-- 1. Exact current arithmetic/data surface.
------------------------------------------------------------------------

heisenbergFactor : Nat
heisenbergFactor = Normalizer.heisenbergDegree

multiplicityFactor : Nat
multiplicityFactor = Normalizer.multiplicityDegree

nontrivialPhaseSector : Nat
nontrivialPhaseSector = Normalizer.nontrivialPhaseDegree

invariantPhaseSector : Nat
invariantPhaseSector = Normalizer.invariantPhaseDegree

invariantExcess : Nat
invariantExcess = Normalizer.characterResidual

heisenbergFactorIs729 : heisenbergFactor ≡ 729
heisenbergFactorIs729 = refl

multiplicityFactorIs90 : multiplicityFactor ≡ 90
multiplicityFactorIs90 = Normalizer.multiplicity-degree-is-90

nontrivialPhaseIs729Times90 :
  heisenbergFactor * multiplicityFactor ≡ nontrivialPhaseSector
nontrivialPhaseIs729Times90 = refl

nontrivialPhaseIs65610 : nontrivialPhaseSector ≡ 65610
nontrivialPhaseIs65610 = Normalizer.nontrivial-phase-degree-is-65610

invariantExcessIs53 : invariantExcess ≡ 53
invariantExcessIs53 = refl

invariantIsNontrivialPlus53 :
  nontrivialPhaseSector + invariantExcess ≡ invariantPhaseSector
invariantIsNontrivialPlus53 = Normalizer.invariant-excess

------------------------------------------------------------------------
-- 2. The Base369 fibre already matches the model Heisenberg carrier exactly,
--    and Heisenberg translations act equivariantly on the periodic C3^6 host.
------------------------------------------------------------------------

base369FibreCountMatchesHeisenberg :
  Fibre.heisenbergFibreStateCount ≡ heisenbergFactor
base369FibreCountMatchesHeisenberg = refl

periodicTranslationModelAvailable : Bool
periodicTranslationModelAvailable = true

periodicTranslationModelAvailableIsTrue : periodicTranslationModelAvailable ≡ true
periodicTranslationModelAvailableIsTrue = refl

------------------------------------------------------------------------
-- 3. Proof/search consumers ordered by authority.
------------------------------------------------------------------------

data Monster3BProofLeaf : Set where
  restrictionAlgorithmImplemented : Monster3BProofLeaf
  exactHeadRestrictionReplay : Monster3BProofLeaf
  heisenbergUniquenessOrActionIdentification : Monster3BProofLeaf
  actualTensorConstituentIdentification : Monster3BProofLeaf
  base369PeriodicIntertwiner : Monster3BProofLeaf
  structuredFiftyThreeExcessIdentification : Monster3BProofLeaf
  largerMonsterRepresentationPromotion : Monster3BProofLeaf

data LeafState : Set where
  closed : LeafState
  open : LeafState
  blocked : LeafState

leafState : Monster3BProofLeaf → LeafState
leafState restrictionAlgorithmImplemented = closed
leafState exactHeadRestrictionReplay = open
leafState heisenbergUniquenessOrActionIdentification = blocked
leafState actualTensorConstituentIdentification = blocked
leafState base369PeriodicIntertwiner = blocked
leafState structuredFiftyThreeExcessIdentification = blocked
leafState largerMonsterRepresentationPromotion = blocked

restrictionAlgorithmIsClosed : leafState restrictionAlgorithmImplemented ≡ closed
restrictionAlgorithmIsClosed = refl

------------------------------------------------------------------------
-- 4. Dependency relation.  Geometry/counts cannot bypass representation
--    authority.  In particular, 729 = 729 is not the Stone-von Neumann step.
------------------------------------------------------------------------

data Requires : Monster3BProofLeaf → Monster3BProofLeaf → Set where
  replayNeedsAlgorithm :
    Requires exactHeadRestrictionReplay restrictionAlgorithmImplemented
  uniquenessNeedsReplay :
    Requires heisenbergUniquenessOrActionIdentification exactHeadRestrictionReplay
  tensorNeedsHeisenbergAuthority :
    Requires actualTensorConstituentIdentification heisenbergUniquenessOrActionIdentification
  base369NeedsTensor :
    Requires base369PeriodicIntertwiner actualTensorConstituentIdentification
  fiftyThreeNeedsReplay :
    Requires structuredFiftyThreeExcessIdentification exactHeadRestrictionReplay
  fiftyThreeNeedsIntertwiner :
    Requires structuredFiftyThreeExcessIdentification base369PeriodicIntertwiner
  monsterNeedsTensor :
    Requires largerMonsterRepresentationPromotion actualTensorConstituentIdentification
  monsterNeedsResidualAudit :
    Requires largerMonsterRepresentationPromotion structuredFiftyThreeExcessIdentification

------------------------------------------------------------------------
-- 5. Current highest-impact live target.
------------------------------------------------------------------------

highestImpactLiveLeaf : Monster3BProofLeaf
highestImpactLiveLeaf = exactHeadRestrictionReplay

highestImpactLeafIsOpen : leafState highestImpactLiveLeaf ≡ open
highestImpactLeafIsOpen = refl

nextMathematicalLeafAfterReplay : Monster3BProofLeaf
nextMathematicalLeafAfterReplay = heisenbergUniquenessOrActionIdentification

------------------------------------------------------------------------
-- 6. Receipts that would actually promote the frontier.
------------------------------------------------------------------------

record RestrictionReplayReceipt : Set where
  constructor restrictionReplayReceipt
  field
    ctblLibLoaded : Bool
    storedFusionChecked : Bool
    nonnegativeIntegralDecompositionChecked : Bool
    classValuesReconstructed : Bool
    central3BTrace53Checked : Bool
    pairedPhaseTwelveAndSeventyEightChecked : Bool
    generatedAgdaCertificateKernelChecked : Bool
open RestrictionReplayReceipt public

record HeisenbergRepresentationAuthorityReceipt : Set where
  constructor heisenbergRepresentationAuthorityReceipt
  field
    replayReceipt : RestrictionReplayReceipt
    nontrivialCentralCharacterLocated : Bool
    extraspecialCarrierIdentified : Bool
    finiteStoneVonNeumannUniquenessProvedOrExplicitMatricesImported : Bool
    certified729RepresentationIdentifiedWithX6SchrodingerModel : Bool
open HeisenbergRepresentationAuthorityReceipt public

record HeisenbergTensorFactorisationReceipt : Set where
  constructor heisenbergTensorFactorisationReceipt
  field
    heisenbergAuthority : HeisenbergRepresentationAuthorityReceipt
    multiplicityCarrierReallyActs : Bool
    twelvePlusSeventyEightConstituentsIdentified : Bool
    tensorActionIntertwinesRestriction : Bool
open HeisenbergTensorFactorisationReceipt public

record Base369NormalizerIntertwinerReceipt : Set where
  constructor base369NormalizerIntertwinerReceipt
  field
    tensorReceipt : HeisenbergTensorFactorisationReceipt
    periodicFibreChartUsed : Bool
    normalizerGeneratorsIntertwine : Bool
    pathRestrictionResidualTracked : Bool
open Base369NormalizerIntertwinerReceipt public

record FiftyThreeExcessReceipt : Set where
  constructor fiftyThreeExcessReceipt
  field
    replayReceipt53 : RestrictionReplayReceipt
    base369IntertwinerReceipt : Base369NormalizerIntertwinerReceipt
    zeta54CarrierUsed : Bool
    invariantLineLocated : Bool
    fiftyThreeExcessRecoveredAsActionStableResidual : Bool
open FiftyThreeExcessReceipt public

------------------------------------------------------------------------
-- 7. The 54 carrier is a discriminator, not authority by itself.
------------------------------------------------------------------------

zeta54CarrierCount : Nat
zeta54CarrierCount = Zeta54.fiftyFourCarrierCount

zeta54CarrierCountIs54 : zeta54CarrierCount ≡ 54
zeta54CarrierCountIs54 = Zeta54.fiftyFourCarrierCountIs54

zeta54ReducedCandidateCount : Nat
zeta54ReducedCandidateCount = 53

zeta54ReducedCandidateMatchesNormalizerExcess :
  zeta54ReducedCandidateCount ≡ invariantExcess
zeta54ReducedCandidateMatchesNormalizerExcess = refl

------------------------------------------------------------------------
-- 8. BIDI boundary / search discipline.
------------------------------------------------------------------------

record Monster3BRepresentationSearchBoundary : Set where
  constructor monster3BRepresentationSearchBoundary
  field
    arithmeticAgreementAvailable : Bool
    exact729CarrierChartAvailable : Bool
    periodicHeisenbergEquivarianceAvailable : Bool
    restrictionAlgorithmImplementedHere : Bool
    exactHeadRestrictionReplayAvailable : Bool
    finiteStoneVonNeumannOrExplicitActionAvailable : Bool
    actualTensorConstituentIdentificationAvailable : Bool
    base369NormalizerIntertwinerAvailable : Bool
    structured53ExcessIdentificationAvailable : Bool
    fullMonsterRepresentationProvedHere : Bool
    fiftyThreeCountAloneClosesResidualLeaf : Bool
    shared729CountAloneClosesHeisenbergAuthorityLeaf : Bool
open Monster3BRepresentationSearchBoundary public

canonicalMonster3BRepresentationSearchBoundary : Monster3BRepresentationSearchBoundary
canonicalMonster3BRepresentationSearchBoundary =
  monster3BRepresentationSearchBoundary
    true true true true
    false false false false false false
    false false

------------------------------------------------------------------------
-- 9. Scientific-priority ranking.
------------------------------------------------------------------------

impactRank : Monster3BProofLeaf → Nat
impactRank restrictionAlgorithmImplemented = 0
impactRank exactHeadRestrictionReplay = 1
impactRank heisenbergUniquenessOrActionIdentification = 2
impactRank actualTensorConstituentIdentification = 3
impactRank base369PeriodicIntertwiner = 4
impactRank structuredFiftyThreeExcessIdentification = 5
impactRank largerMonsterRepresentationPromotion = 6

replayRanksBeforeGeometryPromotion :
  impactRank exactHeadRestrictionReplay ≡ 1
replayRanksBeforeGeometryPromotion = refl

heisenbergAuthorityImmediatelyFollowsReplay :
  impactRank nextMathematicalLeafAfterReplay ≡ 2
heisenbergAuthorityImmediatelyFollowsReplay = refl

fullPromotionRanksAfterResidualAudit :
  impactRank largerMonsterRepresentationPromotion ≡ 6
fullPromotionRanksAfterResidualAudit = refl
