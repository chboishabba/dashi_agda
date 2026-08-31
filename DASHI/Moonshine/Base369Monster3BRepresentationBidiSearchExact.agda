module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchExact where

------------------------------------------------------------------------
-- CONSUMER-FIRST MONSTER 3B REPRESENTATION BIDI SEARCH FRONTIER
--
-- The purpose of this owner is not to add another numerical Monster model.
-- It orders the remaining proof obligations by representation-theoretic
-- authority.  Existing exact arithmetic/model agreements are treated as
-- producers only when they feed an actual normalizer/restriction consumer.
--
-- Highest-impact route:
--
--   checked M -> MN3B restriction certificate
--   -> actual 729 x 90 tensor constituent identification
--   -> Heisenberg/Base369 periodic-fibre intertwiner
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
-- 3. Live proof/search consumers.  These are ordered by authority.
------------------------------------------------------------------------

data Monster3BProofLeaf : Set where
  checkedNormalizerRestrictionCertificate : Monster3BProofLeaf
  actualTensorConstituentIdentification : Monster3BProofLeaf
  explicitNormalizerActionOnHeisenbergFactor : Monster3BProofLeaf
  base369PeriodicIntertwiner : Monster3BProofLeaf
  structuredFiftyThreeExcessIdentification : Monster3BProofLeaf
  largerMonsterRepresentationPromotion : Monster3BProofLeaf

data LeafState : Set where
  closed : LeafState
  open : LeafState
  blocked : LeafState

leafState : Monster3BProofLeaf → LeafState
leafState checkedNormalizerRestrictionCertificate = open
leafState actualTensorConstituentIdentification = blocked
leafState explicitNormalizerActionOnHeisenbergFactor = blocked
leafState base369PeriodicIntertwiner = blocked
leafState structuredFiftyThreeExcessIdentification = blocked
leafState largerMonsterRepresentationPromotion = blocked

------------------------------------------------------------------------
-- 4. Dependency relation.  Later geometry cannot bypass earlier authority.
------------------------------------------------------------------------

data Requires : Monster3BProofLeaf → Monster3BProofLeaf → Set where
  tensorNeedsRestriction :
    Requires actualTensorConstituentIdentification checkedNormalizerRestrictionCertificate
  actionNeedsTensor :
    Requires explicitNormalizerActionOnHeisenbergFactor actualTensorConstituentIdentification
  base369NeedsAction :
    Requires base369PeriodicIntertwiner explicitNormalizerActionOnHeisenbergFactor
  fiftyThreeNeedsRestriction :
    Requires structuredFiftyThreeExcessIdentification checkedNormalizerRestrictionCertificate
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
highestImpactLiveLeaf = checkedNormalizerRestrictionCertificate

highestImpactLeafIsOpen : leafState highestImpactLiveLeaf ≡ open
highestImpactLeafIsOpen = refl

------------------------------------------------------------------------
-- 6. Receipt types that would actually promote the frontier.
------------------------------------------------------------------------

record NormalizerRestrictionCertificate : Set where
  constructor normalizerRestrictionCertificate
  field
    restrictionChecked : Bool
    concreteConstituentsIdentified : Bool
    sourceToTargetTableCorrespondenceChecked : Bool
open NormalizerRestrictionCertificate public

record HeisenbergTensorFactorisationReceipt : Set where
  constructor heisenbergTensorFactorisationReceipt
  field
    restrictionReceipt : NormalizerRestrictionCertificate
    heisenbergCarrierReallyActs : Bool
    multiplicityCarrierReallyActs : Bool
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
    restrictionReceipt53 : NormalizerRestrictionCertificate
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
    actualNormalizerRestrictionCertificateAvailable : Bool
    actualTensorConstituentIdentificationAvailable : Bool
    base369NormalizerIntertwinerAvailable : Bool
    structured53ExcessIdentificationAvailable : Bool
    fullMonsterRepresentationProvedHere : Bool
    fiftyThreeCountAloneClosesResidualLeaf : Bool
    shared729CountAloneClosesTensorLeaf : Bool
open Monster3BRepresentationSearchBoundary public

canonicalMonster3BRepresentationSearchBoundary : Monster3BRepresentationSearchBoundary
canonicalMonster3BRepresentationSearchBoundary =
  monster3BRepresentationSearchBoundary
    true true true
    false false false false false
    false false

------------------------------------------------------------------------
-- 9. Scientific-priority statement encoded as a finite ranking.
------------------------------------------------------------------------

impactRank : Monster3BProofLeaf → Nat
impactRank checkedNormalizerRestrictionCertificate = 0
impactRank actualTensorConstituentIdentification = 1
impactRank explicitNormalizerActionOnHeisenbergFactor = 2
impactRank base369PeriodicIntertwiner = 3
impactRank structuredFiftyThreeExcessIdentification = 4
impactRank largerMonsterRepresentationPromotion = 5

restrictionRanksBeforeGeometryPromotion :
  impactRank checkedNormalizerRestrictionCertificate ≡ 0
restrictionRanksBeforeGeometryPromotion = refl

fullPromotionRanksAfterResidualAudit :
  impactRank largerMonsterRepresentationPromotion ≡ 5
fullPromotionRanksAfterResidualAudit = refl
