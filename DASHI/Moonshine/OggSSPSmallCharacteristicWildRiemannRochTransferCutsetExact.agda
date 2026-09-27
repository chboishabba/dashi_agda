module DASHI.Moonshine.OggSSPSmallCharacteristicWildRiemannRochTransferCutsetExact where

------------------------------------------------------------------------
-- WILD RIEMANN--ROCH / INERTIA TRANSFER CUTSET
--
-- SOURCE CONTEXT
--
-- Tame positive-characteristic stacks are singled out precisely because finite
-- stabilizers are linearly reductive and quotient/inertia/cohomology operations
-- have better exactness properties.  The small-characteristic elliptic-moduli
-- points used here are WILD, not tame.
--
-- CONSEQUENCE
--
-- One cannot justify the candidate rule
--
--   one valuation copy per wild layer per local sector
--
-- merely by citing a tame orbifold/inertia Riemann--Roch decomposition.
--
-- A valid analytic promotion must supply one of:
--
--   * a genuinely wild Riemann--Roch / Artin--Schreier root-stack theorem;
--   * a theorem comparing the wild local object to an admissible tame model
--     with the required multiplicities;
--   * a direct q-expansion/Hauptmodul calculation independent of tame RR.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPSmallCharacteristicWildLayerSectorProductCandidateExact as LayerSector
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Distinguish tame and wild theorem classes.
------------------------------------------------------------------------

data StackRamificationRegime : Set where
  tameRegime :
    StackRamificationRegime
  wildRegime :
    StackRamificationRegime

p2Regime : StackRamificationRegime
p2Regime = wildRegime

p3Regime : StackRamificationRegime
p3Regime = wildRegime

data RiemannRochAuthorityKind : Set where
  tameInertiaLocalization :
    RiemannRochAuthorityKind

  wildRootStackRiemannRoch :
    RiemannRochAuthorityKind

  directCorrectedQExpansion :
    RiemannRochAuthorityKind

  provedTameToWildComparison :
    RiemannRochAuthorityKind

------------------------------------------------------------------------
-- 2. What an admissible wild transfer theorem must pay.
------------------------------------------------------------------------

record WildSectorMultiplicityAuthority : Set₁ where
  field
    authorityKind :
      RiemannRochAuthorityKind

    tameOnly :
      Bool

    tameOnlyIsFalse :
      tameOnly ≡ false

    layerSectorAuthority :
      LayerSector.WildLayerSectorValuationAuthority

    localCohomologyOrValuationConstructionOwned :
      Bool

    localCohomologyOrValuationConstructionOwnedIsTrue :
      localCohomologyOrValuationConstructionOwned ≡ true

    wildRamificationDataUsed :
      Bool

    wildRamificationDataUsedIsTrue :
      wildRamificationDataUsed ≡ true

    oneCopyPerLayerPerSectorDerived :
      Bool

    oneCopyPerLayerPerSectorDerivedIsTrue :
      oneCopyPerLayerPerSectorDerived ≡ true

open WildSectorMultiplicityAuthority public

------------------------------------------------------------------------
-- 3. Tame-only authority cannot inhabit the wild cut.
------------------------------------------------------------------------

record TameOnlySectorAuthority : Set where
  constructor tame-only-sector-authority
  field
    usesOnlyLinearlyReductiveInertia :
      Bool

    usesOnlyLinearlyReductiveInertiaIsTrue :
      usesOnlyLinearlyReductiveInertia ≡ true

data TameOnlyAuthorityClosesWildMonsterBridge : Set where
data TameInertiaSectorsAutomaticallyGiveWildValuationMultiplicity : Set where
data ConjugacyClassCountAutomaticallyGivesWildRiemannRochTerm : Set where

tameOnlyAuthorityDoesNotCloseWildBridge :
  TameOnlyAuthorityClosesWildMonsterBridge -> ⊥
tameOnlyAuthorityDoesNotCloseWildBridge ()

tameInertiaDoesNotAutomaticallyGiveWildMultiplicity :
  TameInertiaSectorsAutomaticallyGiveWildValuationMultiplicity -> ⊥
tameInertiaDoesNotAutomaticallyGiveWildMultiplicity ()

conjugacyCountDoesNotAutomaticallyGiveWildRR :
  ConjugacyClassCountAutomaticallyGivesWildRiemannRochTerm -> ⊥
conjugacyCountDoesNotAutomaticallyGiveWildRR ()

------------------------------------------------------------------------
-- 4. Accepted proof routes.
------------------------------------------------------------------------

data AcceptedWildProofRoute : Set where
  artinSchreierRootStackCohomology :
    AcceptedWildProofRoute

  wildRiemannRoch :
    AcceptedWildProofRoute

  directHauptmodulValuation :
    AcceptedWildProofRoute

  explicitTameToWildComparison :
    AcceptedWildProofRoute

record WildProofRouteReceipt : Set where
  constructor wild-proof-route-receipt
  field
    route :
      AcceptedWildProofRoute

    handlesP2WildPoint :
      Bool

    handlesP2WildPointIsTrue :
      handlesP2WildPoint ≡ true

    handlesP3WildPoint :
      Bool

    handlesP3WildPointIsTrue :
      handlesP3WildPoint ≡ true

    provesRequiredMultiplicity :
      Bool

    provesRequiredMultiplicityIsTrue :
      provesRequiredMultiplicity ≡ true

------------------------------------------------------------------------
-- 5. Attribution boundary.
------------------------------------------------------------------------

data AbramovichOlssonVistoliProveMonsterCorrection : Set where
data ToenRiemannRochProvesWildLayerSectorRuleHere : Set where
data WildStackRootDescriptionAloneProvesMultiplicity : Set where

aovNotCreditedWithMonsterCorrection :
  AbramovichOlssonVistoliProveMonsterCorrection -> ⊥
aovNotCreditedWithMonsterCorrection ()

toenNotSilentlyPromotedToWildLayerSectorRule :
  ToenRiemannRochProvesWildLayerSectorRuleHere -> ⊥
toenNotSilentlyPromotedToWildLayerSectorRule ()

rootDescriptionAloneDoesNotProveMultiplicity :
  WildStackRootDescriptionAloneProvesMultiplicity -> ⊥
rootDescriptionAloneDoesNotProveMultiplicity ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record WildRiemannRochTransferCutsetBoundary : Set where
  constructor wild-riemann-roch-transfer-cutset-boundary
  field
    p2ClassifiedWild : Bool
    p3ClassifiedWild : Bool
    tameOnlySectorArgumentRejected : Bool
    wildSpecificAuthoritySpecified : Bool
    acceptedWildProofRoutesEnumerated : Bool
    oneCopyPerLayerPerSectorCurrentlyProved : Bool
    tameRRPromotedToMonsterCorrection : Bool
    attributionFirewallPreserved : Bool

canonicalWildRiemannRochTransferCutsetBoundary :
  WildRiemannRochTransferCutsetBoundary
canonicalWildRiemannRochTransferCutsetBoundary =
  wild-riemann-roch-transfer-cutset-boundary
    true true true true true false false true
