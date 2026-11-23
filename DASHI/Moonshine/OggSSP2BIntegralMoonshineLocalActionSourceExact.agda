module DASHI.Moonshine.OggSSP2BIntegralMoonshineLocalActionSourceExact where

------------------------------------------------------------------------
-- SOURCE AUTHORITY FOR GATE A'
--
-- External mathematics already supplies the action whose existence gate A'
-- needs:
--
-- * Carnahan, "A Self-Dual Integral Form of the Moonshine Module" (SIGMA
--   2019), constructs a self-dual integral form of V^natural and proves that
--   it has Monster symmetry.  In particular the 196884-dimensional weight-two
--   representation admits a positive-definite self-dual integral form with
--   Monster action.
--
-- * ATLAS / CTblLib supply the Monster local subgroup
--
--     2^(2+11+22).(M24 x S3)
--
--   normalizing a 2B-pure Klein four.
--
-- * The repository runtime receipt explicitly extracts a pure order-three
--   element in the S3 factor which fixes the M24 quotient and cycles the three
--   nonidentity 2B labels.
--
-- Therefore the local order-three element DOES act on the integral Moonshine
-- form by restriction of the Monster action.  What remains unpaid in DASHI is
-- not existence of this action; it is the same-object formal weld from that
-- full integral carrier/action to the current source-derived 4A/Tate
-- multiplicity owner, which currently stores multiplicities rather than the
-- complete 196884-dimensional lattice.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. External source receipt.
------------------------------------------------------------------------

record IntegralMoonshineLocalActionSource : Set where
  constructor integral-moonshine-local-action-source
  field
    integralFormSource : String
    localSubgroupSource : String
    computationalRepresentationSource : String

    weightTwoRank : Nat
    localGroupShape : String

    selfDualIntegralFormConstructed : Bool
    monsterActsOnIntegralForm : Bool
    weightTwoIntegralMonsterRepresentationExists : Bool
    localGroupIsMonsterSubgroup : Bool
    localGroupNormalizesTwoBPureKleinFour : Bool
    pureOrderThreeCyclesThreeTwoBElements : Bool

    restrictedLocalActionExistsMathematically : Bool
    fullIntegralCarrierConstructedInRepo : Bool
    current4AMultiplicityOwnerIsFullCarrier : Bool
    sameObjectTateCarrierWeldPaid : Bool
    actualTateIntertwinersInstantiatedInRepo : Bool

open IntegralMoonshineLocalActionSource public

canonicalIntegralMoonshineLocalActionSource :
  IntegralMoonshineLocalActionSource
canonicalIntegralMoonshineLocalActionSource =
  integral-moonshine-local-action-source
    "Scott Carnahan, A Self-Dual Integral Form of the Moonshine Module, SIGMA 15 (2019) 030"
    "ATLAS / CTblLib: 2^(2+11+22).(M24 x S3), normalizer of a 2B-pure Klein four"
    "Conway 196884-dimensional representation; Martin Seysen mmgroup implementation"
    196884
    "2^(2+11+22).(M24 x S3)"
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false

weightTwoRankIs196884 :
  weightTwoRank canonicalIntegralMoonshineLocalActionSource ≡ 196884
weightTwoRankIs196884 = refl

externalRestrictedLocalActionIsSourced :
  restrictedLocalActionExistsMathematically
    canonicalIntegralMoonshineLocalActionSource
  ≡ true
externalRestrictedLocalActionIsSourced = refl

repoSameObjectTateCarrierWeldStillOpen :
  sameObjectTateCarrierWeldPaid canonicalIntegralMoonshineLocalActionSource
  ≡ false
repoSameObjectTateCarrierWeldStillOpen = refl

------------------------------------------------------------------------
-- 2. Promotion firewall.
------------------------------------------------------------------------

data SourcedExistenceConstructsFormalTateCarrierWeld : Set where

data ConwayRationalCoordinatesAreCarnahanIntegralBasis : Set where

sourcedExistenceDoesNotConstructFormalTateCarrierWeld :
  SourcedExistenceConstructsFormalTateCarrierWeld → ⊥
sourcedExistenceDoesNotConstructFormalTateCarrierWeld ()

conwayCoordinatesNotDeclaredCarnahanIntegralBasis :
  ConwayRationalCoordinatesAreCarnahanIntegralBasis → ⊥
conwayCoordinatesNotDeclaredCarnahanIntegralBasis ()

------------------------------------------------------------------------
-- 3. Revised A' boundary.
------------------------------------------------------------------------

record GateAPrimeStatus : Set where
  constructor gate-a-prime-status
  field
    externalIntegralMonsterActionSourced : Bool
    externalTwoBPureLocalSubgroupSourced : Bool
    externalPureC3TransportElementSourcedAndComputed : Bool
    abstractRestrictedActionExists : Bool
    genericConjugacyToTateCompilerAvailable : Bool
    formalFullIntegralCarrierOwnerAvailable : Bool
    current4ATateMultiplicityOwnerWeldedToFullCarrier : Bool
    actualTateTransportInstantiated : Bool
    nextResidual : String

canonicalGateAPrimeStatus : GateAPrimeStatus
canonicalGateAPrimeStatus =
  gate-a-prime-status
    true true true true true
    false false false
    "construct or import the full integral weight-two Monster carrier/action into the formal repo and identify the current Carnahan--Urano 4A multiplicity/Tate model with its restriction; the sourced local C3 action then compiles automatically to the three Tate-fibre intertwiners"
