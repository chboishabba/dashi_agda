module DASHI.Analysis.NonArchimedeanMonster3BDyadicCorrespondenceBidiExact where

------------------------------------------------------------------------
-- NON-ARCHIMEDEAN / MONSTER 3B DYADIC CORRESPONDENCE BIDI LADDER
--
-- Existing DASHI Monster machinery already exposes a dyadic bulk
--
--   65536 = 2^16
--
-- inside each C3 phase multiplicity of the 3B chart.  The source spectral
-- system's twisted block at level n is indexed by Z/2^(n-1)Z, so level 17 has
-- the same finite cardinality 2^16.
--
-- This module records that exact cardinality alignment as a candidate bridge,
-- while refusing every stronger representation-theoretic promotion until the
-- corresponding producer is supplied.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as M3B
import DASHI.Moonshine.Monster3BKernelCharacterCriterionExact as Kernel

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 * pow2 n

sourceTwistedLevel : Nat
sourceTwistedLevel = 17

sourceTwistedExponent : Nat
sourceTwistedExponent = 16

sourceTwistedCardinalityAt17 : Nat
sourceTwistedCardinalityAt17 = pow2 sourceTwistedExponent

sourceTwistedCardinalityAt17Is65536 :
  sourceTwistedCardinalityAt17 ≡ 65536
sourceTwistedCardinalityAt17Is65536 = refl

monsterDyadicBaselineIs65536 :
  M3B.dyadicPhaseBaseline ≡ 65536
monsterDyadicBaselineIs65536 = refl

source17MatchesMonsterDyadicBaseline :
  sourceTwistedCardinalityAt17 ≡ M3B.dyadicPhaseBaseline
source17MatchesMonsterDyadicBaseline = refl

------------------------------------------------------------------------
-- Correspondence ladder.
------------------------------------------------------------------------

data CorrespondenceStrength : Set where
  sameCardinality : CorrespondenceStrength
  sameDyadicMultiplicityCoordinate : CorrespondenceStrength
  compatiblePhaseFibre : CorrespondenceStrength
  classCharacterAgreement : CorrespondenceStrength
  operatorIntertwiner : CorrespondenceStrength
  sameRepresentation : CorrespondenceStrength

record MonsterDyadicCorrespondenceStatus : Set where
  constructor monster-dyadic-correspondence-status
  field
    cardinalityMatchOwned : Bool
    dyadicBulkArithmeticOwned : Bool
    c3PhaseMultiplicityChartOwned : Bool
    sourceActionIdentifiedWithMonsterAction : Bool
    actualKernelClassCharacterAgreementOwned : Bool
    sourceMonsterOperatorIntertwinerOwned : Bool
    sameRepresentationOwned : Bool

canonicalMonsterDyadicCorrespondenceStatus :
  MonsterDyadicCorrespondenceStatus
canonicalMonsterDyadicCorrespondenceStatus =
  monster-dyadic-correspondence-status
    true true true false false false false

------------------------------------------------------------------------
-- Strongest currently promotable statement.
------------------------------------------------------------------------

currentPromotion : CorrespondenceStrength
currentPromotion = sameDyadicMultiplicityCoordinate

------------------------------------------------------------------------
-- Reverse obligations for stronger claims.
------------------------------------------------------------------------

data MonsterCorrespondenceObligation : Set where
  needSourceToMonsterPhaseFibreMap : MonsterCorrespondenceObligation
  needActualKernelClassMap : MonsterCorrespondenceObligation
  needClassCharacterEquality : MonsterCorrespondenceObligation
  needSourceMonsterOperatorIntertwiner : MonsterCorrespondenceObligation
  needRepresentationEquivalenceReceipt : MonsterCorrespondenceObligation

reverseMonsterCutset : CorrespondenceStrength → List MonsterCorrespondenceObligation
reverseMonsterCutset sameCardinality = []
reverseMonsterCutset sameDyadicMultiplicityCoordinate = []
reverseMonsterCutset compatiblePhaseFibre =
  needSourceToMonsterPhaseFibreMap ∷ []
reverseMonsterCutset classCharacterAgreement =
  needSourceToMonsterPhaseFibreMap ∷
  needActualKernelClassMap ∷
  needClassCharacterEquality ∷ []
reverseMonsterCutset operatorIntertwiner =
  needSourceToMonsterPhaseFibreMap ∷
  needActualKernelClassMap ∷
  needClassCharacterEquality ∷
  needSourceMonsterOperatorIntertwiner ∷ []
reverseMonsterCutset sameRepresentation =
  needSourceToMonsterPhaseFibreMap ∷
  needActualKernelClassMap ∷
  needClassCharacterEquality ∷
  needSourceMonsterOperatorIntertwiner ∷
  needRepresentationEquivalenceReceipt ∷ []

------------------------------------------------------------------------
-- Critical prime/fibre firewall.
--
-- The source finite carrier is dyadic.  The Monster 3B phase decomposition is
-- C3-valued, and the kernel-character owner concerns an extraspecial 3-group.
-- The integer 2^16 is therefore a multiplicity/resolution coordinate in the
-- Monster chart, not evidence that the source Z/2^16Z action is the Monster
-- kernel action.
------------------------------------------------------------------------

record CrossPrimeFirewall : Set where
  constructor cross-prime-firewall
  field
    samePowerOfTwoImpliesSameGroupAction : Bool
    dyadicMultiplicityImpliesDyadicMonsterKernel : Bool
    c3PhaseFibreEqualsSourceDyadicCarrier : Bool
    characterAgreementImpliesIntertwinerAutomatically : Bool
    dimensionAgreementImpliesRepresentationEquivalence : Bool

canonicalCrossPrimeFirewall : CrossPrimeFirewall
canonicalCrossPrimeFirewall =
  cross-prime-firewall false false false false false

------------------------------------------------------------------------
-- Reuse the Monster kernel-character promotion discipline explicitly.
------------------------------------------------------------------------

monsterKernelCharacterStillNeedsActualCoverage :
  Kernel.actualMN3BClassCoverageCertified
    Kernel.canonicalKernelCharacterPromotionBoundary
  ≡ false
monsterKernelCharacterStillNeedsActualCoverage =
  Kernel.actualMN3BClassCoverageCertifiedIsFalse
    Kernel.canonicalKernelCharacterPromotionBoundary

monsterKernelCharacterStillNeedsCertificate :
  Kernel.actualKernelCharacterCertificateConstructed
    Kernel.canonicalKernelCharacterPromotionBoundary
  ≡ false
monsterKernelCharacterStillNeedsCertificate =
  Kernel.actualKernelCharacterCertificateConstructedIsFalse
    Kernel.canonicalKernelCharacterPromotionBoundary

monsterCharacterEqualityDoesNotYetGiveIntertwiner :
  Kernel.actualCharacterEqualityPromotedToIntertwiner
    Kernel.canonicalKernelCharacterPromotionBoundary
  ≡ false
monsterCharacterEqualityDoesNotYetGiveIntertwiner =
  Kernel.actualCharacterEqualityPromotedToIntertwinerIsFalse
    Kernel.canonicalKernelCharacterPromotionBoundary
