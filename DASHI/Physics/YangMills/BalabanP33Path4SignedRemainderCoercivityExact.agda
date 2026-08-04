module DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- PURPOSE AND DASHI CONTRIBUTION
--
-- Close the sign-sensitive scalar step in the physical P33 argument on the
-- repository's literal side-four rational bond carrier.  The existing exact
-- path-four LDL certificate gives the reference floor 1/16.  The five physical
-- Hessian channels have total coefficient 256.  Choosing radius 1/8192 spends
-- exactly 1/32 of the reference floor.  A genuine signed lower bound
--
--   -(1/32)||v||^2 <= R_A(v)
--
-- therefore proves
--
--   (1/32)||v||^2 <= H_0(v) + R_A(v).
--
-- This replaces the former opaque "physical energy lower from absolute
-- remainder" socket.  An upper bound R_A(v) <= epsilon is not enough for
-- coercivity; the lower side, or an absolute-value estimate implying it, is
-- mathematically essential.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
open import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate using
  (oneSixteenth)
open import DASHI.Physics.YangMills.CompactLieProofLevel

p33PhysicalFloor p33SmallFieldRadius : ℚ
p33PhysicalFloor = + 1 / 32
p33SmallFieldRadius = + 1 / 8192

p33ReferenceFloorSplitsExactly :
  p33PhysicalFloor + p33PhysicalFloor ≡ oneSixteenth
p33ReferenceFloorSplitsExactly = ℚRing.solve []

p33RadiusSpendsHalfReferenceExactly :
  Constants.configuredTotalCoefficient * p33SmallFieldRadius
  ≡ p33PhysicalFloor
p33RadiusSpendsHalfReferenceExactly = ℚRing.solve []

p33RadiusSpendsHalfReferenceScaledExactly : ∀ normSq →
  Constants.configuredTotalCoefficient * p33SmallFieldRadius * normSq
  ≡ p33PhysicalFloor * normSq
p33RadiusSpendsHalfReferenceScaledExactly = ℚRing.solve-∀

p33HalfFloorCancellationIdentity : ∀ normSq →
  p33PhysicalFloor * normSq
  ≡ oneSixteenth * normSq + - (p33PhysicalFloor * normSq)
p33HalfFloorCancellationIdentity = ℚRing.solve-∀

physicalHessianEnergy : ℚ → ℚ → ℚ
physicalHessianEnergy referenceEnergy signedRemainder =
  referenceEnergy + signedRemainder

path4SignedRemainderCoercive :
  ∀ field gaugeFixingEnergy blockPenaltyEnergy signedRemainder →
  Hodge.BondComponentMeanZero field →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  - (p33PhysicalFloor * Hodge.bondNormSq field) ≤ signedRemainder →
  p33PhysicalFloor * Hodge.bondNormSq field
  ≤ physicalHessianEnergy
      (Hodge.referenceHodgeEnergy
        field gaugeFixingEnergy blockPenaltyEnergy)
      signedRemainder
path4SignedRemainderCoercive
    field gaugeFixingEnergy blockPenaltyEnergy signedRemainder
    meanZero gaugeNonnegative blockNonnegative remainderLower =
  subst
    (λ lower → lower ≤
      physicalHessianEnergy
        (Hodge.referenceHodgeEnergy
          field gaugeFixingEnergy blockPenaltyEnergy)
        signedRemainder)
    (sym (p33HalfFloorCancellationIdentity (Hodge.bondNormSq field)))
    (ℚP.+-mono-≤
      (Hodge.path4BondReferenceHodgeCoercivity
        field gaugeFixingEnergy blockPenaltyEnergy
        meanZero gaugeNonnegative blockNonnegative)
      remainderLower)

path4ConfiguredRadiusRemainderLowerImpliesPhysicalLower :
  ∀ field signedRemainder →
  - (Constants.configuredTotalCoefficient
      * p33SmallFieldRadius
      * Hodge.bondNormSq field)
  ≤ signedRemainder →
  - (p33PhysicalFloor * Hodge.bondNormSq field)
  ≤ signedRemainder
path4ConfiguredRadiusRemainderLowerImpliesPhysicalLower
    field signedRemainder configuredLower =
  subst
    (λ lower → lower ≤ signedRemainder)
    (cong -_
      (p33RadiusSpendsHalfReferenceScaledExactly
        (Hodge.bondNormSq field)))
    configuredLower

path4ConfiguredRadiusPhysicalCoercive :
  ∀ field gaugeFixingEnergy blockPenaltyEnergy signedRemainder →
  Hodge.BondComponentMeanZero field →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  - (Constants.configuredTotalCoefficient
      * p33SmallFieldRadius
      * Hodge.bondNormSq field)
  ≤ signedRemainder →
  p33PhysicalFloor * Hodge.bondNormSq field
  ≤ physicalHessianEnergy
      (Hodge.referenceHodgeEnergy
        field gaugeFixingEnergy blockPenaltyEnergy)
      signedRemainder
path4ConfiguredRadiusPhysicalCoercive
    field gaugeFixingEnergy blockPenaltyEnergy signedRemainder
    meanZero gaugeNonnegative blockNonnegative configuredLower =
  path4SignedRemainderCoercive
    field gaugeFixingEnergy blockPenaltyEnergy signedRemainder
    meanZero gaugeNonnegative blockNonnegative
    (path4ConfiguredRadiusRemainderLowerImpliesPhysicalLower
      field signedRemainder configuredLower)

p33Path4ReferenceFloorLevel : ProofLevel
p33Path4ReferenceFloorLevel = machineChecked

p33ConfiguredRadiusArithmeticLevel : ProofLevel
p33ConfiguredRadiusArithmeticLevel = machineChecked

p33SignedRemainderCoercivityLevel : ProofLevel
p33SignedRemainderCoercivityLevel = machineChecked
