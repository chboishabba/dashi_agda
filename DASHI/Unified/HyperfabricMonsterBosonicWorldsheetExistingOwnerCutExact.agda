module DASHI.Unified.HyperfabricMonsterBosonicWorldsheetExistingOwnerCutExact where

-- Source-native bridge; deliberately NO new VOA, BRST or string ontology.
--
-- PRIOR MATHEMATICS: FLM V^natural has chiral c=24; a Lorentzian
-- even unimodular rank-two lattice II_{1,1} has c=2; the standard
-- bosonic worldsheet reparametrization bc ghost sector has c=-26.
-- The algebraic charge cancellation (24+2)-26=0 is a NECESSARY
-- bookkeeping check. It is not a proof of Weyl gauge consistency,
-- BRST nilpotence, no-ghost positive physical-state cohomology,
-- a path integral, a worldsheet sigma model or physical target space.
--
-- OWNERS: VNaturalOrbifoldConstruction, TwistedModuleModularity,
-- MoonshineMonsterLieStringBigradingExact, and CalabiYau369CompactFibreBridge.
-- This file does not synthesize nonexistent Vnatural/II11/BRST constructors.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN
import DASHI.Biology.MoonshineMonsterLieStringBigradingExact as Lie
import DASHI.Geometry.CalabiYau369CompactFibreBridge as CY

monsterChiralCharge : Nat
monsterChiralCharge = 24

lorentzianII11RankTwoCharge : Nat
lorentzianII11RankTwoCharge = 2

bosonicBCGhostNegativeChargeMagnitude : Nat
bosonicBCGhostNegativeChargeMagnitude = 26

-- Required matter central charge = ghost magnitude, so signed sum is zero.
sourcedMatterChargeMatchesGhost :
  monsterChiralCharge + lorentzianII11RankTwoCharge
    ≡ bosonicBCGhostNegativeChargeMagnitude
sourcedMatterChargeMatchesGhost = refl

-- The selected Vnatural source does not come for free: its conformal
-- c=24 certificate is an EXTERNAL field in its existing orbifold assembly.
sourceDependentChargeBudget :
  (source : VN.VNaturalConstruction) →
  VN.centralCharge24 source →
  monsterChiralCharge + lorentzianII11RankTwoCharge
    ≡ bosonicBCGhostNegativeChargeMagnitude
sourceDependentChargeBudget source sourceC24 =
  sourcedMatterChargeMatchesGhost

-- The different 10D Calabi-Yau candidate describes the standard
-- 9 spatial + 1 temporal counting; it is NOT the same selected 2D
-- Lorentzian lattice c=2 tensor or a critical bosonic 10D target.
existingCYSpacetimeDimension : CY.spacetimeDimension CY.canonicalDimension369 ≡ 10
existingCYSpacetimeDimension = refl

tenFreeBosonsNeedSixteenMoreUnits : 10 + 16 ≡ 26
tenFreeBosonsNeedSixteenMoreUnits = refl

monsterPlusTenNotBosonicCritical : 24 + 10 ≡ 26 → ⊥
monsterPlusTenNotBosonicCritical ()

-- Independent 10D RNS superstring budget. Ten worldsheet coordinate
-- bosons give c=10, ten free Majorana partners c=10/2=5;
-- superconformal beta-gamma ghosts give c=+11, bc gives c=-26.
-- Unlike the Monster c=24 plus II11 c=2 bosonic route, this uses
-- super-Virasoro, NS/R spin structure and GSO/BRST conditions not built here.
rnsBosonCharge : Nat
rnsBosonCharge = 10

rnsFermionCharge : Nat
rnsFermionCharge = 5

rnsBetaGammaSuperghostCharge : Nat
rnsBetaGammaSuperghostCharge = 11

tenDimensionalRNSChargeBudget :
  rnsBosonCharge + rnsFermionCharge + rnsBetaGammaSuperghostCharge
    ≡ bosonicBCGhostNegativeChargeMagnitude
tenDimensionalRNSChargeBudget = refl

-- Reuse existing source-rooted Monster Lie root-multiplicity theorems,
-- rather than recertifying a no-ghost theorem from a character coefficient.
monsterLieRootOneOne : Lie.rootMultiplicity Lie.degreeOneOne ≡ 196884
monsterLieRootOneOne = Lie.oneOneRootMultiplicityExact

monsterLieRootOneTwo : Lie.rootMultiplicity Lie.degreeOneTwo ≡ 21493760
monsterLieRootOneTwo = Lie.oneTwoRootMultiplicityExact

rootMultiplicityNotPhysicalBRSTQuotient :
  Lie.moonshineChiralStateSpace ≡ Lie.physicalStateBRSTQuotient → ⊥
rootMultiplicityNotPhysicalBRSTQuotient ()

-- No theorem here identifies chiral Monster VOA c=24 + II11 c=2
-- with the spatial Cube27/P3^3 Hamiltonian or physical CY tenfold.
