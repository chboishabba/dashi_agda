module DASHI.Moonshine.OggSSPClimbingGymEmpiricalDiscriminatorTerminalExact where

------------------------------------------------------------------------
-- EMPIRICAL DISCRIMINATOR TERMINAL
--
-- This owner composes the two strongest phase/address experiments without
-- inventing a third statistic after seeing their results.
--
-- 1. Multiplicative p^(i gamma) centered contrast:
--    discovery raw coherence rank      541 / 15504
--    discovery Landau-residual rank    248 / 15504
--    held-out raw rank                1067 / 15504
--    held-out Landau-residual rank    7367 / 15504
--
-- 2. Predeclared native p-radix depth-one occupancy discriminator:
--    discovery two-sided rank         7074 / 15504
--    held-out two-sided rank         10449 / 15504
--
-- The first experiment's exploratory discovery tail fails on the disjoint
-- held-out zero window, while the independently predeclared SSP-address test is
-- non-extreme on both windows.  The finite empirical max-cut therefore closes
-- in the conservative direction: no replicated Ogg-specific discriminator has
-- been established by these tests.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPClimbingGymDirichletPhaseExact as Dirichlet
import DASHI.Moonshine.OggSSPClimbingGymAddressDiscriminatorResultExact as Address

record EmpiricalDiscriminatorTerminal : Set where
  constructor empirical-discriminator-terminal
  field
    dirichletDiscoveryExploratoryTailObserved : Bool
    dirichletHeldOutNoReplication : Bool
    nativeAddressBothWindowsNonExtreme : Bool
    independentControlFamiliesUsed : Bool
    exhaustiveBalancedRanksComputed : Bool
    randomizationExactnessHypothesisSeparatelyRequired : Bool

    monsterSpecificEmpiricalDiscriminatorEstablished : Bool
    moonshineMechanismEstablished : Bool
    zetaParametrisationEstablished : Bool
    riemannHypothesisEvidenceEstablished : Bool
    universalNoOggSignalTheoremEstablished : Bool

open EmpiricalDiscriminatorTerminal public

canonicalEmpiricalDiscriminatorTerminal : EmpiricalDiscriminatorTerminal
canonicalEmpiricalDiscriminatorTerminal =
  empirical-discriminator-terminal
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
    false

------------------------------------------------------------------------
-- Exact cross-owner consistency pins.
------------------------------------------------------------------------

dirichletDiscoveryResidualRank : Dirichlet.discoveryLandauResidualCoherenceUpperOrEqual ≡ 248
dirichletDiscoveryResidualRank = refl

dirichletHeldOutResidualRank : Dirichlet.heldOutLandauResidualCoherenceUpperOrEqual ≡ 7367
dirichletHeldOutResidualRank = refl

addressDiscoveryRank : Address.discoveryTwoSidedTailCount ≡ 7074
addressDiscoveryRank = refl

addressHeldOutRank : Address.heldOutTwoSidedTailCount ≡ 10449
addressHeldOutRank = refl

dirichletDoesNotPromoteMonster :
  Dirichlet.heldOutReplicatedMonsterSpecificAnomaly
    Dirichlet.canonicalDirichletPhaseBoundary
  ≡ false
dirichletDoesNotPromoteMonster = refl

addressDoesNotPromoteMonster :
  Address.addressDiscriminatorPromotesMonster
    Address.canonicalAddressDiscriminatorResultBoundary
  ≡ false
addressDoesNotPromoteMonster = refl
