module DASHI.Physics.Closure.NSCompactGammaOfficialDataObstruction where

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations

------------------------------------------------------------------------
-- Rigorous obstruction to the all-data-initially-admissible route.
--
-- The zero solution is in the official smooth divergence-free finite-energy
-- class.  Any compact-Gamma chart that demands a strictly positive packet
-- denominator excludes that solution.  Consequently the official class cannot
-- be covered by a single theorem asserting positive packet energy at t = 0 for
-- every datum.  The zero solution must be split off, or the proof must use
-- entry-before-singularity or a universal replacement/atlas mechanism.
------------------------------------------------------------------------

record ZeroDatumPacketFloorObstruction
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    initialTime : Time S
    zeroDatum : InitialDatum S
    zeroSolution : Solution S

    zeroIsOfficial : SmoothDivergenceFreeFiniteEnergy S zeroDatum
    zeroSolves : SolvesFrom S zeroDatum zeroSolution

    PacketEnergyPositive : Solution S → Time S → Set i
    admissibleImpliesPositivePacketEnergy :
      CompactGammaAdmissible S zeroSolution initialTime →
      PacketEnergyPositive zeroSolution initialTime

    zeroPacketEnergyNotPositive :
      PacketEnergyPositive zeroSolution initialTime → ⊥

open ZeroDatumPacketFloorObstruction public

zero-datum-refutes-all-data-initial-admissibility :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  ZeroDatumPacketFloorObstruction S →
  AllDataInitiallyAdmissible S → ⊥
zero-datum-refutes-all-data-initial-admissibility O A₀ =
  zeroPacketEnergyNotPositive O
    (admissibleImpliesPositivePacketEnergy O
      (everyOfficialDatumStartsAdmissible A₀
        (zeroDatum O)
        (zeroSolution O)
        (zeroIsOfficial O)
        (zeroSolves O)))

record OfficialCoverageAfterInitialObstruction
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    zeroObstruction : ZeroDatumPacketFloorObstruction S
    coverage : OfficialDataCoverage S

open OfficialCoverageAfterInitialObstruction public

official-coverage-must-use-entry-or-replacement :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  OfficialCoverageAfterInitialObstruction S →
  EverySolutionEntersBeforeSingularity S
  ⊎ UniversalReplacementMechanism S
official-coverage-must-use-entry-or-replacement C with coverage C
... | inj₁ starts = absurd
  (zero-datum-refutes-all-data-initial-admissibility
    (zeroObstruction C) starts)
  where
  absurd : ⊥ →
    EverySolutionEntersBeforeSingularity _
    ⊎ UniversalReplacementMechanism _
  absurd ()
... | inj₂ surviving = surviving
