module DASHI.Physics.Quantum.CircularRydbergRoomTemperatureLifetimeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Einius Pultinevicius, Aaron Götzelmann, Fabian Thielemann,
-- Christian Hölzl, Florian Meinert, et al.
-- "Long-lived giant circular Rydberg atoms at room temperature"
-- Nature Communications 17, 9834 (2026).
-- DOI: 10.1038/s41467-026-77764-x
-- Published: 2026-09-15.
--
-- Source-bounded claims used here:
--   * individually trapped circular Rydberg atoms with state lifetimes >10 ms;
--   * Purcell suppression of room-temperature blackbody modes yields >20-fold
--     suppression of BBR-induced decay relative to the unsuppressed setting;
--   * coherent control up to principal quantum number n = 103;
--   * optical-tweezer trapping on the hundred-millisecond scale.
--
-- The source motivates neutral-atom quantum computing/simulation.  Citation
-- does not itself prove a target-Hamiltonian encoding, a simulator error bound,
-- a Yang--Mills theorem, or any spectral-gap statement.
------------------------------------------------------------------------

pultinevicius2026 : Source.AttributedSource
pultinevicius2026 =
  Source.mkDOISource
    "Einius Pultinevicius; Aaron Götzelmann; Fabian Thielemann; Christian Hölzl; Florian Meinert; et al."
    "Long-lived giant circular Rydberg atoms at room temperature"
    "Nature Communications 17, 9834"
    "2026"
    "10.1038/s41467-026-77764-x"
    "https://doi.org/10.1038/s41467-026-77764-x"
    Source.academicArticleSource
    "primary experimental source for circular-Rydberg preparation, lifetime, blackbody-mode suppression, n=103 control, and tweezer-storage claims; not imported as simulator or Yang--Mills proof authority"
    Source.publicAttribution

sourceDOIIsPinned :
  Source.doiState pultinevicius2026
  ≡ Source.doiRecorded "10.1038/s41467-026-77764-x"
sourceDOIIsPinned = refl

data LifetimeCoordinate : Set where
  circularElectronicStateLifetime : LifetimeCoordinate
  opticalTweezerRetentionLifetime : LifetimeCoordinate

stateLifetimeIsNotTrapLifetime :
  circularElectronicStateLifetime ≡ opticalTweezerRetentionLifetime → ⊥
stateLifetimeIsNotTrapLifetime ()

data ProtectionCoordinate : Set where
  angularMomentumSelectionRuleProtection : ProtectionCoordinate
  environmentalBlackbodyModeSuppression : ProtectionCoordinate

purcellSuppressionIsNotIntrinsicProtection :
  environmentalBlackbodyModeSuppression
  ≡ angularMomentumSelectionRuleProtection → ⊥
purcellSuppressionIsNotIntrinsicProtection ()

record CircularRydbergExperimentalClaimSurface : Set where
  field
    species : String
    principalQuantumNumberUpperControlled : String
    stateLifetimeLowerBound : String
    blackbodyInducedDecaySuppression : String
    tweezerRetentionScale : String
    stateLifetimeCoordinate : LifetimeCoordinate
    trapLifetimeCoordinate : LifetimeCoordinate
    intrinsicProtectionCoordinate : ProtectionCoordinate
    environmentalProtectionCoordinate : ProtectionCoordinate
    source : Source.AttributedSource

open CircularRydbergExperimentalClaimSurface public

pultineviciusCircularRydbergSurface : CircularRydbergExperimentalClaimSurface
pultineviciusCircularRydbergSurface =
  record
    { species = "88Sr"
    ; principalQuantumNumberUpperControlled = "n = 103"
    ; stateLifetimeLowerBound = "> 10 ms"
    ; blackbodyInducedDecaySuppression = "> 20-fold BBR-induced decay suppression"
    ; tweezerRetentionScale = "hundred-millisecond scale"
    ; stateLifetimeCoordinate = circularElectronicStateLifetime
    ; trapLifetimeCoordinate = opticalTweezerRetentionLifetime
    ; intrinsicProtectionCoordinate = angularMomentumSelectionRuleProtection
    ; environmentalProtectionCoordinate = environmentalBlackbodyModeSuppression
    ; source = pultinevicius2026
    }

stateAndTrapCoordinatesRemainDistinct :
  stateLifetimeCoordinate pultineviciusCircularRydbergSurface
  ≡ trapLifetimeCoordinate pultineviciusCircularRydbergSurface → ⊥
stateAndTrapCoordinatesRemainDistinct = stateLifetimeIsNotTrapLifetime

intrinsicAndEnvironmentalProtectionRemainDistinct :
  environmentalProtectionCoordinate pultineviciusCircularRydbergSurface
  ≡ intrinsicProtectionCoordinate pultineviciusCircularRydbergSurface → ⊥
intrinsicAndEnvironmentalProtectionRemainDistinct =
  purcellSuppressionIsNotIntrinsicProtection
