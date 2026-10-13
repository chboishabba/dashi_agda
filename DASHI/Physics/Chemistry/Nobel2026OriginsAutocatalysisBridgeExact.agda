module DASHI.Physics.Chemistry.Nobel2026OriginsAutocatalysisBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Origins.AutocatalyticCompartmentBoundary as Origins
import DASHI.Physics.Chemistry.AsymmetricChiralDynamicsExact as Dynamics
import DASHI.Physics.Chemistry.Nobel2026KaganSoaiAsymmetricAutocatalysisExact as Nobel

------------------------------------------------------------------------
-- ORIGINS-OF-LIFE CROSS-POLLINATION WITHOUT PROMOTION
--
-- We instantiate the existing prebiotic chemical-system *interface* with the
-- finite Soai feedback step.  The adapter deliberately has no compartment
-- witness: `Compartments` is bottom.  Thus the chemistry can inhabit the
-- autocatalysis coordinate while an AutocatalyticCompartmentWitness is
-- impossible in this fixture.
------------------------------------------------------------------------

soaiMatchesAmplify :
  (x : Dynamics.ChiralBiasState) →
  Nobel.soaiStep x ≡ Dynamics.amplifyBias x
soaiMatchesAmplify Dynamics.leftAmplified = refl
soaiMatchesAmplify Dynamics.leftSeed = refl
soaiMatchesAmplify Dynamics.racemic = refl
soaiMatchesAmplify Dynamics.rightSeed = refl
soaiMatchesAmplify Dynamics.rightAmplified = refl

soaiOriginsAdapter : Origins.PrebioticChemicalSystem
soaiOriginsAdapter = record
  { State = Dynamics.ChiralBiasState
  ; Environment = ⊤
  ; Reaction = ⊤
  ; Gradient = ⊤
  ; Compartment = ⊤
  ; step = λ _ _ x → Nobel.soaiStep x
  ; gradientAt = λ _ _ → tt
  ; DissipatesGradient = λ _ _ _ → tt ≡ tt
  ; Autocatalytic = λ _ x → Nobel.soaiStep x ≡ Dynamics.amplifyBias x
  ; Compartments = λ _ _ → ⊥
  ; Persists = λ x → Dynamics.amplifyBias x ≡ x
  }

leftSeedAutocatalytic :
  Origins.PrebioticChemicalSystem.Autocatalytic
    soaiOriginsAdapter tt Dynamics.leftSeed
leftSeedAutocatalytic = soaiMatchesAmplify Dynamics.leftSeed

rightSeedAutocatalytic :
  Origins.PrebioticChemicalSystem.Autocatalytic
    soaiOriginsAdapter tt Dynamics.rightSeed
rightSeedAutocatalytic = soaiMatchesAmplify Dynamics.rightSeed

leftAmplifiedPersists :
  Origins.PrebioticChemicalSystem.Persists
    soaiOriginsAdapter Dynamics.leftAmplified
leftAmplifiedPersists = Dynamics.leftAmplifiedFixed

rightAmplifiedPersists :
  Origins.PrebioticChemicalSystem.Persists
    soaiOriginsAdapter Dynamics.rightAmplified
rightAmplifiedPersists = Dynamics.rightAmplifiedFixed

noAutocatalyticCompartmentWitness :
  Origins.AutocatalyticCompartmentWitness soaiOriginsAdapter → ⊥
noAutocatalyticCompartmentWitness witness =
  Origins.AutocatalyticCompartmentWitness.enclosed witness

record Nobel2026OriginsBridgeBoundary : Set where
  constructor nobel2026OriginsBridgeBoundary
  field
    soaiFeedbackFitsExistingAutocatalysisInterface : Bool
    amplifiedBranchesFitExistingPersistenceCoordinate : Bool
    compartmentWitnessConstructed : Bool
    heredityConstructed : Bool
    agencyConstructed : Bool
    evolutionConstructed : Bool
    lifeConstructed : Bool

canonicalNobel2026OriginsBridgeBoundary : Nobel2026OriginsBridgeBoundary
canonicalNobel2026OriginsBridgeBoundary =
  nobel2026OriginsBridgeBoundary true true false false false false false
