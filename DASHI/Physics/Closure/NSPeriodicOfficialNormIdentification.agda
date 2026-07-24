module DASHI.Physics.Closure.NSPeriodicOfficialNormIdentification where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact carrier-matching surface for the official periodic Fourier norms.
--
-- This module does not identify a finite numerical matrix norm with the PDE norm
-- by assertion.  Instead it records every equality and cutoff-uniform operator
-- estimate required for that identification.  The shell quantities match the
-- repository's concrete Bernstein chain exactly:
--
--   ||P_j omega||_2 <= curlWeightedShell_j,
--   ||P_j omega||_infinity <= curlWeightedShell_j,
--   curlWeightedShell_j = 2^(5j/2) ||P_j u||_2
--
-- in the selected scalar realization.
------------------------------------------------------------------------

record OfficialPeriodicNormIdentification
    {c sh st : Level}
    (A : AbsorptionArithmetic)
    (Cutoff : Set c)
    (Shell : Set sh)
    (State : Set st) : Set (lsuc (c ⊔ sh ⊔ st)) where
  field
    Admissible : Cutoff → State → Set (c ⊔ st)

    coefficientL2 physicalL2 hSobolevNorm : Cutoff → State → Scalar A
    shellCoefficientL2 shellPhysicalL2 :
      Cutoff → Shell → State → Scalar A

    lerayInputL2 lerayOutputL2 : Cutoff → State → Scalar A
    biotSavartVorticityL2 biotSavartVelocityH1 :
      Cutoff → State → Scalar A

    shellVelocityL2 shellVorticityL2 curlWeightedShell
      shellVorticityLInfinity :
      Cutoff → Shell → State → Scalar A

    weightedFiveHalvesShellSum vorticityLInfinity :
      Cutoff → State → Scalar A

    parsevalPlancherel : ∀ N u →
      coefficientL2 N u ≡ physicalL2 N u

    shellParsevalPlancherel : ∀ N shell u →
      shellCoefficientL2 N shell u ≡ shellPhysicalL2 N shell u

    lerayProjectionBounded : ∀ N u →
      Admissible N u →
      _≤_ A (lerayOutputL2 N u) (lerayInputL2 N u)

    biotSavartBounded : ∀ N u →
      Admissible N u →
      _≤_ A
        (biotSavartVelocityH1 N u)
        (biotSavartVorticityL2 N u)

    shellCurlEstimate : ∀ N shell u →
      Admissible N u →
      _≤_ A
        (shellVorticityL2 N shell u)
        (curlWeightedShell N shell u)

    shellBernsteinFiveHalves : ∀ N shell u →
      Admissible N u →
      _≤_ A
        (shellVorticityLInfinity N shell u)
        (curlWeightedShell N shell u)

    curlWeightedShellMeaning : ∀ N shell u →
      curlWeightedShell N shell u ≡ shellVelocityL2 N shell u

    literalHatAgreesWithOfficialShell : ∀ N shell u →
      shellCoefficientL2 N shell u ≡ shellPhysicalL2 N shell u

    weightedShellReconstructsVorticity : ∀ N u →
      Admissible N u →
      _≤_ A
        (vorticityLInfinity N u)
        (weightedFiveHalvesShellSum N u)

    -- Constants used above are independent of the Galerkin cutoff.  This is kept
    -- as a proposition rather than a Boolean or a comment so an inhabitant must
    -- expose the actual uniformity proof.
    CutoffUniform : Set (c ⊔ st)
    cutoffUniform : CutoffUniform

open OfficialPeriodicNormIdentification public

officialShellVorticityL2FromVelocity :
  ∀ {c sh st} {A : AbsorptionArithmetic}
    {Cutoff : Set c} {Shell : Set sh} {State : Set st} →
  (N : OfficialPeriodicNormIdentification A Cutoff Shell State) →
  ∀ cutoff shell state →
  Admissible N cutoff state →
  _≤_ A
    (shellVorticityL2 N cutoff shell state)
    (shellVelocityL2 N cutoff shell state)
officialShellVorticityL2FromVelocity {A = A} N cutoff shell state admissible =
  subst
    (λ rhs →
      _≤_ A
        (shellVorticityL2 N cutoff shell state)
        rhs)
    (curlWeightedShellMeaning N cutoff shell state)
    (shellCurlEstimate N cutoff shell state admissible)

officialShellVorticityFromVelocity :
  ∀ {c sh st} {A : AbsorptionArithmetic}
    {Cutoff : Set c} {Shell : Set sh} {State : Set st} →
  (N : OfficialPeriodicNormIdentification A Cutoff Shell State) →
  ∀ cutoff shell state →
  Admissible N cutoff state →
  _≤_ A
    (shellVorticityLInfinity N cutoff shell state)
    (shellVelocityL2 N cutoff shell state)
officialShellVorticityFromVelocity {A = A} N cutoff shell state admissible =
  subst
    (λ rhs →
      _≤_ A
        (shellVorticityLInfinity N cutoff shell state)
        rhs)
    (curlWeightedShellMeaning N cutoff shell state)
    (shellBernsteinFiveHalves N cutoff shell state admissible)

officialVorticityReconstruction :
  ∀ {c sh st} {A : AbsorptionArithmetic}
    {Cutoff : Set c} {Shell : Set sh} {State : Set st} →
  (N : OfficialPeriodicNormIdentification A Cutoff Shell State) →
  ∀ cutoff state →
  Admissible N cutoff state →
  _≤_ A
    (vorticityLInfinity N cutoff state)
    (weightedFiveHalvesShellSum N cutoff state)
officialVorticityReconstruction N cutoff state admissible =
  weightedShellReconstructsVorticity N cutoff state admissible

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

officialNormSurfaceDefinitionLevel : ProofLevel
officialNormSurfaceDefinitionLevel = machineChecked

periodicParsevalCarrierMatchLevel : ProofLevel
periodicParsevalCarrierMatchLevel = conditional

periodicLerayBiotSavartUniformityLevel : ProofLevel
periodicLerayBiotSavartUniformityLevel = conditional

periodicShellReconstructionLevel : ProofLevel
periodicShellReconstructionLevel = conditional

officialPeriodicNormIdentificationInhabited : Bool
officialPeriodicNormIdentificationInhabited = false
