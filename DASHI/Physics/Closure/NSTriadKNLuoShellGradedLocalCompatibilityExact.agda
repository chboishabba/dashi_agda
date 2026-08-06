module DASHI.Physics.Closure.NSTriadKNLuoShellGradedLocalCompatibilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Michel Bony,
-- "Calcul symbolique et propagation des singularites pour les equations aux
-- derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Shin-ichi Inage,
-- "Conditional Regularity of the Three-Dimensional Navier-Stokes Equations
-- via High-High Triadic Absorption".
-- DOI: 10.20944/preprints202603.1591.v1.
-- Status: non-peer-reviewed preprint.
--
-- DASHI CONTRIBUTION
-- Instantiate the domain-neutral graded/local/probe carrier at a fixed shell.
-- The local operation adds HH/LH/HL/comparable interaction profiles at the
-- same shell; the four coordinate probes are separating.  This is finite
-- algebra and does not supply any physical classwise bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_)

import DASHI.Physics.Common.GradedLocalCompatibilitySystemExact as Common

record ShellInteractionProfile (shell : Nat) : Set where
  constructor shellInteractionProfile
  field
    highHigh : ℚ
    lowHigh : ℚ
    highLow : ℚ
    comparable : ℚ

open ShellInteractionProfile public

addShellProfiles :
  ∀ {shell} →
  ShellInteractionProfile shell →
  ShellInteractionProfile shell →
  ShellInteractionProfile shell
addShellProfiles left right =
  shellInteractionProfile
    (highHigh left + highHigh right)
    (lowHigh left + lowHigh right)
    (highLow left + highLow right)
    (comparable left + comparable right)

data InteractionProbe : Set where
  highHighProbe : InteractionProbe
  lowHighProbe : InteractionProbe
  highLowProbe : InteractionProbe
  comparableProbe : InteractionProbe

observeInteraction :
  ∀ {shell} →
  InteractionProbe → ShellInteractionProfile shell → ℚ
observeInteraction highHighProbe profile = highHigh profile
observeInteraction lowHighProbe profile = lowHigh profile
observeInteraction highLowProbe profile = highLow profile
observeInteraction comparableProbe profile = comparable profile

interactionProbesSeparate :
  ∀ {shell} left right →
  ((probe : InteractionProbe) →
    observeInteraction probe left ≡ observeInteraction probe right) →
  left ≡ right
interactionProbesSeparate
  (shellInteractionProfile leftHH leftLH leftHL leftCC)
  (shellInteractionProfile rightHH rightLH rightHL rightCC)
  agreement
  rewrite agreement highHighProbe
        | agreement lowHighProbe
        | agreement highLowProbe
        | agreement comparableProbe = refl

shellGradedSystem : Nat → Common.GradedLocalCompatibilitySystem
shellGradedSystem shell =
  Common.gradedLocalCompatibilitySystem
    Nat
    (ShellInteractionProfile shell)
    InteractionProbe
    ℚ
    ℚ
    (λ profile → shell)
    addShellProfiles
    (λ left right → shell)
    (λ left right → refl)
    observeInteraction
    (λ defect → defect)

separatingShellGradedSystem :
  Nat → Common.SeparatingGradedLocalCompatibilitySystem
separatingShellGradedSystem shell =
  Common.separatingGradedLocalCompatibilitySystem
    (shellGradedSystem shell)
    interactionProbesSeparate

profileAdditionStaysAtShell :
  ∀ shell left right →
  Common.gradeOf (shellGradedSystem shell)
    (Common.localOperation (shellGradedSystem shell) left right)
  ≡ shell
profileAdditionStaysAtShell shell left right = refl

record ShellCompatibilityBoundary : Set where
  constructor shellCompatibilityBoundary
  field
    separatingClassProbesSupplyPhysicalBounds : Set
    separatingClassProbesDoNotSupplyPhysicalBounds :
      separatingClassProbesSupplyPhysicalBounds → Set

canonicalShellCompatibilityBoundary : ShellCompatibilityBoundary
canonicalShellCompatibilityBoundary =
  shellCompatibilityBoundary
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
