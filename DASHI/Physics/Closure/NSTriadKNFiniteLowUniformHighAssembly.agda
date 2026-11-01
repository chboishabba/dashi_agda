module DASHI.Physics.Closure.NSTriadKNFiniteLowUniformHighAssembly where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Alexey Cheskidov; Roman Shvydkoy; Alexey Cheskidov; Mimi Dai;
-- DASHI repository contributors.
-- Titles:
--   * "A unified approach to regularity problems for the 3D Navier-Stokes
--      and Euler equations: the use of Kolmogorov's dissipation range";
--   * "Regularity criteria for the 3D Navier-Stokes and MHD equations";
--   * "Finite-low / uniform-high shell assembly".
-- DOI:
--   * 10.1007/s00021-014-0167-4;
--   * 10.1017/S0013091525100813;
--   * the abstract assembly lemmas below are repository-original.
--
-- PURPOSE
-- Isolate the constructive case split common to localized regularity
-- criteria.  The theorem says only that low-shell control and high-shell
-- control assemble once a shell dichotomy is supplied.  It does not assert
-- that any Navier--Stokes solution provides either hypothesis.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_; _<_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Fixed-cutoff assembly.
------------------------------------------------------------------------

record FiniteLowUniformHighControl
    {ℓ : Level}
    (ShellProperty : Nat → Set ℓ) : Set (lsuc ℓ) where
  field
    cutoff : Nat

    shellDichotomy :
      (shell : Nat) →
      shell ≤ cutoff ⊎ cutoff < shell

    finiteLowControl :
      (shell : Nat) →
      shell ≤ cutoff →
      ShellProperty shell

    uniformHighControl :
      (shell : Nat) →
      cutoff < shell →
      ShellProperty shell

open FiniteLowUniformHighControl public

allShellControl :
  ∀ {ℓ} {ShellProperty : Nat → Set ℓ} →
  FiniteLowUniformHighControl ShellProperty →
  (shell : Nat) →
  ShellProperty shell
allShellControl control shell
  with FiniteLowUniformHighControl.shellDichotomy control shell
... | inj₁ low =
  FiniteLowUniformHighControl.finiteLowControl control shell low
... | inj₂ high =
  FiniteLowUniformHighControl.uniformHighControl control shell high

------------------------------------------------------------------------
-- Solution-dependent dissipation-wavenumber assembly.
------------------------------------------------------------------------

record TimeDependentDissipationSplitControl
    {t ℓ : Level}
    (Time : Set t)
    (ShellProperty : Time → Nat → Set ℓ) : Set (lsuc (t ⊔ ℓ)) where
  field
    dissipationWavenumber : Time → Nat

    shellDichotomyAtTime :
      (time : Time) →
      (shell : Nat) →
      shell ≤ dissipationWavenumber time
        ⊎
      dissipationWavenumber time < shell

    lowModeControl :
      (time : Time) →
      (shell : Nat) →
      shell ≤ dissipationWavenumber time →
      ShellProperty time shell

    highModeDissipativeControl :
      (time : Time) →
      (shell : Nat) →
      dissipationWavenumber time < shell →
      ShellProperty time shell

open TimeDependentDissipationSplitControl public

allShellControlAtTime :
  ∀ {t ℓ}
    {Time : Set t}
    {ShellProperty : Time → Nat → Set ℓ} →
  TimeDependentDissipationSplitControl Time ShellProperty →
  (time : Time) →
  (shell : Nat) →
  ShellProperty time shell
allShellControlAtTime control time shell
  with TimeDependentDissipationSplitControl.shellDichotomyAtTime
    control time shell
... | inj₁ low =
  TimeDependentDissipationSplitControl.lowModeControl
    control time shell low
... | inj₂ high =
  TimeDependentDissipationSplitControl.highModeDissipativeControl
    control time shell high

------------------------------------------------------------------------
-- Quantitative natural-number specialization.
------------------------------------------------------------------------

record FiniteLowUniformHighNatBound
    (quantity : Nat → Nat)
    (bound : Nat) : Set where
  field
    cutoff : Nat

    shellDichotomy :
      (shell : Nat) →
      shell ≤ cutoff ⊎ cutoff < shell

    finiteLowBound :
      (shell : Nat) →
      shell ≤ cutoff →
      quantity shell ≤ bound

    uniformHighBound :
      (shell : Nat) →
      cutoff < shell →
      quantity shell ≤ bound

open FiniteLowUniformHighNatBound public

allShellNatBound :
  ∀ {quantity : Nat → Nat} {bound : Nat} →
  FiniteLowUniformHighNatBound quantity bound →
  (shell : Nat) →
  quantity shell ≤ bound
allShellNatBound control shell
  with FiniteLowUniformHighNatBound.shellDichotomy control shell
... | inj₁ low =
  FiniteLowUniformHighNatBound.finiteLowBound control shell low
... | inj₂ high =
  FiniteLowUniformHighNatBound.uniformHighBound control shell high

finiteLowUniformHighAssemblyClosed : Bool
finiteLowUniformHighAssemblyClosed = true

finiteLowUniformHighAssemblyClosedIsTrue :
  finiteLowUniformHighAssemblyClosed ≡ true
finiteLowUniformHighAssemblyClosedIsTrue = refl
