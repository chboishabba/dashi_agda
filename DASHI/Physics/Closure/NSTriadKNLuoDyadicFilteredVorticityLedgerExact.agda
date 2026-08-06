module DASHI.Physics.Closure.NSTriadKNLuoDyadicFilteredVorticityLedgerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphaël Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- This module implements the exact finite K2--K3 ledger after the physical
-- filtered vorticity equation has been derived.  Every dyadic shell carries
-- five literal source classes:
--
--   high-high, low-high, high-low, comparable, commutator.
--
-- No generic remainder is available.  A shell identity
--
--   Eout + D = Ein + HH + LH + HL + CC + Com
--
-- is multiplied by its literal nonnegative critical weight and summed over a
-- finite shell list.  The resulting equality is the finite algebraic core of
-- the critical filtered-enstrophy balance.  It does not construct the Leray
-- projector, paraproduct index ranges, or the PDE differentiation itself.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; cong₂; trans)

data FilteredInteractionClass : Set where
  highHigh lowHigh highLow comparable commutator : FilteredInteractionClass

record DyadicFilteredShell : Set where
  constructor dyadicFilteredShell
  field
    criticalWeight : ℚ
    criticalWeightNonnegative : 0ℚ ≤ criticalWeight

    enstrophyIn enstrophyOut diffusion : ℚ
    highHighSource lowHighSource highLowSource : ℚ
    comparableSource commutatorSource : ℚ

    filteredShellBalance :
      enstrophyOut + diffusion
      ≡
      enstrophyIn
      + highHighSource
      + lowHighSource
      + highLowSource
      + comparableSource
      + commutatorSource

open DyadicFilteredShell public

sourceOf : FilteredInteractionClass → DyadicFilteredShell → ℚ
sourceOf highHigh = highHighSource
sourceOf lowHigh = lowHighSource
sourceOf highLow = highLowSource
sourceOf comparable = comparableSource
sourceOf commutator = commutatorSource

totalFilteredSource : DyadicFilteredShell → ℚ
totalFilteredSource shell =
  highHighSource shell
  + lowHighSource shell
  + highLowSource shell
  + comparableSource shell
  + commutatorSource shell

filteredShellBalanceNormalized :
  ∀ shell →
  enstrophyOut shell + diffusion shell
  ≡ enstrophyIn shell + totalFilteredSource shell
filteredShellBalanceNormalized shell =
  trans
    (filteredShellBalance shell)
    (solve
      ( enstrophyIn shell
      ∷ highHighSource shell
      ∷ lowHighSource shell
      ∷ highLowSource shell
      ∷ comparableSource shell
      ∷ commutatorSource shell
      ∷ []))

weightedShellBalance :
  ∀ shell →
  criticalWeight shell
    * (enstrophyOut shell + diffusion shell)
  ≡
  criticalWeight shell
    * (enstrophyIn shell + totalFilteredSource shell)
weightedShellBalance shell =
  cong
    (λ value → criticalWeight shell * value)
    (filteredShellBalanceNormalized shell)

weightedShellBalanceExpanded :
  ∀ shell →
  criticalWeight shell * enstrophyOut shell
    + criticalWeight shell * diffusion shell
  ≡
  criticalWeight shell * enstrophyIn shell
    + criticalWeight shell * highHighSource shell
    + criticalWeight shell * lowHighSource shell
    + criticalWeight shell * highLowSource shell
    + criticalWeight shell * comparableSource shell
    + criticalWeight shell * commutatorSource shell
weightedShellBalanceExpanded shell =
  trans
    (solve
      ( criticalWeight shell
      ∷ enstrophyOut shell ∷ diffusion shell ∷ []))
    (trans
      (weightedShellBalance shell)
      (solve
        ( criticalWeight shell
        ∷ enstrophyIn shell
        ∷ highHighSource shell
        ∷ lowHighSource shell
        ∷ highLowSource shell
        ∷ comparableSource shell
        ∷ commutatorSource shell
        ∷ [])))

weightedSum :
  (DyadicFilteredShell → ℚ) → List DyadicFilteredShell → ℚ
weightedSum select [] = 0ℚ
weightedSum select (shell ∷ shells) =
  criticalWeight shell * select shell + weightedSum select shells

weightedEnstrophyIn : List DyadicFilteredShell → ℚ
weightedEnstrophyIn = weightedSum enstrophyIn

weightedEnstrophyOut : List DyadicFilteredShell → ℚ
weightedEnstrophyOut = weightedSum enstrophyOut

weightedDiffusion : List DyadicFilteredShell → ℚ
weightedDiffusion = weightedSum diffusion

weightedHighHigh : List DyadicFilteredShell → ℚ
weightedHighHigh = weightedSum highHighSource

weightedLowHigh : List DyadicFilteredShell → ℚ
weightedLowHigh = weightedSum lowHighSource

weightedHighLow : List DyadicFilteredShell → ℚ
weightedHighLow = weightedSum highLowSource

weightedComparable : List DyadicFilteredShell → ℚ
weightedComparable = weightedSum comparableSource

weightedCommutator : List DyadicFilteredShell → ℚ
weightedCommutator = weightedSum commutatorSource

weightedTotalSource : List DyadicFilteredShell → ℚ
weightedTotalSource = weightedSum totalFilteredSource

weightedSourceDecomposition :
  ∀ shells →
  weightedTotalSource shells
  ≡
  weightedHighHigh shells
  + weightedLowHigh shells
  + weightedHighLow shells
  + weightedComparable shells
  + weightedCommutator shells
weightedSourceDecomposition [] = solve []
weightedSourceDecomposition (shell ∷ shells)
  rewrite weightedSourceDecomposition shells =
  solve
    ( criticalWeight shell
    ∷ highHighSource shell
    ∷ lowHighSource shell
    ∷ highLowSource shell
    ∷ comparableSource shell
    ∷ commutatorSource shell
    ∷ weightedHighHigh shells
    ∷ weightedLowHigh shells
    ∷ weightedHighLow shells
    ∷ weightedComparable shells
    ∷ weightedCommutator shells
    ∷ [])

finiteCriticalFilteredEnstrophyLedger :
  ∀ shells →
  weightedEnstrophyOut shells + weightedDiffusion shells
  ≡
  weightedEnstrophyIn shells
  + weightedHighHigh shells
  + weightedLowHigh shells
  + weightedHighLow shells
  + weightedComparable shells
  + weightedCommutator shells
finiteCriticalFilteredEnstrophyLedger [] = solve []
finiteCriticalFilteredEnstrophyLedger (shell ∷ shells) =
  let
    tailBalance = finiteCriticalFilteredEnstrophyLedger shells

    leftRegroup :
      (criticalWeight shell * enstrophyOut shell
        + weightedEnstrophyOut shells)
      + (criticalWeight shell * diffusion shell
        + weightedDiffusion shells)
      ≡
      (criticalWeight shell * enstrophyOut shell
        + criticalWeight shell * diffusion shell)
      + (weightedEnstrophyOut shells + weightedDiffusion shells)
    leftRegroup =
      solve
        ( criticalWeight shell
        ∷ enstrophyOut shell ∷ diffusion shell
        ∷ weightedEnstrophyOut shells
        ∷ weightedDiffusion shells ∷ [])

    middle :
      (criticalWeight shell * enstrophyOut shell
        + criticalWeight shell * diffusion shell)
      + (weightedEnstrophyOut shells + weightedDiffusion shells)
      ≡
      (criticalWeight shell * enstrophyIn shell
        + criticalWeight shell * highHighSource shell
        + criticalWeight shell * lowHighSource shell
        + criticalWeight shell * highLowSource shell
        + criticalWeight shell * comparableSource shell
        + criticalWeight shell * commutatorSource shell)
      +
      (weightedEnstrophyIn shells
        + weightedHighHigh shells
        + weightedLowHigh shells
        + weightedHighLow shells
        + weightedComparable shells
        + weightedCommutator shells)
    middle =
      cong₂ _+_
        (weightedShellBalanceExpanded shell)
        tailBalance

    rightRegroup :
      (criticalWeight shell * enstrophyIn shell
        + criticalWeight shell * highHighSource shell
        + criticalWeight shell * lowHighSource shell
        + criticalWeight shell * highLowSource shell
        + criticalWeight shell * comparableSource shell
        + criticalWeight shell * commutatorSource shell)
      +
      (weightedEnstrophyIn shells
        + weightedHighHigh shells
        + weightedLowHigh shells
        + weightedHighLow shells
        + weightedComparable shells
        + weightedCommutator shells)
      ≡
      (criticalWeight shell * enstrophyIn shell
        + weightedEnstrophyIn shells)
      + (criticalWeight shell * highHighSource shell
        + weightedHighHigh shells)
      + (criticalWeight shell * lowHighSource shell
        + weightedLowHigh shells)
      + (criticalWeight shell * highLowSource shell
        + weightedHighLow shells)
      + (criticalWeight shell * comparableSource shell
        + weightedComparable shells)
      + (criticalWeight shell * commutatorSource shell
        + weightedCommutator shells)
    rightRegroup =
      solve
        ( criticalWeight shell
        ∷ enstrophyIn shell
        ∷ highHighSource shell
        ∷ lowHighSource shell
        ∷ highLowSource shell
        ∷ comparableSource shell
        ∷ commutatorSource shell
        ∷ weightedEnstrophyIn shells
        ∷ weightedHighHigh shells
        ∷ weightedLowHigh shells
        ∷ weightedHighLow shells
        ∷ weightedComparable shells
        ∷ weightedCommutator shells
        ∷ [])
  in
  trans leftRegroup (trans middle rightRegroup)

record ShellCriticalWeightMeaning (shell : DyadicFilteredShell) : Set where
  constructor shellCriticalWeightMeaning
  field
    vorticityWeight velocityCriticalWeight : ℚ
    vorticityToVelocityCritical :
      criticalWeight shell * vorticityWeight
      ≡ velocityCriticalWeight

open ShellCriticalWeightMeaning public

record DyadicFilteredLedgerAuthorityBoundary : Set where
  constructor dyadicFilteredLedgerAuthorityBoundary
  field
    fiveClassExhaustiveCarrierImplemented : Set
    finiteCriticalWeightedIdentityProved : Set
    physicalFilteredVorticityEquationDerived : Set
    literalParaproductIndexRangesDerived : Set
    infiniteShellLimitProved : Set

canonicalDyadicFilteredLedgerAuthorityBoundary :
  DyadicFilteredLedgerAuthorityBoundary
canonicalDyadicFilteredLedgerAuthorityBoundary =
  dyadicFilteredLedgerAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
