module DASHI.Automata.KernelInternal where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Kernel-internal automata.
--
-- The carrier, kernel and transition family are deliberately separated.
-- An automaton is internal exactly when every transition preserves the
-- kernel-null shell.  This covers finite puzzles, Z^n cellular automata,
-- subshifts of finite type and lifted phasic systems.
------------------------------------------------------------------------

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

record KernelSystem : Set₁ where
  field
    State : Set
    Generator : Set
    defectZero : State → Bool
    step : Generator → State → State

record KernelInternal (K : KernelSystem) : Set₁ where
  open KernelSystem K
  field
    preservesKernel :
      (g : Generator) →
      (x : State) →
      defectZero x ≡ true →
      defectZero (step g x) ≡ true

record KernelInternalAutomaton : Set₁ where
  field
    system : KernelSystem
    internality : KernelInternal system

record FiniteRadiusPresentation (K : KernelSystem) : Set₁ where
  field
    dimension : Nat
    radius : Nat
    translationInvariant : Bool
    finiteLocalAlphabet : Bool
    finiteConstraintFamily : Bool

  presentsSFT : Bool
  presentsSFT =
    translationInvariant
    ∧ finiteLocalAlphabet
    ∧ finiteConstraintFamily

record LiftClosure (K : KernelSystem) : Set₁ where
  field
    M3Available : Bool
    M6Available : Bool
    M9Available : Bool
    arbitraryFiniteRankAvailable : Bool
    phasicLiftAvailable : Bool
    scalarDefectContractionAvailable : Bool

  liftClosed : Bool
  liftClosed =
    M3Available
    ∧ M6Available
    ∧ M9Available
    ∧ arbitraryFiniteRankAvailable
    ∧ phasicLiftAvailable
    ∧ scalarDefectContractionAvailable

------------------------------------------------------------------------
-- Containment boundary.
--
-- A classical cellular automaton is recovered by taking a trivial kernel.
-- An SFT endomorphism is recovered by a finite-radius kernel presentation.
-- Strict structural extension is recorded only when lifted state is treated
-- as first-class rather than compiled away into an enlarged base alphabet.
------------------------------------------------------------------------

record ClassicalContainmentReceipt (K : KernelSystem) : Set₁ where
  field
    finiteRadius : FiniteRadiusPresentation K
    lifts : LiftClosure K
    cellularAutomataEmbedded : Bool
    subshiftsEmbedded : Bool
    finiteCSPEmbedded : Bool
    operadicRewritesEmbedded : Bool
    hybridPhasicDynamicsNotBaseCA : Bool
    higherObservablesRequireExpansion : Bool

  containmentClosed : Bool
  containmentClosed =
    cellularAutomataEmbedded
    ∧ subshiftsEmbedded
    ∧ finiteCSPEmbedded
    ∧ operadicRewritesEmbedded
    ∧ hybridPhasicDynamicsNotBaseCA
    ∧ higherObservablesRequireExpansion

kernelInternalStatement : String
kernelInternalStatement =
  "A kernel-internal automaton is an endomorphism of the admissible shell: "
  ++ "every generator preserves zero scalar defect. Classical CA and SFT "
  ++ "dynamics are recovered as finite-radius special cases; phasic and "
  ++ "lift-closed dynamics require extra state or loss of structure when "
  ++ "compiled to a base-alphabet CA."
