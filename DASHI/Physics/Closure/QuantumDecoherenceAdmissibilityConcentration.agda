module DASHI.Physics.Closure.QuantumDecoherenceAdmissibilityConcentration where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; Σ)

open import DASHI.Foundations.BidirectionalAdmissibilityGalois
open import DASHI.Foundations.UltrametricAdmissibilityConcentration

------------------------------------------------------------------------
-- Quantum interpretation boundary.
--
-- This module makes the thread's structural dictionary precise:
--
--   superposition  = more than one admitted micro-realizer of one macro label
--   entanglement   = failure of a joint admissibility predicate to factor
--   decoherence    = concentration of a joint carrier together with a stable
--                    forward/pullback macro branch
--
-- It does not derive the Born rule, Hilbert-space linearity, unitary quantum
-- dynamics, or a measurement-collapse theorem.  Concrete quantum models must
-- provide the realization relation, weights/amplitudes, and contraction data.

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Superposition as unresolved multiplicity in a projection fibre.

record SuperpositionFibre
    {Micro Macro : Set}
    (R : Rel Micro Macro)
    (Admitted : Pred Micro)
    (macro : Macro) : Set₁ where
  field
    left right : Micro
    left-admitted : Admitted left
    right-admitted : Admitted right
    left-realizes : R left macro
    right-realizes : R right macro
    distinct : left ≢ right

open SuperpositionFibre public

superposition-forward-supported :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {Admitted : Pred Micro}
    {macro : Macro} →
  SuperpositionFibre R Admitted macro →
  Forward R Admitted macro
superposition-forward-supported S =
  left S , (left-admitted S , left-realizes S)

------------------------------------------------------------------------
-- Entanglement as non-factorization of joint admissibility.

JointPred : Set → Set → Set₁
JointPred A B = Pred (A × B)

record Factorization
    {A B : Set}
    (Joint : JointPred A B) : Set₂ where
  field
    Left : Pred A
    Right : Pred B
    factor-forward :
      ∀ {a b} →
      Joint (a , b) →
      Left a × Right b
    factor-backward :
      ∀ {a b} →
      Left a →
      Right b →
      Joint (a , b)

Entangled :
  ∀ {A B : Set} →
  JointPred A B →
  Set₂
Entangled Joint = Factorization Joint → ⊥

factorized-is-not-entangled :
  ∀ {A B : Set}
    {Joint : JointPred A B} →
  Factorization Joint →
  Entangled Joint →
  ⊥
factorized-is-not-entangled factor entangled = entangled factor

------------------------------------------------------------------------
-- A macro branch is bidirectionally stable when every admitted macro label
-- has a safe micro witness.  Galois reductivity supplies the reverse inclusion.

MacroWitness :
  ∀ {Micro Macro : Set} →
  Rel Micro Macro →
  Pred Macro →
  Set₁
MacroWitness {Micro} R Y =
  ∀ {y} →
  Y y →
  Σ Micro (λ x → SafePullback R Y x × R x y)

macroWitness-to-kernel :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {Y : Pred Macro} →
  MacroWitness R Y →
  Y ⊆ MacroKernel R Y
macroWitness-to-kernel witness y∈Y = witness y∈Y

record GaloisStableBranch
    {Micro Macro : Set}
    (R : Rel Micro Macro)
    (Y : Pred Macro) : Set₁ where
  field
    witnessed : MacroWitness R Y

open GaloisStableBranch public

stableBranch-forward :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {Y : Pred Macro} →
  GaloisStableBranch R Y →
  Y ⊆ MacroKernel R Y
stableBranch-forward branch =
  macroWitness-to-kernel (witnessed branch)

stableBranch-backward :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {Y : Pred Macro} →
  GaloisStableBranch R Y →
  MacroKernel R Y ⊆ Y
stableBranch-backward _ = macroKernel-reductive

------------------------------------------------------------------------
-- Decoherence bridge: concentration on a micro carrier plus a stable macro
-- branch under the realization relation.

record DecoherenceAsAdmissibilityConcentration : Set₃ where
  field
    Micro : Set
    Macro : Set

    realization : Rel Micro Macro
    MicroMetric : Set

    -- The quantitative ultrametric carrier is kept abstract at this bridge.
    -- Concrete instances should instantiate
    -- AdmissibilityConcentrationKernel in the foundations module.
    ConcentrationReceipt : Set

    survivingBranch : Pred Macro
    branchStable : GaloisStableBranch realization survivingBranch

    decoherenceReading :
      GaloisStableBranch realization survivingBranch

open DecoherenceAsAdmissibilityConcentration public

branch-is-bidirectionally-closed :
  (D : DecoherenceAsAdmissibilityConcentration) →
  (survivingBranch D ⊆ MacroKernel (realization D) (survivingBranch D))
  ×
  (MacroKernel (realization D) (survivingBranch D) ⊆ survivingBranch D)
branch-is-bidirectionally-closed D =
  stableBranch-forward (branchStable D)
  ,
  stableBranch-backward (branchStable D)
