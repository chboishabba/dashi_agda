{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayE1VariableCutoffCylinderLimitExact where

------------------------------------------------------------------------
-- CLAY E1: a SAFE, measure-parametric theorem for CHANGING link carriers.
-- A cylinder is one continuum-labelled observable with a realization
-- on EVERY finite lattice; it is not a function on a fictitious fixed
-- Configuration. No global limit operator on arbitrary real sequences.
--
-- Proof results: selected finite-state semantics and actual convergence
-- imply positivity/normalization/additivity/homogeneity of the concrete
-- continuum expectation for the same source. Genuine convergence,
-- projective consistency, gauge covariance and OS reconstruction require
-- original source evidence; no Clay conclusion is assumed or proved.
-- No import of RealAnalysisAxioms or an unverified physical scalar socket.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)


record CylinderRealization
    (Configuration : Nat → Set)
    (Observable Scalar : Set) : Set₁ where
  field
    realization : (cutoff : Nat) → Observable → Configuration cutoff → Scalar
    zeroObservable oneObservable : Observable
    addObservable : Observable → Observable → Observable
    scalarObservable : Scalar → Observable → Observable

open CylinderRealization public

record SelectedScalarConvergence (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    Nonnegative : Scalar → Set
    Converges : (Nat → Scalar) → Scalar → Set

    convergenceUnique : ∀ sequence left right →
      Converges sequence left →
      Converges sequence right →
      left ≡ right

    constantConverges : ∀ value →
      Converges (λ _ → value) value

    addConverges : ∀ left right leftLimit rightLimit →
      Converges left leftLimit →
      Converges right rightLimit →
      Converges (λ n → add (left n) (right n))
        (add leftLimit rightLimit)

    multiplyConstantConverges : ∀ scalar sequence target →
      Converges sequence target →
      Converges (λ n → multiply scalar (sequence n))
        (multiply scalar target)

    nonnegativeClosed : ∀ sequence target →
      Converges sequence target →
      (∀ n → Nonnegative (sequence n)) →
      Nonnegative target

    convergenceCongruent : ∀ first second target →
      (∀ n → first n ≡ second n) →
      Converges second target →
      Converges first target

open SelectedScalarConvergence public

record ActualVariableCutoffCylinderFamily
    (Configuration Measure : Nat → Set)
    (Observable Scalar : Set)
    (realization : CylinderRealization Configuration Observable Scalar)
    (laws : SelectedScalarConvergence Scalar) : Set₁ where
  field
    -- These are the original n-dependent Wilson/Haar measure objects.
    finitePhysicalMeasure : (n : Nat) → Measure n

    originalNormalizedExpectation :
      (n : Nat) → Measure n → (Configuration n → Scalar) → Scalar

    -- This is the SAME literal normalization at every physical cutoff.
    finiteExpectation :
      (n : Nat) → Observable → Scalar

    finiteExpectationIsOriginalWilson :
      ∀ n observable →
      finiteExpectation n observable
      ≡ originalNormalizedExpectation n (finitePhysicalMeasure n)
          (CylinderRealization.realization realization n observable)

    -- Finite Wilson/Haar identities are derived from actual integration
    -- laws, not inferred from arbitrary assigned finite expectations.
    finiteZero : ∀ n →
      finiteExpectation n (zeroObservable realization) ≡ zero laws

    finiteOne : ∀ n →
      finiteExpectation n (oneObservable realization) ≡ one laws

    finiteAdd : ∀ n left right →
      finiteExpectation n (addObservable realization left right)
      ≡ add laws (finiteExpectation n left) (finiteExpectation n right)

    finiteScale : ∀ n scalar observable →
      finiteExpectation n (scalarObservable realization scalar observable)
      ≡ multiply laws scalar (finiteExpectation n observable)

    PositiveCylinder : Observable → Set
    finitePositive : ∀ n observable →
      PositiveCylinder observable →
      Nonnegative laws (finiteExpectation n observable)

    -- Crucial physical input: selected original Wilson expectations
    -- REALLY converge, even as their configuration carrier varies.
    continuumExpectation : Observable → Scalar
    originalWilsonConverges : ∀ observable →
      Converges laws
        (λ n → finiteExpectation n observable)
        (continuumExpectation observable)

open ActualVariableCutoffCylinderFamily public

-- Actual continuum measure is the selected functional with certified
-- original changing-cutoff expectation convergence.
literalVariableCutoffContinuumExpectation :
  ∀ {Configuration Measure Observable Scalar realization laws} →
  ActualVariableCutoffCylinderFamily
    Configuration Measure Observable Scalar realization laws →
  Observable → Scalar
literalVariableCutoffContinuumExpectation source = continuumExpectation source

variableCutoffContinuumZero :
  ∀ {Configuration Measure Observable Scalar realization laws}
    (source : ActualVariableCutoffCylinderFamily
      Configuration Measure Observable Scalar realization laws) →
  continuumExpectation source (zeroObservable realization) ≡ zero laws
variableCutoffContinuumZero
    {realization = realization} {laws = laws} source =
  convergenceUnique laws
    (λ n → finiteExpectation source n (zeroObservable realization))
    (continuumExpectation source (zeroObservable realization))
    (zero laws)
    (originalWilsonConverges source (zeroObservable realization))
    (convergenceCongruent laws
      (λ n → finiteExpectation source n (zeroObservable realization))
      (λ n → zero laws)
      (zero laws)
      (finiteZero source)
      (constantConverges laws (zero laws)))

variableCutoffContinuumNormalized :
  ∀ {Configuration Measure Observable Scalar realization laws}
    (source : ActualVariableCutoffCylinderFamily
      Configuration Measure Observable Scalar realization laws) →
  continuumExpectation source (oneObservable realization) ≡ one laws
variableCutoffContinuumNormalized
    {realization = realization} {laws = laws} source =
  convergenceUnique laws
    (λ n → finiteExpectation source n (oneObservable realization))
    (continuumExpectation source (oneObservable realization))
    (one laws)
    (originalWilsonConverges source (oneObservable realization))
    (convergenceCongruent laws
      (λ n → finiteExpectation source n (oneObservable realization))
      (λ n → one laws)
      (one laws)
      (finiteOne source)
      (constantConverges laws (one laws)))

variableCutoffContinuumAdd :
  ∀ {Configuration Measure Observable Scalar realization laws}
    (source : ActualVariableCutoffCylinderFamily
      Configuration Measure Observable Scalar realization laws)
    left right →
  continuumExpectation source (addObservable realization left right)
    ≡ add laws
      (continuumExpectation source left)
      (continuumExpectation source right)
variableCutoffContinuumAdd
    {realization = realization} {laws = laws} source left right =
  convergenceUnique laws
    (λ n → finiteExpectation source n
      (addObservable realization left right))
    (continuumExpectation source (addObservable realization left right))
    (add laws (continuumExpectation source left)
      (continuumExpectation source right))
    (originalWilsonConverges source
      (addObservable realization left right))
    (convergenceCongruent laws
      (λ n → finiteExpectation source n
        (addObservable realization left right))
      (λ n → add laws
        (finiteExpectation source n left)
        (finiteExpectation source n right))
      (add laws (continuumExpectation source left)
        (continuumExpectation source right))
      (λ n → finiteAdd source n left right)
      (addConverges laws
        (λ n → finiteExpectation source n left)
        (λ n → finiteExpectation source n right)
        (continuumExpectation source left)
        (continuumExpectation source right)
        (originalWilsonConverges source left)
        (originalWilsonConverges source right)))

variableCutoffContinuumScale :
  ∀ {Configuration Measure Observable Scalar realization laws}
    (source : ActualVariableCutoffCylinderFamily
      Configuration Measure Observable Scalar realization laws)
    scalar observable →
  continuumExpectation source (scalarObservable realization scalar observable)
    ≡ multiply laws scalar (continuumExpectation source observable)
variableCutoffContinuumScale
    {realization = realization} {laws = laws} source scalar observable =
  convergenceUnique laws
    (λ n → finiteExpectation source n
      (scalarObservable realization scalar observable))
    (continuumExpectation source
      (scalarObservable realization scalar observable))
    (multiply laws scalar (continuumExpectation source observable))
    (originalWilsonConverges source
      (scalarObservable realization scalar observable))
    (convergenceCongruent laws
      (λ n → finiteExpectation source n
        (scalarObservable realization scalar observable))
      (λ n → multiply laws scalar
        (finiteExpectation source n observable))
      (multiply laws scalar (continuumExpectation source observable))
      (λ n → finiteScale source n scalar observable)
      (multiplyConstantConverges laws scalar
        (λ n → finiteExpectation source n observable)
        (continuumExpectation source observable)
        (originalWilsonConverges source observable)))

variableCutoffContinuumPositive :
  ∀ {Configuration Measure Observable Scalar realization laws}
    (source : ActualVariableCutoffCylinderFamily
      Configuration Measure Observable Scalar realization laws)
    observable →
  PositiveCylinder source observable →
  Nonnegative laws (continuumExpectation source observable)
variableCutoffContinuumPositive {laws = laws} source observable positive =
  nonnegativeClosed laws
    (λ n → finiteExpectation source n observable)
    (continuumExpectation source observable)
    (originalWilsonConverges source observable)
    (λ n → finitePositive source n observable positive)
