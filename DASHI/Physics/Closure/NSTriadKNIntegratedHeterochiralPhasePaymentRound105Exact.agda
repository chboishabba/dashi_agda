module DASHI.Physics.Closure.NSTriadKNIntegratedHeterochiralPhasePaymentRound105Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: J. M. Manley; H. E. Rowe.
-- Title: "Some General Properties of Nonlinear Elements-Part I. General
-- Energy Relations".
-- Proceedings of the IRE 44(7) (1956), 904--913.
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- ROUND105 / INTEGRATED PHASE PAYMENT
--
-- The preceding Round105 pointwise theorem gives on each adverse mixed-helicity
-- cell
--
--   nu P(t) <= 2 gamma(t) A_+(t).
--
-- The scalar damped-forced Waleffe amplitude equation gives, after the standard
-- positive-part/Kato integration on the SAME interval,
--
--   A_+(T) + integral gamma A_+ <= A_+(0) + integral F_+.
--
-- This file proves the exact finite algebraic composition and summation:
--
--   nu integral P
--     <= 2 A_+(0) + 2 integral F_+.
--
-- Therefore the literal heterochiral critical-production problem is reduced to
-- one quantity: a cutoff-uniform weighted sum of POSITIVE NETWORK FORCING in
-- the Waleffe amplitude equations.  Terminal amplitude is favourable and is
-- discarded only by its proved nonnegativity.
--
-- This is not a danger/excess receipt: the two input inequalities are the exact
-- integrated forms of (i) the Round105 geometric pointwise theorem and (ii)
-- the literal Round94 scalar amplitude ODE.  The theorem below eliminates the
-- intermediate damping-area variable completely.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

two : ℚ
two = Int.+ 2 / 1

record IntegratedAdversePhaseCell (viscosity : ℚ) : Set where
  constructor integrated-adverse-phase-cell
  field
    integratedProduction dampingArea : ℚ
    initialPositiveAmplitude terminalPositiveAmplitude : ℚ
    positiveNetworkForcing : ℚ

    terminalAmplitudeNonnegative : 0ℚ ≤ terminalPositiveAmplitude

    -- Integrated Round105 pointwise comparison.
    productionPaidByDampingArea :
      viscosity * integratedProduction ≤ two * dampingArea

    -- Positive-part integral of dA + gamma A = F_network.
    positiveAmplitudeBalance :
      terminalPositiveAmplitude + dampingArea
      ≤ initialPositiveAmplitude + positiveNetworkForcing

open IntegratedAdversePhaseCell public

cellProductionPaidByInitialAmplitudeAndNetworkForcing :
  ∀ {viscosity} (cell : IntegratedAdversePhaseCell viscosity) →
  viscosity * integratedProduction cell
  ≤ two * initialPositiveAmplitude cell
      + two * positiveNetworkForcing cell
cellProductionPaidByInitialAmplitudeAndNetworkForcing {viscosity} cell =
  let
    dampingBelowEndpoint :
      dampingArea cell
      ≤ initialPositiveAmplitude cell + positiveNetworkForcing cell
    dampingBelowEndpoint =
      let
        addTerminal :
          0ℚ + dampingArea cell
          ≤ terminalPositiveAmplitude cell + dampingArea cell
        addTerminal =
          ℚP.+-mono-≤ (terminalAmplitudeNonnegative cell) ℚP.≤-refl

        dropZero :
          dampingArea cell
          ≤ terminalPositiveAmplitude cell + dampingArea cell
        dropZero =
          subst
            (λ left → left ≤ terminalPositiveAmplitude cell + dampingArea cell)
            (solve (dampingArea cell ∷ []))
            addTerminal
      in
      ℚP.≤-trans dropZero (positiveAmplitudeBalance cell)

    doubled :
      two * dampingArea cell
      ≤ two * (initialPositiveAmplitude cell + positiveNetworkForcing cell)
    doubled =
      let
        twoNN : 0ℚ ≤ two
        twoNN = ℚP.<⇒≤ (ℚP.positive⁻¹ two)
        open import Data.Rational.Base using (NonNegative; nonNegative)
        instance twoNNI : NonNegative two
                 twoNNI = nonNegative twoNN
      in ℚP.*-monoˡ-≤-nonNeg two dampingBelowEndpoint

    endpoint :
      two * (initialPositiveAmplitude cell + positiveNetworkForcing cell)
      ≡ two * initialPositiveAmplitude cell + two * positiveNetworkForcing cell
    endpoint = solve
      (initialPositiveAmplitude cell ∷ positiveNetworkForcing cell ∷ [])
  in
  ℚP.≤-trans
    (productionPaidByDampingArea cell)
    (subst
      (λ upper → two * dampingArea cell ≤ upper)
      endpoint doubled)

sumIntegratedProduction :
  ∀ {viscosity} → List (IntegratedAdversePhaseCell viscosity) → ℚ
sumIntegratedProduction [] = 0ℚ
sumIntegratedProduction (cell ∷ rest) =
  integratedProduction cell + sumIntegratedProduction rest

sumInitialPositiveAmplitude :
  ∀ {viscosity} → List (IntegratedAdversePhaseCell viscosity) → ℚ
sumInitialPositiveAmplitude [] = 0ℚ
sumInitialPositiveAmplitude (cell ∷ rest) =
  initialPositiveAmplitude cell + sumInitialPositiveAmplitude rest

sumPositiveNetworkForcing :
  ∀ {viscosity} → List (IntegratedAdversePhaseCell viscosity) → ℚ
sumPositiveNetworkForcing [] = 0ℚ
sumPositiveNetworkForcing (cell ∷ rest) =
  positiveNetworkForcing cell + sumPositiveNetworkForcing rest

finiteAdverseProductionPaidByInitialPhaseAndNetworkForcing :
  ∀ {viscosity}
    (cells : List (IntegratedAdversePhaseCell viscosity)) →
  viscosity * sumIntegratedProduction cells
  ≤ two * sumInitialPositiveAmplitude cells
      + two * sumPositiveNetworkForcing cells
finiteAdverseProductionPaidByInitialPhaseAndNetworkForcing [] = ℚP.≤-refl
finiteAdverseProductionPaidByInitialPhaseAndNetworkForcing
    {viscosity} (cell ∷ rest) =
  let
    head = cellProductionPaidByInitialAmplitudeAndNetworkForcing cell
    tail = finiteAdverseProductionPaidByInitialPhaseAndNetworkForcing rest
    added = ℚP.+-mono-≤ head tail

    leftMeaning :
      viscosity * integratedProduction cell
        + viscosity * sumIntegratedProduction rest
      ≡ viscosity * sumIntegratedProduction (cell ∷ rest)
    leftMeaning = solve
      (viscosity ∷ integratedProduction cell
       ∷ sumIntegratedProduction rest ∷ [])

    rightMeaning :
      (two * initialPositiveAmplitude cell + two * positiveNetworkForcing cell)
        + (two * sumInitialPositiveAmplitude rest
          + two * sumPositiveNetworkForcing rest)
      ≡ two * sumInitialPositiveAmplitude (cell ∷ rest)
        + two * sumPositiveNetworkForcing (cell ∷ rest)
    rightMeaning = solve
      ( initialPositiveAmplitude cell ∷ positiveNetworkForcing cell
      ∷ sumInitialPositiveAmplitude rest ∷ sumPositiveNetworkForcing rest ∷ [])
  in
  subst
    (λ left → left ≤
      two * sumInitialPositiveAmplitude (cell ∷ rest)
        + two * sumPositiveNetworkForcing (cell ∷ rest))
    leftMeaning
    (subst
      (λ right →
        viscosity * integratedProduction cell
          + viscosity * sumIntegratedProduction rest ≤ right)
      rightMeaning added)

round105IntegratedAdversePhasePaymentClosed : Bool
round105IntegratedAdversePhasePaymentClosed = true

round105HeterochiralFrontierReducedToPositiveNetworkForcing : Bool
round105HeterochiralFrontierReducedToPositiveNetworkForcing = true

-- Still physical/analytic: construct the positive-part amplitude balance from
-- the literal Round94 trajectory, then prove the weighted complete-network
-- forcing sum is cutoff-uniform for arbitrary smooth data.
round105PhysicalPositiveNetworkForcingBudgetClosed : Bool
round105PhysicalPositiveNetworkForcingBudgetClosed = false

round105IntegratedAdversePhasePaymentClosedIsTrue :
  round105IntegratedAdversePhasePaymentClosed ≡ true
round105IntegratedAdversePhasePaymentClosedIsTrue = refl

round105HeterochiralFrontierReducedToPositiveNetworkForcingIsTrue :
  round105HeterochiralFrontierReducedToPositiveNetworkForcing ≡ true
round105HeterochiralFrontierReducedToPositiveNetworkForcingIsTrue = refl

round105PhysicalPositiveNetworkForcingBudgetClosedIsFalse :
  round105PhysicalPositiveNetworkForcingBudgetClosed ≡ false
round105PhysicalPositiveNetworkForcingBudgetClosedIsFalse = refl
