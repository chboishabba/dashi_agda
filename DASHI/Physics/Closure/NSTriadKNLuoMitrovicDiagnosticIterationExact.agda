module DASHI.Physics.Closure.NSTriadKNLuoMitrovicDiagnosticIterationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- PURPOSE
-- Isolate and prove the scalar fixed-point induction used by a terminal-tail
-- diagnostic.  The hypotheses remain visible:
--
--   farHistory <= seed/2,
--   0 <= theta <= 1/4,
--   w(0)=seed,
--   w(n+1)=farHistory+theta*w(n).
--
-- Exact rational induction gives w(n)<=2*seed for every finite n.  This
-- theorem does not derive the terminal tail relation or the seed lower bound
-- from the energy inequality and therefore cannot be mistaken for an
-- unconditional Navier--Stokes regularity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂)
open import Relation.Nullary.Decidable.Core using (toWitness)

half quarter two : ℚ
half = Int.+ 1 / 2
quarter = Int.+ 1 / 4
two = Int.+ 2 / 1

quarterNonnegative : 0ℚ ≤ quarter
quarterNonnegative = toWitness {a? = 0ℚ ≤? quarter} _

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ≤? two} _

record DiagnosticIterationData : Set where
  constructor diagnostic-iteration-data
  field
    seed farHistory theta : ℚ

    seedNonnegative : 0ℚ ≤ seed
    thetaNonnegative : 0ℚ ≤ theta

    farHistoryBelowHalfSeed : farHistory ≤ half * seed
    thetaBelowQuarter : theta ≤ quarter

open DiagnosticIterationData public

diagnosticIterate : DiagnosticIterationData → Nat → ℚ
diagnosticIterate inputs zero = seed inputs
diagnosticIterate inputs (suc iteration) =
  farHistory inputs + theta inputs * diagnosticIterate inputs iteration

seedBelowTwoSeed :
  (inputs : DiagnosticIterationData) →
  seed inputs ≤ two * seed inputs
seedBelowTwoSeed inputs =
  let
    shifted : seed inputs + 0ℚ ≤ seed inputs + seed inputs
    shifted =
      ℚₚ.+-monoʳ-≤
        (seed inputs)
        (seedNonnegative inputs)

    leftMeaning : seed inputs + 0ℚ ≡ seed inputs
    leftMeaning = solve (seed inputs ∷ [])

    rightMeaning : seed inputs + seed inputs ≡ two * seed inputs
    rightMeaning = solve (seed inputs ∷ [])
  in
  subst₂ _≤_ leftMeaning rightMeaning shifted

twoSeedNonnegative :
  (inputs : DiagnosticIterationData) →
  0ℚ ≤ two * seed inputs
twoSeedNonnegative inputs =
  let
    instance
      twoIsNonnegative = nonNegative twoNonnegative
      seedIsNonnegative = nonNegative (seedNonnegative inputs)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg two (seed inputs)
  in
  ℚₚ.nonNegative⁻¹ (two * seed inputs)

diagnosticIterationUniformBound :
  (inputs : DiagnosticIterationData) →
  (iteration : Nat) →
  diagnosticIterate inputs iteration ≤ two * seed inputs
diagnosticIterationUniformBound inputs zero = seedBelowTwoSeed inputs
diagnosticIterationUniformBound inputs (suc iteration) =
  let
    oldBound = diagnosticIterationUniformBound inputs iteration

    thetaTimesOld :
      theta inputs * diagnosticIterate inputs iteration
      ≤ theta inputs * (two * seed inputs)
    thetaTimesOld =
      let
        instance thetaIsNonnegative =
          nonNegative (thetaNonnegative inputs)
      in
      ℚₚ.*-monoˡ-≤-nonNeg (theta inputs) oldBound

    thetaTimesTwoSeed :
      theta inputs * (two * seed inputs)
      ≤ quarter * (two * seed inputs)
    thetaTimesTwoSeed =
      let
        instance twoSeedIsNonnegative =
          nonNegative (twoSeedNonnegative inputs)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (two * seed inputs)
        (thetaBelowQuarter inputs)

    nearBound :
      theta inputs * diagnosticIterate inputs iteration
      ≤ half * seed inputs
    nearBound =
      ℚₚ.≤-trans
        thetaTimesOld
        (subst
          (λ upper →
            theta inputs * (two * seed inputs) ≤ upper)
          (solve (seed inputs ∷ []))
          thetaTimesTwoSeed)

    combined :
      farHistory inputs
        + theta inputs * diagnosticIterate inputs iteration
      ≤ half * seed inputs + half * seed inputs
    combined =
      ℚₚ.+-mono-≤
        (farHistoryBelowHalfSeed inputs)
        nearBound

    combinedToSeed :
      half * seed inputs + half * seed inputs ≤ seed inputs
    combinedToSeed =
      subst
        (λ lower → lower ≤ seed inputs)
        (solve (seed inputs ∷ []))
        ℚₚ.≤-refl
  in
  ℚₚ.≤-trans
    (ℚₚ.≤-trans combined combinedToSeed)
    (seedBelowTwoSeed inputs)
