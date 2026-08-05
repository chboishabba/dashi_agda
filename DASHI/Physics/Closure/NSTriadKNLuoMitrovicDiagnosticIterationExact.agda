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
--   0 <= theta <= 1/2,
--   w(0)=seed,
--   w(n+1)=farHistory+theta*w(n).
--
-- Exact rational induction gives w(n)<=2*seed for every finite n.  This
-- theorem does not derive the terminal tail relation or the seed lower bound
-- from the energy inequality and therefore cannot be mistaken for an
-- unconditional Navier--Stokes regularity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

half two : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1

record DiagnosticIterationData : Set where
  constructor diagnostic-iteration-data
  field
    seed farHistory theta : ℚ

    seedNonnegative : 0ℚ ≤ seed
    farHistoryNonnegative : 0ℚ ≤ farHistory
    thetaNonnegative : 0ℚ ≤ theta

    farHistoryBelowHalfSeed : farHistory ≤ half * seed
    thetaBelowHalf : theta ≤ half

open DiagnosticIterationData public

diagnosticIterate : DiagnosticIterationData → Nat → ℚ
diagnosticIterate inputs zero = seed inputs
diagnosticIterate inputs (suc iteration) =
  farHistory inputs + theta inputs * diagnosticIterate inputs iteration

twoSeedNonnegative :
  (inputs : DiagnosticIterationData) →
  0ℚ ≤ two * seed inputs
twoSeedNonnegative inputs =
  let
    twoNonnegative : 0ℚ ≤ two
    twoNonnegative =
      ℚₚ.≤-trans (seedNonnegative inputs)
        (subst
          (λ upper → seed inputs ≤ upper)
          (solve (seed inputs ∷ []))
          ℚₚ.≤-refl)

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
diagnosticIterationUniformBound inputs zero =
  let
    target : seed inputs ≤ two * seed inputs
    target =
      subst
        (λ upper → seed inputs ≤ upper)
        (solve (seed inputs ∷ []))
        (ℚₚ.+-monoʳ-≤
          (seed inputs)
          (seedNonnegative inputs))
  in
  target
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
      ≤ half * (two * seed inputs)
    thetaTimesTwoSeed =
      let
        instance twoSeedIsNonnegative =
          nonNegative (twoSeedNonnegative inputs)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (two * seed inputs)
        (thetaBelowHalf inputs)

    nearBound :
      theta inputs * diagnosticIterate inputs iteration
      ≤ seed inputs
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
      ≤ half * seed inputs + seed inputs
    combined =
      ℚₚ.+-mono-≤
        (farHistoryBelowHalfSeed inputs)
        nearBound

    targetMeaning :
      half * seed inputs + seed inputs
      ≤ two * seed inputs
    targetMeaning =
      let
        halfSeedNonnegative : 0ℚ ≤ half * seed inputs
        halfSeedNonnegative =
          let
            halfNonnegative : 0ℚ ≤ half
            halfNonnegative =
              subst
                (λ lower → lower ≤ half)
                (solve [])
                (seedNonnegative inputs)
            instance
              halfIsNonnegative = nonNegative halfNonnegative
              seedIsNonnegative = nonNegative (seedNonnegative inputs)
              productIsNonnegative =
                ℚₚ.nonNeg*nonNeg⇒nonNeg half (seed inputs)
          in
          ℚₚ.nonNegative⁻¹ (half * seed inputs)
      in
      subst
        (λ upper → half * seed inputs + seed inputs ≤ upper)
        (solve (seed inputs ∷ []))
        (ℚₚ.+-monoˡ-≤
          (seed inputs)
          (subst
            (λ lower → lower ≤ seed inputs)
            (solve (seed inputs ∷ []))
            halfSeedNonnegative))
  in
  ℚₚ.≤-trans combined targetMeaning
