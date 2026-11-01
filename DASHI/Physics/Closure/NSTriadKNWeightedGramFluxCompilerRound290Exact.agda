module DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact where

------------------------------------------------------------------------
-- ROUND290 / RESOLVENT-WEIGHTED GRAM FLUX COMPILER
--
-- R289 rejects the naive identification of quartic Gram debt with the
-- nonlinear part of dQ/dt: the latter is quintic.  The physical damping
-- convention in R94 supplies the missing compatible quartic structure.
--
-- For two R227 cells alpha,beta let
--
--   g = 2 Re <A_alpha,A_beta>
--
-- and suppose their pair tangent has the physical damped form
--
--   dg = -lambda g + r,
--   lambda = lambda_alpha + lambda_beta > 0,
--
-- where r is the nonlinear/product-rule remainder.  Choose a resolvent weight
-- w with
--
--   w * lambda = 1.
--
-- Then for the weighted phase/Gram flux F = w g,
--
--   dF = -g + w r.
--
-- Equivalently,
--
--   g = -dF + w r.
--
-- After summing over the finite off-diagonal same-output carrier and
-- integrating in time, the quartic coherent Gram debt becomes endpoint flux
-- plus a weighted nonlinear remainder.  This is exactly the temporal shape
-- wanted by R222.
--
-- The theorem below is only the ordered-field/algebraic compiler.  The next
-- physical theorem must identify lambda with the literal viscous pair rate
-- nu(|p|^2+|q|^2+|p'|^2+|q'|^2), identify g with the actual R179/R288 Gram
-- scalar, and identify r with the R230 nonlinear product-rule work.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record DampedGramPair : Set where
  constructor damped-gram-pair
  field
    gram pairRate nonlinearRemainder gramTangent resolventWeight : ℚ

    tangentLaw :
      gramTangent ≡ (0ℚ - pairRate) * gram + nonlinearRemainder

    resolventLaw :
      resolventWeight * pairRate ≡ 1ℚ

open DampedGramPair public

weightedGramFlux : DampedGramPair → ℚ
weightedGramFlux P = resolventWeight P * gram P

weightedGramFluxTangent : DampedGramPair → ℚ
weightedGramFluxTangent P = resolventWeight P * gramTangent P

weightedNonlinearRemainder : DampedGramPair → ℚ
weightedNonlinearRemainder P = resolventWeight P * nonlinearRemainder P

weightedFluxDerivativeIdentity :
  (P : DampedGramPair) →
  weightedGramFluxTangent P
  ≡ (0ℚ - gram P) + weightedNonlinearRemainder P
weightedFluxDerivativeIdentity P =
  trans
    (cong (resolventWeight P *_) (tangentLaw P))
    (reduce P)
  where
  reduce : (Q : DampedGramPair) →
    resolventWeight Q
      * (((0ℚ - pairRate Q) * gram Q) + nonlinearRemainder Q)
    ≡ (0ℚ - gram Q) + resolventWeight Q * nonlinearRemainder Q
  reduce Q rewrite resolventLaw Q =
    solve
      (gram Q ∷ nonlinearRemainder Q ∷ resolventWeight Q ∷ pairRate Q ∷ [])

gramAsNegativeFluxDerivativePlusRemainder :
  (P : DampedGramPair) →
  gram P
  ≡ (0ℚ - weightedGramFluxTangent P) + weightedNonlinearRemainder P
gramAsNegativeFluxDerivativePlusRemainder P =
  let identity = weightedFluxDerivativeIdentity P
  in
  trans
    (sym (solve (gram P ∷ weightedNonlinearRemainder P ∷ [])))
    (cong
      (λ x → (0ℚ - x) + weightedNonlinearRemainder P)
      (sym identity))

round290WeightedGramFluxCompilerClosed : Bool
round290WeightedGramFluxCompilerClosed = true

round290UsesViscousRateResolvent : Bool
round290UsesViscousRateResolvent = true

round290RequiresNonlinearRemainderSign : Bool
round290RequiresNonlinearRemainderSign = false

round290PhysicalR227PairTangentIdentified : Bool
round290PhysicalR227PairTangentIdentified = false

round290WeightedNonlinearRemainderPaid : Bool
round290WeightedNonlinearRemainderPaid = false

round290R222IntegratedBudgetClosed : Bool
round290R222IntegratedBudgetClosed = false

round290PackageAClosed : Bool
round290PackageAClosed = false

round290ClayPromotion : Bool
round290ClayPromotion = false

round290WeightedGramFluxCompilerClosedIsTrue :
  round290WeightedGramFluxCompilerClosed ≡ true
round290WeightedGramFluxCompilerClosedIsTrue = refl

round290PhysicalR227PairTangentIdentifiedIsFalse :
  round290PhysicalR227PairTangentIdentified ≡ false
round290PhysicalR227PairTangentIdentifiedIsFalse = refl
