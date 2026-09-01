module DASHI.Physics.Closure.NSTriadKNResolventYoungAbsorptionRound300Exact where

------------------------------------------------------------------------
-- ROUND300 / RADICAL-FREE YOUNG ABSORPTION FOR THE HEAT-RESOLVENT CROSS WORK
--
-- After R299 the weighted nonlinear pair remainder has the form
--
--   4 Re <A_s,F_s>.
--
-- Do not introduce square roots.  The natural repository identity is
--
--   eta ||A_s||^2 + 4 etaInv ||F_s||^2 - 4 Re<A_s,F_s>
--     = etaInv || eta A_s - 2 F_s ||^2 >= 0,
--
-- with etaInv * eta = 1.  This yields
--
--   4 Re<A_s,F_s>
--     <= eta ||A_s||^2 + 4 etaInv ||F_s||^2.
--
-- The finite C3 completion identity is routine algebra on the literal vectors;
-- this compiler exposes it explicitly rather than assuming the target bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

four : ℚ
four = 4

record ResolventYoungCompletion : Set where
  constructor resolvent-young-completion
  field
    eta etaInverse amplitudeMass forcingMass aggregateCross completionMass : ℚ

    etaInverseLaw : etaInverse * eta ≡ 1

    completionIdentity :
      eta * amplitudeMass
      + four * etaInverse * forcingMass
      - four * aggregateCross
      ≡ etaInverse * completionMass

    weightedCompletionNonnegative :
      0ℚ ≤ etaInverse * completionMass

open ResolventYoungCompletion public

fourCrossAbsorbed :
  (P : ResolventYoungCompletion) →
  four * aggregateCross P
  ≤ eta P * amplitudeMass P
    + four * etaInverse P * forcingMass P
fourCrossAbsorbed P =
  let
    completedNN :
      0ℚ ≤
        eta P * amplitudeMass P
        + four * etaInverse P * forcingMass P
        - four * aggregateCross P
    completedNN = subst
      (0ℚ ≤_)
      (sym (completionIdentity P))
      (weightedCompletionNonnegative P)

    shifted = ℚP.+-monoˡ-≤ (four * aggregateCross P) completedNN

    normalizeLeft :
      four * aggregateCross P + 0ℚ ≡ four * aggregateCross P
    normalizeLeft = solve (aggregateCross P ∷ [])

    normalizeRight :
      four * aggregateCross P
      + (eta P * amplitudeMass P
        + four * etaInverse P * forcingMass P
        - four * aggregateCross P)
      ≡ eta P * amplitudeMass P
        + four * etaInverse P * forcingMass P
    normalizeRight = solve
      ( eta P ∷ etaInverse P ∷ amplitudeMass P
      ∷ forcingMass P ∷ aggregateCross P ∷ [])
  in
  subst
    (λ left → left ≤ eta P * amplitudeMass P
      + four * etaInverse P * forcingMass P)
    normalizeLeft
    (subst
      (four * aggregateCross P + 0ℚ ≤_)
      normalizeRight
      shifted)

record IntegratedResolventAbsorptionLeaf : Set where
  constructor integrated-resolvent-absorption-leaf
  field
    absorbedAmplitudeContribution : ℚ
    forcingContribution : ℚ
    weightedRemainder : ℚ
    weightedRemainderBound :
      weightedRemainder ≤ absorbedAmplitudeContribution + forcingContribution

open IntegratedResolventAbsorptionLeaf public

round300SquareCompletionCompilerClosed : Bool
round300SquareCompletionCompilerClosed = true

round300UsesSquareRoots : Bool
round300UsesSquareRoots = false

round300AmplitudeTermIdentifiedWithPositiveResolventForm : Bool
round300AmplitudeTermIdentifiedWithPositiveResolventForm = false

round300HeatWeightedForcingSpacetimePaid : Bool
round300HeatWeightedForcingSpacetimePaid = false

round300PackageAClosed : Bool
round300PackageAClosed = false

round300ClayPromotion : Bool
round300ClayPromotion = false

round300SquareCompletionCompilerClosedIsTrue :
  round300SquareCompletionCompilerClosed ≡ true
round300SquareCompletionCompilerClosedIsTrue = refl
