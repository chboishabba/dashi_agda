module DASHI.Physics.Closure.NSTriadKNLuoScopedPairedSecondMomentBudgetExact where

------------------------------------------------------------------------
-- SCOPED CORRECTION OF THE AUG-5 PAIRED SECOND-MOMENT INTERFACE
--
-- Historical/provenance note.
--
-- `NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact` stores a finite
-- `samples` list but its six envelope fields quantify over *every*
-- `PairedSecondMomentSample`, not only members of that list.  The finite
-- summation theorem subsequently uses those universal hypotheses only on the
-- declared samples.
--
-- This owner preserves the old theorem unchanged and adds the least-privilege
-- interface actually required by the finite proof: every envelope is required
-- only for a sample carrying evidence that it belongs to the declared family.
-- The rational pointwise algebra and second-moment factorization are otherwise
-- identical to the Aug-5 theorem.
--
-- This is an interface correction, not a new PDE estimate.  In particular it
-- does not supply cutoff-uniform physical constants for the R571 carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; here; there)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment

record ScopedPairedSecondMomentBudget : Set₁ where
  field
    samples : List Moment.PairedSecondMomentSample
    transportGradient derivativeCurvature : ℚ
    transportCurvature derivativeEnvelope : ℚ

    transportGradientNonnegative : 0ℚ ≤ transportGradient
    derivativeCurvatureNonnegative : 0ℚ ≤ derivativeCurvature
    transportCurvatureNonnegative : 0ℚ ≤ transportCurvature
    derivativeEnvelopeNonnegative : 0ℚ ≤ derivativeEnvelope

    linearIncrementBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.linearIncrement sample
      ≤ Moment.displacement sample * transportGradient

    derivativeDifferenceBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.derivativeDifference sample
      ≤ Moment.displacement sample * derivativeCurvature

    plusRemainderBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.plusRemainder sample
      ≤ Moment.displacement sample * Moment.displacement sample
        * transportCurvature

    minusRemainderBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.minusRemainder sample
      ≤ Moment.displacement sample * Moment.displacement sample
        * transportCurvature

    plusDerivativeBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.plusDerivative sample ≤ derivativeEnvelope

    minusDerivativeBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.minusDerivative sample ≤ derivativeEnvelope

open ScopedPairedSecondMomentBudget public

scopedSecondMomentCoefficient : ScopedPairedSecondMomentBudget → ℚ
scopedSecondMomentCoefficient budget =
  transportGradient budget * derivativeCurvature budget
  + transportCurvature budget * derivativeEnvelope budget
  + transportCurvature budget * derivativeEnvelope budget

scopedPointwisePairedSecondMomentBound :
  (budget : ScopedPairedSecondMomentBudget) →
  (sample : Moment.PairedSecondMomentSample) →
  sample ∈ samples budget →
  Moment.pairedMagnitude sample
  ≤ Moment.weightedSecondMoment sample * scopedSecondMomentCoefficient budget
scopedPointwisePairedSecondMomentBound budget sample member =
  let
    displacementSquaredNonnegative :
      0ℚ ≤ Moment.displacement sample * Moment.displacement sample
    displacementSquaredNonnegative =
      Moment.productNonnegative
        (Moment.displacement sample)
        (Moment.displacement sample)
        (Moment.displacementNonnegative sample)
        (Moment.displacementNonnegative sample)

    displacementGradientNonnegative :
      0ℚ ≤ Moment.displacement sample * transportGradient budget
    displacementGradientNonnegative =
      Moment.productNonnegative
        (Moment.displacement sample)
        (transportGradient budget)
        (Moment.displacementNonnegative sample)
        (transportGradientNonnegative budget)

    displacementDerivativeCurvatureNonnegative :
      0ℚ ≤ Moment.displacement sample * derivativeCurvature budget
    displacementDerivativeCurvatureNonnegative =
      Moment.productNonnegative
        (Moment.displacement sample)
        (derivativeCurvature budget)
        (Moment.displacementNonnegative sample)
        (derivativeCurvatureNonnegative budget)

    squaredTransportCurvatureNonnegative :
      0ℚ ≤ Moment.displacement sample * Moment.displacement sample
        * transportCurvature budget
    squaredTransportCurvatureNonnegative =
      Moment.productNonnegative
        (Moment.displacement sample * Moment.displacement sample)
        (transportCurvature budget)
        displacementSquaredNonnegative
        (transportCurvatureNonnegative budget)

    linearTermBound :
      Moment.linearIncrement sample * Moment.derivativeDifference sample
      ≤ (Moment.displacement sample * Moment.displacement sample)
        * (transportGradient budget * derivativeCurvature budget)
    linearTermBound =
      subst
        (λ upper →
          Moment.linearIncrement sample * Moment.derivativeDifference sample
          ≤ upper)
        (solve
          ( Moment.displacement sample
          ∷ transportGradient budget
          ∷ derivativeCurvature budget
          ∷ []))
        (Moment.multiplyBounds
          (Moment.linearIncrementNonnegative sample)
          displacementGradientNonnegative
          (Moment.derivativeDifferenceNonnegative sample)
          displacementDerivativeCurvatureNonnegative
          (linearIncrementBound budget sample member)
          (derivativeDifferenceBound budget sample member))

    plusTermBound :
      Moment.plusRemainder sample * Moment.plusDerivative sample
      ≤ (Moment.displacement sample * Moment.displacement sample)
        * (transportCurvature budget * derivativeEnvelope budget)
    plusTermBound =
      subst
        (λ upper → Moment.plusRemainder sample * Moment.plusDerivative sample ≤ upper)
        (solve
          ( Moment.displacement sample
          ∷ transportCurvature budget
          ∷ derivativeEnvelope budget
          ∷ []))
        (Moment.multiplyBounds
          (Moment.plusRemainderNonnegative sample)
          squaredTransportCurvatureNonnegative
          (Moment.plusDerivativeNonnegative sample)
          (derivativeEnvelopeNonnegative budget)
          (plusRemainderBound budget sample member)
          (plusDerivativeBound budget sample member))

    minusTermBound :
      Moment.minusRemainder sample * Moment.minusDerivative sample
      ≤ (Moment.displacement sample * Moment.displacement sample)
        * (transportCurvature budget * derivativeEnvelope budget)
    minusTermBound =
      subst
        (λ upper → Moment.minusRemainder sample * Moment.minusDerivative sample ≤ upper)
        (solve
          ( Moment.displacement sample
          ∷ transportCurvature budget
          ∷ derivativeEnvelope budget
          ∷ []))
        (Moment.multiplyBounds
          (Moment.minusRemainderNonnegative sample)
          squaredTransportCurvatureNonnegative
          (Moment.minusDerivativeNonnegative sample)
          (derivativeEnvelopeNonnegative budget)
          (minusRemainderBound budget sample member)
          (minusDerivativeBound budget sample member))

    innerBound :
      Moment.linearIncrement sample * Moment.derivativeDifference sample
        + Moment.plusRemainder sample * Moment.plusDerivative sample
        + Moment.minusRemainder sample * Moment.minusDerivative sample
      ≤ (Moment.displacement sample * Moment.displacement sample)
        * scopedSecondMomentCoefficient budget
    innerBound =
      subst
        (λ upper →
          Moment.linearIncrement sample * Moment.derivativeDifference sample
            + Moment.plusRemainder sample * Moment.plusDerivative sample
            + Moment.minusRemainder sample * Moment.minusDerivative sample
          ≤ upper)
        (solve
          ( Moment.displacement sample
          ∷ transportGradient budget
          ∷ derivativeCurvature budget
          ∷ transportCurvature budget
          ∷ derivativeEnvelope budget
          ∷ []))
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤ linearTermBound plusTermBound)
          minusTermBound)

    weightedBound :
      Moment.pairedMagnitude sample
      ≤ Moment.weight sample
        * ((Moment.displacement sample * Moment.displacement sample)
          * scopedSecondMomentCoefficient budget)
    weightedBound =
      let
        instance
          weightIsNonnegative = nonNegative (Moment.weightNonnegative sample)
      in
      ℚP.*-monoˡ-≤-nonNeg (Moment.weight sample) innerBound

    targetMeaning :
      Moment.weight sample
        * ((Moment.displacement sample * Moment.displacement sample)
          * scopedSecondMomentCoefficient budget)
      ≡ Moment.weightedSecondMoment sample * scopedSecondMomentCoefficient budget
    targetMeaning =
      solve
        ( Moment.weight sample
        ∷ Moment.displacement sample
        ∷ scopedSecondMomentCoefficient budget
        ∷ [])
  in
  subst
    (λ upper → Moment.pairedMagnitude sample ≤ upper)
    targetMeaning
    weightedBound

scopedSumBoundOn :
  (budget : ScopedPairedSecondMomentBudget) →
  (family : List Moment.PairedSecondMomentSample) →
  ((sample : Moment.PairedSecondMomentSample) →
    sample ∈ family → sample ∈ samples budget) →
  Sum.sumBy family Moment.pairedMagnitude
  ≤ scopedSecondMomentCoefficient budget
      * Sum.sumBy family Moment.weightedSecondMoment
scopedSumBoundOn budget [] included =
  subst
    (0ℚ ≤_)
    (sym (solve (scopedSecondMomentCoefficient budget ∷ [])))
    ℚP.≤-refl
scopedSumBoundOn budget (sample ∷ rest) included =
  let
    local :
      Moment.pairedMagnitude sample
      ≤ scopedSecondMomentCoefficient budget
          * Moment.weightedSecondMoment sample
    local =
      subst
        (λ upper → Moment.pairedMagnitude sample ≤ upper)
        (solve
          ( Moment.weightedSecondMoment sample
          ∷ scopedSecondMomentCoefficient budget
          ∷ []))
        (scopedPointwisePairedSecondMomentBound
          budget sample (included sample (here refl)))

    tail :
      Sum.sumBy rest Moment.pairedMagnitude
      ≤ scopedSecondMomentCoefficient budget
          * Sum.sumBy rest Moment.weightedSecondMoment
    tail =
      scopedSumBoundOn budget rest
        (λ other member → included other (there member))

    summed :
      Moment.pairedMagnitude sample
        + Sum.sumBy rest Moment.pairedMagnitude
      ≤ scopedSecondMomentCoefficient budget * Moment.weightedSecondMoment sample
        + scopedSecondMomentCoefficient budget
          * Sum.sumBy rest Moment.weightedSecondMoment
    summed = ℚP.+-mono-≤ local tail

    factorized :
      scopedSecondMomentCoefficient budget * Moment.weightedSecondMoment sample
        + scopedSecondMomentCoefficient budget
          * Sum.sumBy rest Moment.weightedSecondMoment
      ≡ scopedSecondMomentCoefficient budget
          * (Moment.weightedSecondMoment sample
            + Sum.sumBy rest Moment.weightedSecondMoment)
    factorized =
      solve
        ( scopedSecondMomentCoefficient budget
        ∷ Moment.weightedSecondMoment sample
        ∷ Sum.sumBy rest Moment.weightedSecondMoment
        ∷ [])
  in
  subst
    (λ upper →
      Moment.pairedMagnitude sample
        + Sum.sumBy rest Moment.pairedMagnitude
      ≤ upper)
    factorized
    summed

finiteScopedPairedSecondMomentBound :
  (budget : ScopedPairedSecondMomentBudget) →
  Sum.sumBy (samples budget) Moment.pairedMagnitude
  ≤ scopedSecondMomentCoefficient budget
      * Sum.sumBy (samples budget) Moment.weightedSecondMoment
finiteScopedPairedSecondMomentBound budget =
  scopedSumBoundOn budget (samples budget) (λ sample member → member)

fromUniversalBudget :
  Moment.PairedSecondMomentBudget → ScopedPairedSecondMomentBudget
fromUniversalBudget budget = record
  { samples = Moment.samples budget
  ; transportGradient = Moment.transportGradient budget
  ; derivativeCurvature = Moment.derivativeCurvature budget
  ; transportCurvature = Moment.transportCurvature budget
  ; derivativeEnvelope = Moment.derivativeEnvelope budget
  ; transportGradientNonnegative = Moment.transportGradientNonnegative budget
  ; derivativeCurvatureNonnegative = Moment.derivativeCurvatureNonnegative budget
  ; transportCurvatureNonnegative = Moment.transportCurvatureNonnegative budget
  ; derivativeEnvelopeNonnegative = Moment.derivativeEnvelopeNonnegative budget
  ; linearIncrementBound = λ sample member → Moment.linearIncrementBound budget sample
  ; derivativeDifferenceBound = λ sample member → Moment.derivativeDifferenceBound budget sample
  ; plusRemainderBound = λ sample member → Moment.plusRemainderBound budget sample
  ; minusRemainderBound = λ sample member → Moment.minusRemainderBound budget sample
  ; plusDerivativeBound = λ sample member → Moment.plusDerivativeBound budget sample
  ; minusDerivativeBound = λ sample member → Moment.minusDerivativeBound budget sample
  }

scopedPairedSecondMomentCompilerClosed : Bool
scopedPairedSecondMomentCompilerClosed = true

oldUniversalPairedSecondMomentBudgetRetained : Bool
oldUniversalPairedSecondMomentBudgetRetained = true

scopedBudgetClosesCutoffUniformPhysicalProducer : Bool
scopedBudgetClosesCutoffUniformPhysicalProducer = false
