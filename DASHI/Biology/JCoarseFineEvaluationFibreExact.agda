module DASHI.Biology.JCoarseFineEvaluationFibreExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves",
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Construct the exact finite analogue of a coarse point with fine data over
-- it.  The repository's distinguished completion channel j is not an ordinary
-- T^2 residue.  A full fine assignment is evaluated at j, and a constant
-- section proves that every one of the 3^9 fine-frequency values occurs as a
-- j-evaluation.  The evaluation fibre over each value is therefore inhabited.
--
-- The authentic modular interpretation is a forgetful map from elliptic curves
-- with level structure to their coarse j-invariant.  This module proves only
-- the finite DASHI model and records that the modular-curve theorem itself is
-- not reconstructed internally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Nat using (_*_)
open import Data.Product using (Σ; _,_)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.JFineCoarseRelativeScaleExact as Scale
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient

record PointedCoarseFineEvaluation : Set₁ where
  constructor pointed-coarse-fine-evaluation
  field
    Coarse Fine Assignment : Set
    distinguishedCoarse : Coarse
    evaluateAtDistinguished : Assignment → Fine
    section : Fine → Assignment
    evaluateSection :
      (fine : Fine) → evaluateAtDistinguished (section fine) ≡ fine

open PointedCoarseFineEvaluation public

constantFineAssignment : Harmonic.FineFrequency → Harmonic.FullFineAssignment
constantFineAssignment fine channel = fine

constantAssignmentEvaluatesAtJ :
  (fine : Harmonic.FineFrequency) →
  Harmonic.jFine (constantFineAssignment fine) ≡ fine
constantAssignmentEvaluatesAtJ fine = refl

canonicalJCoarseFineEvaluation : PointedCoarseFineEvaluation
canonicalJCoarseFineEvaluation =
  pointed-coarse-fine-evaluation
    Harmonic.CoarseChannel
    Harmonic.FineFrequency
    Harmonic.FullFineAssignment
    Harmonic.completionJ
    Harmonic.jFine
    constantFineAssignment
    constantAssignmentEvaluatesAtJ

JFineEvaluationFibre : Harmonic.FineFrequency → Set
JFineEvaluationFibre fine =
  Σ Harmonic.FullFineAssignment
    (λ assignment → Harmonic.jFine assignment ≡ fine)

canonicalJFineFibrePoint :
  (fine : Harmonic.FineFrequency) → JFineEvaluationFibre fine
canonicalJFineFibrePoint fine = constantFineAssignment fine , refl

jEvaluationIsSurjective :
  (fine : Harmonic.FineFrequency) →
  Σ Harmonic.FullFineAssignment
    (λ assignment → Harmonic.jFine assignment ≡ fine)
jEvaluationIsSurjective = canonicalJFineFibrePoint

completionJIsNotOrdinaryChannel :
  (pair : Harmonic.BalancedPair) →
  Harmonic.completionJ ≡ Harmonic.ordinaryChannel pair → ⊥
completionJIsNotOrdinaryChannel pair ()

completionStateMapsExactlyToJ :
  Quotient.toCoarseChannel Quotient.j9 ≡ Harmonic.completionJ
completionStateMapsExactlyToJ = refl

ordinaryStatesDoNotMapToCompletionJ :
  (pair : Harmonic.BalancedPair) →
  Harmonic.ordinaryChannel pair ≡ Harmonic.completionJ → ⊥
ordinaryStatesDoNotMapToCompletionJ pair ()

jCoarseFrequencyIsNine : Scale.jCoarseFrequency ≡ 9
jCoarseFrequencyIsNine = refl

jFineFrequencyIsThreePowerNine : Scale.jFineFrequency ≡ 19683
jFineFrequencyIsThreePowerNine = refl

jAbsoluteFineFrequencyIsThreePowerEleven :
  Scale.jAbsoluteFineFrequency ≡ 177147
jAbsoluteFineFrequencyIsThreePowerEleven = refl

jAbsoluteIsCoarseTimesFine :
  Scale.jAbsoluteFineFrequency
  ≡ Scale.jCoarseFrequency * Scale.jFineFrequency
jAbsoluteIsCoarseTimesFine = Scale.jAbsoluteFineIsCoarseTimesJFine

jFineCodomainHasRelativeFrequencyDimension :
  Harmonic.fineFrequencyDimension ≡ Scale.jFineFrequency
jFineCodomainHasRelativeFrequencyDimension = refl

------------------------------------------------------------------------
-- FineFrequency is the evaluation codomain.  A fixed-value fibre is the set
-- of complete assignments evaluating to that value and is not assigned size
-- 3^9 merely because the codomain has that dimension.
------------------------------------------------------------------------

record JCoarseFineEvaluationBoundary : Set₁ where
  constructor j-coarse-fine-evaluation-boundary
  field
    evaluationSectionLaw :
      (fine : Harmonic.FineFrequency) →
      Harmonic.jFine (constantFineAssignment fine) ≡ fine
    everyFineValueFibrePoint :
      (fine : Harmonic.FineFrequency) → JFineEvaluationFibre fine
    absoluteScaleFactorisation :
      Scale.jAbsoluteFineFrequency
      ≡ Scale.jCoarseFrequency * Scale.jFineFrequency
    fixedValueAssignmentFibreHasCardinalityThreePowerNine : Bool
    fixedValueAssignmentFibreHasCardinalityThreePowerNineIsFalse :
      fixedValueAssignmentFibreHasCardinalityThreePowerNine ≡ false
    finiteJModelIsLiteralModularCurve : Bool
    finiteJModelIsLiteralModularCurveIsFalse :
      finiteJModelIsLiteralModularCurve ≡ false
    supersingularJDescentProvedInternally : Bool
    supersingularJDescentProvedInternallyIsFalse :
      supersingularJDescentProvedInternally ≡ false

canonicalJCoarseFineEvaluationBoundary : JCoarseFineEvaluationBoundary
canonicalJCoarseFineEvaluationBoundary =
  j-coarse-fine-evaluation-boundary
    constantAssignmentEvaluatesAtJ
    canonicalJFineFibrePoint
    jAbsoluteIsCoarseTimesFine
    false refl
    false refl
    false refl
