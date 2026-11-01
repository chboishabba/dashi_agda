module DASHI.Physics.YangMills.BalabanP33FiniteQuaternionSimpleDuhamelIntegralExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Joseph Diestel and John J. Uhl, Jr.,
-- "Vector Measures", Mathematical Surveys 15, American Mathematical Society,
-- 1977. DOI: 10.1090/SURV/015.
--
-- Jan Mikusinski,
-- "The Bochner Integral", Birkhaeuser, 1978.
-- DOI: 10.1007/978-3-0348-5567-9.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- A Bochner integral is obtained as a completion of vector-valued simple
-- integrals.  This module proves the complete finite-simple-function algebra
-- for the quaternion Duhamel integrand.  Every sample carries a scalar weight
-- and three exponential factors.  The exact pointwise noncommutative telescope
-- is transported through the finite weighted fold, with no reordering and no
-- hidden linearity premise.
--
-- The remaining continuum theorem is now specifically convergence of these
-- finite simple integrals, the norm inequality for their limit, and
-- differentiation under that limit.  It is not the unrelated geometric
-- Bochner identity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (Quaternion; zeroQ; _+q_; scaleRealQ)
import DASHI.Physics.YangMills.BalabanP33QuaternionProductSecondVariationExact as Product
import DASHI.Physics.YangMills.BalabanP33QuaternionDuhamelIntegrandTelescopeExact as Telescope

record OrderedSimpleSample : Set where
  constructor orderedSample
  field
    sampleWeight : ℝ
    leftExponential middleExponential rightExponential : Quaternion

open OrderedSimpleSample public

sumQuaternion : List Quaternion → Quaternion
sumQuaternion = Product.sumQuaternion

weightedQuaternion : ℝ → Quaternion → Quaternion
weightedQuaternion = scaleRealQ

orderedSampleIntegrand :
  Quaternion → Quaternion → OrderedSimpleSample → Quaternion
orderedSampleIntegrand h k sample =
  Telescope.orderedIntegrand
    (leftExponential sample) h
    (middleExponential sample) k
    (rightExponential sample)

orderedSampleDefect :
  Quaternion → Quaternion → OrderedSimpleSample → Quaternion
orderedSampleDefect h k sample =
  Telescope.subQ
    (orderedSampleIntegrand h k sample)
    (Telescope.orderedReference h k)

orderedSampleTelescopeTerms :
  Quaternion → Quaternion → OrderedSimpleSample → Quaternion
orderedSampleTelescopeTerms h k sample =
  Telescope.orderedDefectSum
    (leftExponential sample) h
    (middleExponential sample) k
    (rightExponential sample)

weightedOrderedDefect :
  Quaternion → Quaternion → OrderedSimpleSample → Quaternion
weightedOrderedDefect h k sample =
  weightedQuaternion (sampleWeight sample)
    (orderedSampleDefect h k sample)

weightedOrderedTelescopeTerms :
  Quaternion → Quaternion → OrderedSimpleSample → Quaternion
weightedOrderedTelescopeTerms h k sample =
  weightedQuaternion (sampleWeight sample)
    (orderedSampleTelescopeTerms h k sample)

finiteOrderedSimpleIntegral :
  Quaternion → Quaternion → List OrderedSimpleSample → Quaternion
finiteOrderedSimpleIntegral h k samples =
  sumQuaternion (map (weightedOrderedDefect h k) samples)

finiteOrderedTelescopeIntegral :
  Quaternion → Quaternion → List OrderedSimpleSample → Quaternion
finiteOrderedTelescopeIntegral h k samples =
  sumQuaternion (map (weightedOrderedTelescopeTerms h k) samples)

weightedPointwiseTelescopeExact :
  ∀ h k sample →
  weightedOrderedDefect h k sample
  ≡ weightedOrderedTelescopeTerms h k sample
weightedPointwiseTelescopeExact h k sample =
  cong (weightedQuaternion (sampleWeight sample))
    (Telescope.orderedDuhamelIntegrandTelescopeExact
      (leftExponential sample) h
      (middleExponential sample) k
      (rightExponential sample))

finiteOrderedSimpleIntegralTelescopeExact :
  ∀ h k samples →
  finiteOrderedSimpleIntegral h k samples
  ≡ finiteOrderedTelescopeIntegral h k samples
finiteOrderedSimpleIntegralTelescopeExact h k [] = refl
finiteOrderedSimpleIntegralTelescopeExact h k (sample ∷ samples) =
  cong₂ _+q_
    (weightedPointwiseTelescopeExact h k sample)
    (finiteOrderedSimpleIntegralTelescopeExact h k samples)

------------------------------------------------------------------------
-- The symmetric D^2 exp expression consists of the H/K and K/H orderings.
------------------------------------------------------------------------

finiteSymmetricSimpleIntegral :
  Quaternion → Quaternion → List OrderedSimpleSample → Quaternion
finiteSymmetricSimpleIntegral h k samples =
  finiteOrderedSimpleIntegral h k samples
  +q finiteOrderedSimpleIntegral k h samples

finiteSymmetricTelescopeIntegral :
  Quaternion → Quaternion → List OrderedSimpleSample → Quaternion
finiteSymmetricTelescopeIntegral h k samples =
  finiteOrderedTelescopeIntegral h k samples
  +q finiteOrderedTelescopeIntegral k h samples

finiteSymmetricSimpleIntegralTelescopeExact :
  ∀ h k samples →
  finiteSymmetricSimpleIntegral h k samples
  ≡ finiteSymmetricTelescopeIntegral h k samples
finiteSymmetricSimpleIntegralTelescopeExact h k samples =
  cong₂ _+q_
    (finiteOrderedSimpleIntegralTelescopeExact h k samples)
    (finiteOrderedSimpleIntegralTelescopeExact k h samples)

------------------------------------------------------------------------
-- Refinement compatibility is expressed without a measure theory: replacing
-- one weighted sample by finitely many samples with the same weighted value
-- leaves the fold unchanged.  This is the exact algebra used when refining a
-- simple-function partition.
------------------------------------------------------------------------

record WeightedSampleRefinement
    (h k : Quaternion)
    (coarse : OrderedSimpleSample)
    (fine : List OrderedSimpleSample) : Set where
  field
    integrandRefinement :
      weightedOrderedDefect h k coarse
      ≡ sumQuaternion (map (weightedOrderedDefect h k) fine)

open WeightedSampleRefinement public

replaceHeadByRefinement :
  ∀ h k coarse fine tail →
  WeightedSampleRefinement h k coarse fine →
  weightedOrderedDefect h k coarse
    +q finiteOrderedSimpleIntegral h k tail
  ≡ sumQuaternion
      (map (weightedOrderedDefect h k) fine)
      +q finiteOrderedSimpleIntegral h k tail
replaceHeadByRefinement h k coarse fine tail refinement =
  cong
    (λ head → head +q finiteOrderedSimpleIntegral h k tail)
    (integrandRefinement refinement)

finiteQuaternionSimpleDuhamelLevel : ProofLevel
finiteQuaternionSimpleDuhamelLevel = machineChecked

finiteQuaternionSimpleRefinementLevel : ProofLevel
finiteQuaternionSimpleRefinementLevel = machineChecked

bochnerSimpleCompletionAndDifferentiationLevel : ProofLevel
bochnerSimpleCompletionAndDifferentiationLevel = conditional
