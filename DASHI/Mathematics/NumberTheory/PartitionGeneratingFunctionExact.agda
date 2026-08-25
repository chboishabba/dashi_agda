module DASHI.Mathematics.NumberTheory.PartitionGeneratingFunctionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- G. H. Hardy and S. Ramanujan,
-- "Asymptotic Formulae in Combinatory Analysis",
-- Proceedings of the London Mathematical Society (2) 17 (1918), 75--115.
-- DOI: 10.1112/plms/s2-17.1.75.
--
-- The classical partition generating function is
--
--   sum_{n >= 0} p(n) q^n = product_{m >= 1} (1 - q^m)^(-1).
--
-- DASHI CONTRIBUTION
--
-- Reuse two independently constructed finite owners already in the repo:
--
--   * RankOneFockPartitionGradingExact: partition-labelled oscillator bases;
--   * RankOneFockEulerProductPrefixExact: exact truncated Euler-product
--     convolution.
--
-- Their prefixes are definitionally linked by a machine-checked equality.
-- This module promotes that equality to the NumberTheory namespace without
-- pretending that a degree-five prefix proves coefficient stabilisation for
-- every degree, convergence of the infinite product, eta modularity, or the
-- Hardy--Ramanujan asymptotic.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.RankOneFockPartitionGradingExact as Fock
import DASHI.Moonshine.RankOneFockEulerProductPrefixExact as Euler

------------------------------------------------------------------------
-- Exact finite bridge.

partitionCoefficientPrefix : List Nat
partitionCoefficientPrefix = Fock.fockCharacterPrefix

eulerProductCoefficientPrefix : List Nat
eulerProductCoefficientPrefix = Euler.coefficients Euler.productThroughFive

partitionPrefixEqualsEulerProductPrefix :
  partitionCoefficientPrefix ≡ eulerProductCoefficientPrefix
partitionPrefixEqualsEulerProductPrefix =
  Euler.fockPrefixEqualsEulerProductPrefix

partitionPrefix : List Nat
partitionPrefix = partitionCoefficientPrefix

partitionPrefixIs012357 :
  partitionPrefix ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 7 ∷ []
partitionPrefixIs012357 = Fock.refl

------------------------------------------------------------------------
-- Keep the finite theorem and infinite/analytic promotions as different
-- theorem layers.  Constructor separation prevents a finite-prefix receipt
-- from being confused with either missing promotion.

data PartitionGeneratingFunctionLayer : Set where
  finitePartitionCoefficientBridge : PartitionGeneratingFunctionLayer
  infiniteEulerProductIdentity : PartitionGeneratingFunctionLayer
  partitionAsymptoticAnalysis : PartitionGeneratingFunctionLayer

finiteBridgeIsNotInfiniteProduct :
  finitePartitionCoefficientBridge ≡ infiniteEulerProductIdentity → ⊥
finiteBridgeIsNotInfiniteProduct ()

finiteBridgeIsNotAsymptoticAnalysis :
  finitePartitionCoefficientBridge ≡ partitionAsymptoticAnalysis → ⊥
finiteBridgeIsNotAsymptoticAnalysis ()

infiniteProductIsNotAsymptoticAnalysis :
  infiniteEulerProductIdentity ≡ partitionAsymptoticAnalysis → ⊥
infiniteProductIsNotAsymptoticAnalysis ()

------------------------------------------------------------------------
-- Explicit open boundary.
--
-- A future owner may discharge these fields constructively or analytically.
-- They are obligations, not axioms imported into the finite theorem above.

record PartitionGeneratingFunctionCompletion : Set₁ where
  field
    coefficientStabilisationForEveryDegree : Set
    formalInfiniteEulerProduct : Set
    coefficientIdentityForEveryDegree : Set
    convergenceOnOpenUnitDisk : Set
    dedekindEtaIdentification : Set
    etaModularTransformation : Set

open PartitionGeneratingFunctionCompletion public
