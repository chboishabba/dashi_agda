module DASHI.Physics.YangMills.BalabanPositiveRGDirichletGeometryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CROSS-POLLINATION
--
-- Masatoshi Fukushima, Yoichi Oshima, Masayoshi Takeda,
-- "Dirichlet Forms and Symmetric Markov Processes", second revised and
-- extended edition, De Gruyter Studies in Mathematics 19, 2010.
-- DOI: 10.1515/9783110218091.
--
-- Repository-local structural precursor:
-- DASHI.Moonshine.PositiveFiniteNeighbourSystemExact (PR #567).
-- That branch puts positive finite neighbour geometry before linearization.
-- The present module transports the SAME design rule into the Yang--Mills RG
-- lane without identifying Hecke neighbours with gauge-field RG neighbours.
--
-- DASHI CONTRIBUTION
--
-- A spectral/"Laplacian" object is not accepted merely because its matrix
-- shape looks symmetric.  Positivity is constructed first from literal
-- nonnegative local edge weights.  The derived operator preserves
-- nonnegative observables, and the associated finite rational Dirichlet
-- energy is a sum of nonnegative weighted squares.
--
-- This directly guards against the signed-Delta0 phenomenon formalized in
-- PR #558: algebraic Laplacian shape does not imply a positive Dirichlet form.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2

record PositiveRGNeighbour (State : Set) : Set where
  constructor positiveRGNeighbour
  field
    target : State
    weight : ℚ
    weightNonnegative : 0ℚ ≤ weight
open PositiveRGNeighbour public

neighbourMass : ∀ {State : Set} → List (PositiveRGNeighbour State) → ℚ
neighbourMass [] = 0ℚ
neighbourMass (edge ∷ rest) = weight edge + neighbourMass rest

positiveRGOperator :
  ∀ {State : Set} →
  List (PositiveRGNeighbour State) →
  (State → ℚ) → ℚ
positiveRGOperator [] observable = 0ℚ
positiveRGOperator (edge ∷ rest) observable =
  weight edge * observable (target edge)
  + positiveRGOperator rest observable

nonnegativeProduct :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
nonnegativeProduct {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN

      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN

      productNonnegative : NonNegative (left * right)
      productNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚP.nonNegative⁻¹ (left * right)

positiveRGOperatorPreservesNonnegative :
  ∀ {State : Set}
    (row : List (PositiveRGNeighbour State))
    (observable : State → ℚ) →
    (∀ state → 0ℚ ≤ observable state) →
    0ℚ ≤ positiveRGOperator row observable
positiveRGOperatorPreservesNonnegative [] observable observableNN =
  ℚP.≤-refl
positiveRGOperatorPreservesNonnegative
    (edge ∷ rest) observable observableNN =
  FiniteL2.addNonnegative
    (nonnegativeProduct
      (weightNonnegative edge)
      (observableNN (target edge)))
    (positiveRGOperatorPreservesNonnegative rest observable observableNN)

record PositiveRGEdgeDifference : Set where
  constructor positiveRGEdgeDifference
  field
    edgeWeight : ℚ
    edgeWeightNonnegative : 0ℚ ≤ edgeWeight
    observableDifference : ℚ
open PositiveRGEdgeDifference public

edgeDirichletEnergy : PositiveRGEdgeDifference → ℚ
edgeDirichletEnergy edge =
  edgeWeight edge
  * FiniteL2.square (observableDifference edge)

edgeDirichletEnergyNonnegative :
  ∀ edge → 0ℚ ≤ edgeDirichletEnergy edge
edgeDirichletEnergyNonnegative edge =
  nonnegativeProduct
    (edgeWeightNonnegative edge)
    (FiniteL2.squareNonnegative (observableDifference edge))

dirichletEnergy : List PositiveRGEdgeDifference → ℚ
dirichletEnergy [] = 0ℚ
dirichletEnergy (edge ∷ rest) =
  edgeDirichletEnergy edge + dirichletEnergy rest

dirichletEnergyNonnegative :
  ∀ edges → 0ℚ ≤ dirichletEnergy edges
dirichletEnergyNonnegative [] = ℚP.≤-refl
dirichletEnergyNonnegative (edge ∷ rest) =
  FiniteL2.addNonnegative
    (edgeDirichletEnergyNonnegative edge)
    (dirichletEnergyNonnegative rest)

record PositiveLocalRGGeometry (State : Set) : Set₁ where
  field
    neighbours : State → List (PositiveRGNeighbour State)
open PositiveLocalRGGeometry public

-- The positivity theorem is local and unconditional once literal nonnegative
-- neighbours have been constructed.  What remains physical is to derive these
-- neighbours/weights from the SAME Bałaban block-RG transformation rather than
-- supplying an unrelated stochastic chain.
positiveRGDirichletGeometryLevel : ProofLevel
positiveRGDirichletGeometryLevel = machineChecked

literalBalabanPositiveNeighbourProducerLevel : ProofLevel
literalBalabanPositiveNeighbourProducerLevel = conditional

-- Fukushima--Oshima--Takeda is cited for the mature analytic correspondence
-- between regular Dirichlet forms and symmetric Markov processes.  We do not
-- identify this finite rational construction with the continuum Hunt process
-- without the missing closability/regularity/limit theorems.
dirichletFormToSymmetricMarkovProcessLevel : ProofLevel
dirichletFormToSymmetricMarkovProcessLevel = standardImported

continuumDirichletFormIdentificationLevel : ProofLevel
continuumDirichletFormIdentificationLevel = conditional
