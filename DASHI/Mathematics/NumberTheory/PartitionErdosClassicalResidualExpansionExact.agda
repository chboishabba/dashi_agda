module DASHI.Mathematics.NumberTheory.PartitionErdosClassicalResidualExpansionExact where

------------------------------------------------------------------------
-- ERDOS RESIDUAL WEIGHT AS A LITERAL FINITE FIBRE
--
-- For a residual triple (v,k,mu), the classical double sum contributes weight
-- v.  FiniteWeightUnitExpansionExact turns that coefficient into an explicit
-- Fin v fibre.  Hence
--
--   sum_{(v,k,mu)} v
--
-- is exactly the unit-mass fold over residual quadruples (v,k,mu,u), u : Fin v.
--
-- This closes the generic "where did the factor v come from?" step without
-- analytic generating functions and without treating v as an unexplained
-- numerical annotation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.FiniteWeightUnitExpansionExact as Expand
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition

------------------------------------------------------------------------
-- A finite list of conventional residual triples has a canonical unit-labelled
-- expansion.  Each triple receives exactly `partValue` unit witnesses.

ResidualUnit : (n : Nat) → Set
ResidualUnit n =
  Expand.UnitExpansion
    (Partition.tripleWeight {n = n})

expandResidualTriples :
  (n : Nat) →
  List (Partition.ErdosResidualTriple n) →
  List (ResidualUnit n)
expandResidualTriples n =
  Expand.expandEnumeration (Partition.tripleWeight {n = n})

classicalTripleFold :
  (n : Nat) →
  List (Partition.ErdosResidualTriple n) → Nat
classicalTripleFold n triples =
  Reindex.foldNat (Partition.tripleWeight {n = n}) triples

expandedResidualUnitFold :
  (n : Nat) →
  List (Partition.ErdosResidualTriple n) → Nat
expandedResidualUnitFold n triples =
  Reindex.foldNat
    (λ _ → 1)
    (expandResidualTriples n triples)

factorVIsUnitFibreCardinality :
  (n : Nat) →
  (triples : List (Partition.ErdosResidualTriple n)) →
  expandedResidualUnitFold n triples
  ≡ classicalTripleFold n triples
factorVIsUnitFibreCardinality n triples =
  Expand.expandedUnitFoldEqualsWeightedFold
    (Partition.tripleWeight {n = n})
    triples

------------------------------------------------------------------------
-- This theorem is the generic grouping half of the classical RHS.  A concrete
-- partition enumerator now only has to enumerate every legal (v,k,mu) triple
-- exactly once.  Expanding by Fin v automatically supplies the v coefficient.
------------------------------------------------------------------------
