module DASHI.Physics.Closure.NSTriadKNConcreteProfileCrossWeightedSchurTheorem where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_≤_; _*_)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNConcreteWeightedFiberFolds as Folds
import DASHI.Physics.Closure.NSTriadKNConcreteWeightedSchurDecay as Decay
import DASHI.Physics.Closure.NSTriadKNBipartiteWeightedSchurWitness as Schur

------------------------------------------------------------------------
-- Exact Stage-3 target package.
--
-- This is deliberately a target, not a receipt.  In particular, the source
-- and target weights are functions on the concrete finite/tail indices, and
-- the residual and physical-operator bridges remain explicit inputs.  Thus
-- the package cannot be inhabited by the old unit-weight proxy alone.
------------------------------------------------------------------------

record ConcreteProfileCrossWeightedSchurTheorem (N : Nat) : Set₁ where
  constructor mkConcreteProfileCrossWeightedSchurTheorem
  field
    weightedDecay : Decay.ConcreteWeightedSchurDecayObligation N

    sourceWeight :
      Relation.ConcreteNonResidualFiniteIndex N -> Nat

    targetWeight :
      Relation.ConcreteNonResidualTailIndex N -> Nat

    weightedRowBound :
      (f : Relation.ConcreteNonResidualFiniteIndex N) ->
      Folds.weightedConcreteRowSum targetWeight f
        ≤ Decay.ConcreteWeightedSchurDecayObligation.rowConstant
            weightedDecay
          * sourceWeight f

    weightedColumnBound :
      (t : Relation.ConcreteNonResidualTailIndex N) ->
      Folds.weightedConcreteColumnSum sourceWeight t
        ≤ Decay.ConcreteWeightedSchurDecayObligation.columnConstant
            weightedDecay
          * targetWeight t

    weightedProductBound :
      Decay.ConcreteWeightedSchurDecayObligation.rowConstant weightedDecay
        * Decay.ConcreteWeightedSchurDecayObligation.columnConstant weightedDecay
        ≤ (suc N) * (suc N)

    bipartiteSchurWitness :
      Schur.BipartiteWeightedSchurProductBoundWitness
        (Decay.ConcreteWeightedSchurDecayObligation.rowConstant weightedDecay)
        (Decay.ConcreteWeightedSchurDecayObligation.columnConstant weightedDecay)
        ((suc N) * (suc N))

    residualRowDomination : Set
    residualColumnDomination : Set
    residualWeightedProduct : Set

    exactRepeatedPairOperatorIdentity : Set

------------------------------------------------------------------------
-- The concrete weighted-decay package supplies the finite weighted folds and
-- product arithmetic.  The four final fields above remain the actual analytic
-- obligations: residual domination and identification with the physical
-- repeated-pair operator are not inferred from count-only data.
------------------------------------------------------------------------

concreteProfileCrossWeightedSchurFromDecay :
  {N : Nat} ->
  (weightedDecay : Decay.ConcreteWeightedSchurDecayObligation N) ->
  (residualRowDomination : Set) ->
  (residualColumnDomination : Set) ->
  (residualWeightedProduct : Set) ->
  (exactRepeatedPairOperatorIdentity : Set) ->
  ConcreteProfileCrossWeightedSchurTheorem N
concreteProfileCrossWeightedSchurFromDecay
  weightedDecay residualRowDomination residualColumnDomination
  residualWeightedProduct exactRepeatedPairOperatorIdentity =
  mkConcreteProfileCrossWeightedSchurTheorem
    weightedDecay
    (Decay.ConcreteWeightedSchurDecayObligation.sourceWeight weightedDecay)
    (Decay.ConcreteWeightedSchurDecayObligation.targetWeight weightedDecay)
    (Decay.ConcreteWeightedSchurDecayObligation.weightedRowDecay weightedDecay)
    (Decay.ConcreteWeightedSchurDecayObligation.weightedColumnDecay weightedDecay)
    (Decay.ConcreteWeightedSchurDecayObligation.weightedSchurProduct weightedDecay)
    (Decay.consumeConcreteWeightedSchurDecay weightedDecay)
    residualRowDomination
    residualColumnDomination
    residualWeightedProduct
    exactRepeatedPairOperatorIdentity
  where
    -- The record fields above refer to the package being assembled.  These
    -- aliases make the dependent source/target weights explicit at the
    -- theorem boundary and avoid silently reverting to unit weights.
    sourceWeight =
      Decay.ConcreteWeightedSchurDecayObligation.sourceWeight weightedDecay
    targetWeight =
      Decay.ConcreteWeightedSchurDecayObligation.targetWeight weightedDecay

------------------------------------------------------------------------
-- Conditional budget-to-Stage-3 handoff.
--
-- This is the intended next entry point: the caller supplies the real
-- classwise ceilings and budget inequalities; all finite-fold reduction,
-- row/column decay, product arithmetic, and the bipartite Schur witness are
-- then derived constructively.  Residual domination and physical operator
-- identity remain explicit premises.
------------------------------------------------------------------------

concreteProfileCrossWeightedSchurFromBudgetPremises :
  {N : Nat} ->
  (premises : Decay.ConcreteWeightedSchurBudgetPremises N) ->
  (residualRowDomination : Set) ->
  (residualColumnDomination : Set) ->
  (residualWeightedProduct : Set) ->
  (exactRepeatedPairOperatorIdentity : Set) ->
  ConcreteProfileCrossWeightedSchurTheorem N
concreteProfileCrossWeightedSchurFromBudgetPremises
  premises residualRowDomination residualColumnDomination
  residualWeightedProduct exactRepeatedPairOperatorIdentity =
  concreteProfileCrossWeightedSchurFromDecay
    (Decay.concreteWeightedSchurDecayFromBudgets premises)
    residualRowDomination
    residualColumnDomination
    residualWeightedProduct
    exactRepeatedPairOperatorIdentity

------------------------------------------------------------------------
-- Named target propositions for the remaining non-finite work.
------------------------------------------------------------------------

ConcreteResidualRowDominationTarget : Set₁
ConcreteResidualRowDominationTarget = Set

ConcreteResidualColumnDominationTarget : Set₁
ConcreteResidualColumnDominationTarget = Set

ConcreteResidualWeightedProductTarget : Set₁
ConcreteResidualWeightedProductTarget = Set

ConcreteExactRepeatedPairOperatorIdentityTarget : Set₁
ConcreteExactRepeatedPairOperatorIdentityTarget = Set
