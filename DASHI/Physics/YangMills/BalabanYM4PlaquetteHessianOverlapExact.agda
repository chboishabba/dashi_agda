module DASHI.Physics.YangMills.BalabanYM4PlaquetteHessianOverlapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- RG1c needs no global 342732-dimensional Hessian norm estimate.  If the
-- Hessian is a sum of local plaquette forms, each local variation costs at
-- most L*r times its local energy, and the local energies overlap globally by
-- at most N, then
--
--       sum_p deltaH_p <= (L*r*N) ||h||^2.
--
-- This is the precise bounded-overlap bridge consumed by the existing
-- 1/32 -> 1/64 coercivity perturbation theorem.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record PlaquetteOverlapBudget (Plaquette : Set) (plaquettes : List Plaquette) : Set₁ where
  field
    localVariation localEnergy : Plaquette → ℚ
    localLipschitz backgroundRadius overlap globalEnergy : ℚ

    localFactorNonnegative : 0ℚ ≤ localLipschitz * backgroundRadius

    localVariationBound : ∀ plaquette →
      localVariation plaquette
      ≤ (localLipschitz * backgroundRadius) * localEnergy plaquette

    energyOverlap :
      Sums.sumRational plaquettes localEnergy
      ≤ overlap * globalEnergy

open PlaquetteOverlapBudget public

plaquetteOverlapVariationBound :
  ∀ {Plaquette plaquettes}
    (dataSet : PlaquetteOverlapBudget Plaquette plaquettes) →
  Sums.sumRational plaquettes (localVariation dataSet)
  ≤ (((localLipschitz dataSet * backgroundRadius dataSet)
      * overlap dataSet) * globalEnergy dataSet)
plaquetteOverlapVariationBound {plaquettes = plaquettes} dataSet =
  let
    localSum :
      Sums.sumRational plaquettes (localVariation dataSet)
      ≤ Sums.sumRational plaquettes
          (λ p → (localLipschitz dataSet * backgroundRadius dataSet)
            * localEnergy dataSet p)
    localSum = Schur.sumPointwiseBelow plaquettes _ _
      (localVariationBound dataSet)

    scaledSum :
      Sums.sumRational plaquettes (localVariation dataSet)
      ≤ (localLipschitz dataSet * backgroundRadius dataSet)
          * Sums.sumRational plaquettes (localEnergy dataSet)
    scaledSum = subst
      (λ upper → Sums.sumRational plaquettes (localVariation dataSet) ≤ upper)
      (Sums.sumRationalScale
        (localLipschitz dataSet * backgroundRadius dataSet)
        plaquettes (localEnergy dataSet))
      localSum

    overlapScaled :
      (localLipschitz dataSet * backgroundRadius dataSet)
        * Sums.sumRational plaquettes (localEnergy dataSet)
      ≤ (localLipschitz dataSet * backgroundRadius dataSet)
        * (overlap dataSet * globalEnergy dataSet)
    overlapScaled = Norm.scaleNonnegative
      (localLipschitz dataSet * backgroundRadius dataSet)
      (localFactorNonnegative dataSet)
      (energyOverlap dataSet)

    chained = ℚP.≤-trans scaledSum overlapScaled
  in
  subst
    (λ upper → Sums.sumRational plaquettes (localVariation dataSet) ≤ upper)
    (ℚRing.solve-∀
      (localLipschitz dataSet) (backgroundRadius dataSet)
      (overlap dataSet) (globalEnergy dataSet))
    chained

ym4PlaquetteHessianOverlapLevel : ProofLevel
ym4PlaquetteHessianOverlapLevel = machineChecked
