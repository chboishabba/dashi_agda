module DASHI.Physics.YangMills.YangMillsExtensivePotentialGlobalOscillationNoGoExact where

------------------------------------------------------------------------
-- ROUND69: GLOBAL HOLLEY--STROOCK OSCILLATION IS EXTENSIVE
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Richard Holley and Daniel Stroock,
-- "Logarithmic Sobolev Inequalities and Stochastic Ising Models",
-- Journal of Statistical Physics 46 (1987), 1159--1194.
-- DOI: 10.1007/BF01011161.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- A naive attempt to make L5 downstream of L7 by proving a volume-uniform
-- global oscillation bound for the COMPLETE effective action is structurally
-- wrong for an extensive lattice theory.
--
-- If m independently switchable local blocks each change the local potential
-- by delta, then changing all blocks simultaneously changes the additive
-- potential by exactly m*delta.  Hence any global oscillation bound Omega_m
-- satisfies
--
--      m delta <= Omega_m.
--
-- For delta>0 this cannot remain bounded as m grows.  Therefore a useful
-- Holley--Stroock/multiscale route must perturb around a reference measure with
-- a LOCAL interaction norm, blockwise oscillation, Dobrushin matrix, Hessian
-- bound, or another tensorizing/multiscale quantity.  It cannot use
-- osc(total extensive Wilson/effective action) as a volume-uniform scalar.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record IndependentAdditivePotentialFamily : Set₁ where
  field
    localOscillation : ℚ
    localOscillationPositive : 0ℚ < localOscillation

    totalDifference : Nat → ℚ
    totalDifferenceZero : totalDifference zero ≡ 0ℚ
    addOneIndependentBlock : ∀ n →
      totalDifference (suc n) ≡ totalDifference n + localOscillation

open IndependentAdditivePotentialFamily public

additiveDifferenceExact :
  (dataSet : IndependentAdditivePotentialFamily) → ∀ n →
  totalDifference dataSet n
  ≡ Sums.natAsRational n * localOscillation dataSet
additiveDifferenceExact dataSet zero =
  subst
    (λ left → left ≡ Sums.natAsRational zero * localOscillation dataSet)
    (sym (totalDifferenceZero dataSet))
    (ℚRing.solve-∀ (localOscillation dataSet))
additiveDifferenceExact dataSet (suc n)
  rewrite addOneIndependentBlock dataSet n
        | additiveDifferenceExact dataSet n =
  ℚRing.solve-∀ (Sums.natAsRational n) (localOscillation dataSet)

record GlobalOscillationMajorant
    (dataSet : IndependentAdditivePotentialFamily) : Set₁ where
  field
    oscillationUpper : Nat → ℚ
    switchedEndpointsBelowOscillation : ∀ n →
      totalDifference dataSet n ≤ oscillationUpper n
open GlobalOscillationMajorant public

globalOscillationAtLeastLinear :
  ∀ {dataSet}
    (majorant : GlobalOscillationMajorant dataSet) → ∀ n →
  Sums.natAsRational n * localOscillation dataSet
  ≤ oscillationUpper majorant n
globalOscillationAtLeastLinear {dataSet} majorant n =
  subst
    (λ left → left ≤ oscillationUpper majorant n)
    (additiveDifferenceExact dataSet n)
    (switchedEndpointsBelowOscillation majorant n)

oneMoreBlockStrictlyRaisesExactDifference :
  (dataSet : IndependentAdditivePotentialFamily) → ∀ n →
  totalDifference dataSet n < totalDifference dataSet (suc n)
oneMoreBlockStrictlyRaisesExactDifference dataSet n =
  subst
    (λ right → totalDifference dataSet n < right)
    (sym (addOneIndependentBlock dataSet n))
    (ℚP.+-monoʳ-< (totalDifference dataSet n)
      (localOscillationPositive dataSet))

extensiveGlobalOscillationNoGoLevel : ProofLevel
extensiveGlobalOscillationNoGoLevel = machineChecked

-- Physical Yang--Mills instantiation: select a family of edge-disjoint or
-- otherwise independently switchable local plaquette/block excitations with a
-- common positive local action difference.  Once constructed, the theorem
-- above rules out a volume-uniform scalar osc(total action) strategy.
physicalIndependentWilsonBlockFamilyLevel : ProofLevel
physicalIndependentWilsonBlockFamilyLevel = conditional
