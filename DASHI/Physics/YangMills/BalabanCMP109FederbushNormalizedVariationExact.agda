module DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedVariationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Lift the exact local variation of K_j = J_j T_j through the normalized
-- Federbush average.  Normalization is used before any dimension count:
--
--   Abar(U) = w sum_j K_j(U),       w |J| = 1,
--
-- so
--
--   Abar(U)-Abar(V) = w sum_j [K_j(U)-K_j(V)]
--
-- exactly, and a uniform local column-mass modulus is preserved with no factor
-- of |J|.  Combined with the component telescope this yields the concrete
-- budget
--
--   col(Abar(U)-Abar(V))
--      <= L_J C_T + C_J L_T
--
-- whenever the four displayed local budgets hold.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanFiniteNormalizedKernelSchurExact as Normalized
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationMassExact as VariationMass

componentJacobian :
  ∀ {Index : Set} →
  (Index → Jacobian.Lie3Matrix) →
  (Index → Jacobian.Lie3Matrix) →
  Index → Jacobian.Lie3Matrix
componentJacobian jacobian transport index =
  Component.matrixCompose (jacobian index) (transport index)

normalizedComponentJacobian :
  ∀ {Index : Set} →
  ℚ → List Index →
  (Index → Jacobian.Lie3Matrix) →
  (Index → Jacobian.Lie3Matrix) →
  Jacobian.Lie3Matrix
normalizedComponentJacobian weight indices jacobian transport =
  Normalized.normalizedKernel weight indices
    (componentJacobian jacobian transport)

localComponentVariation :
  ∀ {Index : Set} →
  (Index → Jacobian.Lie3Matrix) →
  (Index → Jacobian.Lie3Matrix) →
  (Index → Jacobian.Lie3Matrix) →
  (Index → Jacobian.Lie3Matrix) →
  Index → Jacobian.Lie3Matrix
localComponentVariation jacobianU transportU jacobianV transportV index =
  Variation.matrixDifference
    (Component.matrixCompose (jacobianU index) (transportU index))
    (Component.matrixCompose (jacobianV index) (transportV index))

normalizedComponentVariation :
  ∀ {Index : Set} →
  ℚ → List Index →
  (Index → Jacobian.Lie3Matrix) →
  (Index → Jacobian.Lie3Matrix) →
  (Index → Jacobian.Lie3Matrix) →
  (Index → Jacobian.Lie3Matrix) →
  Jacobian.Lie3Matrix
normalizedComponentVariation weight indices
    jacobianU transportU jacobianV transportV =
  Normalized.normalizedKernel weight indices
    (localComponentVariation jacobianU transportU jacobianV transportV)

normalizedComponentJacobianDifferenceExact :
  ∀ {Index} weight (indices : List Index)
    jacobianU transportU jacobianV transportV row column →
  Variation.matrixDifference
    (normalizedComponentJacobian weight indices jacobianU transportU)
    (normalizedComponentJacobian weight indices jacobianV transportV)
    row column
  ≡ normalizedComponentVariation weight indices
      jacobianU transportU jacobianV transportV row column
normalizedComponentJacobianDifferenceExact
    weight indices jacobianU transportU jacobianV transportV row column
  rewrite Variation.sumRationalSub indices
    (λ index → Component.matrixCompose
      (jacobianU index) (transportU index) row column)
    (λ index → Component.matrixCompose
      (jacobianV index) (transportV index) row column) =
  ℚRing.solve-∀
    weight
    (Sums.sumRational indices
      (λ index → Component.matrixCompose
        (jacobianU index) (transportU index) row column))
    (Sums.sumRational indices
      (λ index → Component.matrixCompose
        (jacobianV index) (transportV index) row column))

record NormalizedFederbushVariationData (Index : Set) : Set₁ where
  field
    indices : List Index
    weight : ℚ
    weightNonnegative : 0ℚ ≤ weight
    normalizedWeight :
      weight * Fibre.natAsRational (length indices) ≡ 1ℚ

    jacobianU transportU jacobianV transportV :
      Index → Jacobian.Lie3Matrix

    jacobianVariationBound transportNormBound : ℚ
    jacobianNormBound transportVariationBound : ℚ

    jacobianVariationNonnegative : 0ℚ ≤ jacobianVariationBound
    jacobianNormNonnegative : 0ℚ ≤ jacobianNormBound

    jacobianVariationColumns : ∀ index selected →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Variation.matrixDifference (jacobianU index) (jacobianV index)) selected
      ≤ jacobianVariationBound

    transportColumns : ∀ index column →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (transportU index) column
      ≤ transportNormBound

    jacobianColumns : ∀ index selected →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (jacobianV index) selected
      ≤ jacobianNormBound

    transportVariationColumns : ∀ index column →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Variation.matrixDifference (transportU index) (transportV index)) column
      ≤ transportVariationBound

open NormalizedFederbushVariationData public

federbushVariationBudget : ∀ {Index} → NormalizedFederbushVariationData Index → ℚ
federbushVariationBudget dataSet =
  jacobianVariationBound dataSet * transportNormBound dataSet
  + jacobianNormBound dataSet * transportVariationBound dataSet

localComponentVariationColumnBound :
  ∀ {Index} (dataSet : NormalizedFederbushVariationData Index) index column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (localComponentVariation
      (jacobianU dataSet) (transportU dataSet)
      (jacobianV dataSet) (transportV dataSet) index) column
  ≤ federbushVariationBudget dataSet
localComponentVariationColumnBound dataSet index column =
  VariationMass.componentVariationColumnMassBound
    (jacobianU dataSet index) (transportU dataSet index)
    (jacobianV dataSet index) (transportV dataSet index)
    (jacobianVariationBound dataSet) (transportNormBound dataSet)
    (jacobianNormBound dataSet) (transportVariationBound dataSet)
    column
    (jacobianVariationNonnegative dataSet)
    (jacobianNormNonnegative dataSet)
    (jacobianVariationColumns dataSet index)
    (transportColumns dataSet index column)
    (jacobianColumns dataSet index)
    (transportVariationColumns dataSet index column)

normalizedFederbushVariationColumnBound :
  ∀ {Index} (dataSet : NormalizedFederbushVariationData Index) column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (normalizedComponentVariation
      (weight dataSet) (indices dataSet)
      (jacobianU dataSet) (transportU dataSet)
      (jacobianV dataSet) (transportV dataSet)) column
  ≤ federbushVariationBudget dataSet
normalizedFederbushVariationColumnBound dataSet column =
  Normalized.normalizedKernelColumnMassBound
    (weight dataSet) (indices dataSet)
    Physical.lieCoordinates3 Physical.lieCoordinates3
    (localComponentVariation
      (jacobianU dataSet) (transportU dataSet)
      (jacobianV dataSet) (transportV dataSet))
    (federbushVariationBudget dataSet) column
    (weightNonnegative dataSet)
    (normalizedWeight dataSet)
    (λ index → localComponentVariationColumnBound dataSet index column)

normalizedFederbushJacobianDifferenceColumnBound :
  ∀ {Index} (dataSet : NormalizedFederbushVariationData Index) column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference
      (normalizedComponentJacobian
        (weight dataSet) (indices dataSet)
        (jacobianU dataSet) (transportU dataSet))
      (normalizedComponentJacobian
        (weight dataSet) (indices dataSet)
        (jacobianV dataSet) (transportV dataSet))) column
  ≤ federbushVariationBudget dataSet
normalizedFederbushJacobianDifferenceColumnBound dataSet column =
  let
    leftMatrix = Variation.matrixDifference
      (normalizedComponentJacobian
        (weight dataSet) (indices dataSet)
        (jacobianU dataSet) (transportU dataSet))
      (normalizedComponentJacobian
        (weight dataSet) (indices dataSet)
        (jacobianV dataSet) (transportV dataSet))
    rightMatrix = normalizedComponentVariation
      (weight dataSet) (indices dataSet)
      (jacobianU dataSet) (transportU dataSet)
      (jacobianV dataSet) (transportV dataSet)
    massExact :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        leftMatrix column
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        rightMatrix column
    massExact =
      Sums.sumRationalCong Physical.lieCoordinates3 _ _
        (λ row →
          cong ∣_∣
            (normalizedComponentJacobianDifferenceExact
              (weight dataSet) (indices dataSet)
              (jacobianU dataSet) (transportU dataSet)
              (jacobianV dataSet) (transportV dataSet)
              row column))
  in
  subst
    (λ lower → lower ≤ federbushVariationBudget dataSet)
    (sym massExact)
    (normalizedFederbushVariationColumnBound dataSet column)

cmp109FederbushNormalizedVariationExactLevel : ProofLevel
cmp109FederbushNormalizedVariationExactLevel = machineChecked

cmp109FederbushNormalizedVariationMassLevel : ProofLevel
cmp109FederbushNormalizedVariationMassLevel = machineChecked
