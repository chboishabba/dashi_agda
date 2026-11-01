module DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationMassExact where

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
-- Project the exact two-background identity
--
--   J_U T_U - J_V T_V
--     = (J_U-J_V)T_U + J_V(T_U-T_V)
--
-- into the same finite l1 column mass used by the determinant-free Federbush
-- reopening.  If the two difference factors have bounds L_J d and L_T d and
-- the undifferenced factors have masses C_T and C_J, the component variation
-- is bounded by
--
--   (L_J C_T + C_J L_T) d.
--
-- This is the local quantitative bridge needed before normalized averaging.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation
import DASHI.Physics.YangMills.BalabanCMP109FederbushResidualMassTelescopeExact as Mass

variationColumnTriangle :
  ∀ jacobianU transportU jacobianV transportV column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference
      (Component.matrixCompose jacobianU transportU)
      (Component.matrixCompose jacobianV transportV)) column
  ≤ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.matrixCompose
        (Variation.matrixDifference jacobianU jacobianV) transportU) column
    + RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.matrixCompose jacobianV
        (Variation.matrixDifference transportU transportV)) column
variationColumnTriangle jacobianU transportU jacobianV transportV column =
  Schur.sumPointwiseBelow Physical.lieCoordinates3 _ _
    (λ row →
      subst
        (λ value →
          ∣ value ∣
          ≤ ∣ Component.matrixCompose
                (Variation.matrixDifference jacobianU jacobianV)
                transportU row column ∣
            + ∣ Component.matrixCompose jacobianV
                (Variation.matrixDifference transportU transportV)
                row column ∣)
        (Variation.componentProductVariationExact
          jacobianU transportU jacobianV transportV row column)
        (ℚP.∣p+q∣≤∣p∣+∣q∣
          (Component.matrixCompose
            (Variation.matrixDifference jacobianU jacobianV)
            transportU row column)
          (Component.matrixCompose jacobianV
            (Variation.matrixDifference transportU transportV)
            row column)))

componentVariationColumnMassBound :
  ∀ jacobianU transportU jacobianV transportV
    jacobianVariationBound transportNormBound
    jacobianNormBound transportVariationBound column →
  0ℚ ≤ jacobianVariationBound →
  0ℚ ≤ jacobianNormBound →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Variation.matrixDifference jacobianU jacobianV) selected
    ≤ jacobianVariationBound) →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 transportU column
    ≤ transportNormBound →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 jacobianV selected
    ≤ jacobianNormBound) →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Variation.matrixDifference transportU transportV) column
    ≤ transportVariationBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference
      (Component.matrixCompose jacobianU transportU)
      (Component.matrixCompose jacobianV transportV)) column
  ≤ jacobianVariationBound * transportNormBound
    + jacobianNormBound * transportVariationBound
componentVariationColumnMassBound
    jacobianU transportU jacobianV transportV
    jacobianVariationBound transportNormBound
    jacobianNormBound transportVariationBound column
    jacobianVariationNonnegative jacobianNormNonnegative
    jacobianVariationColumns transportColumn
    jacobianColumns transportVariationColumn =
  ℚP.≤-trans
    (variationColumnTriangle
      jacobianU transportU jacobianV transportV column)
    (ℚP.+-mono-≤
      (Mass.composeColumnMassBound
        (Variation.matrixDifference jacobianU jacobianV)
        transportU
        jacobianVariationBound transportNormBound column
        jacobianVariationNonnegative
        jacobianVariationColumns transportColumn)
      (Mass.composeColumnMassBound
        jacobianV
        (Variation.matrixDifference transportU transportV)
        jacobianNormBound transportVariationBound column
        jacobianNormNonnegative
        jacobianColumns transportVariationColumn))

cmp109FederbushComponentVariationMassLevel : ProofLevel
cmp109FederbushComponentVariationMassLevel = machineChecked
