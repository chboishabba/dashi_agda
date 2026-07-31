module DASHI.Physics.YangMills.BalabanClayGate4CMP109GroupAverageImplicitDerivativeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Implicit differential of the CMP109/Federbush group average.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Equation (0.10) characterizes the group average V=M({U_j}) by
--
--   F(U,V) = sum_j (1/i) log(U_j V^{-1}) = 0.
--
-- Differentiating gives
--
--   D_U F[h] + D_V F[D M(h)] = 0.
--
-- If D_V F is invertible, the derivative is therefore
--
--   D M(h) = (D_V F)^{-1}(-D_U F[h]).
--
-- This module proves that formula and its uniqueness in a purely finite
-- algebra.  The physical work is reduced to identifying the two differentials
-- and proving the centre differential invertible on the selected small ball.
------------------------------------------------------------------------

record AdditiveCancellation (Residual : Set) : Set₁ where
  field
    zero : Residual
    add : Residual → Residual → Residual
    negate : Residual → Residual

    addRightInverse : ∀ value → add value (negate value) ≡ zero
    solveRightFromZero : ∀ left right →
      add left right ≡ zero → right ≡ negate left

open AdditiveCancellation public

record FederbushImplicitDifferential
    (InputTangent CentreTangent Residual : Set) : Set₁ where
  field
    cancellation : AdditiveCancellation Residual

    inputDifferential : InputTangent → Residual
    centreDifferential : CentreTangent → Residual
    inverseCentreDifferential : Residual → CentreTangent

    inverseAfterCentre : ∀ tangent →
      inverseCentreDifferential (centreDifferential tangent) ≡ tangent

    centreAfterInverse : ∀ residual →
      centreDifferential (inverseCentreDifferential residual) ≡ residual

open FederbushImplicitDifferential public

implicitAverageDerivative :
  ∀ {InputTangent CentreTangent Residual} →
  FederbushImplicitDifferential InputTangent CentreTangent Residual →
  InputTangent → CentreTangent
implicitAverageDerivative dataSet input =
  inverseCentreDifferential dataSet
    (negate (cancellation dataSet) (inputDifferential dataSet input))

implicitDerivativeSolvesLinearizedFederbushEquation :
  ∀ {InputTangent CentreTangent Residual}
    (dataSet : FederbushImplicitDifferential
      InputTangent CentreTangent Residual)
    input →
  add (cancellation dataSet)
    (inputDifferential dataSet input)
    (centreDifferential dataSet
      (implicitAverageDerivative dataSet input))
  ≡ zero (cancellation dataSet)
implicitDerivativeSolvesLinearizedFederbushEquation dataSet input =
  trans
    (cong
      (add (cancellation dataSet)
        (inputDifferential dataSet input))
      (centreAfterInverse dataSet
        (negate (cancellation dataSet)
          (inputDifferential dataSet input))))
    (addRightInverse (cancellation dataSet)
      (inputDifferential dataSet input))

implicitDerivativeUnique :
  ∀ {InputTangent CentreTangent Residual}
    (dataSet : FederbushImplicitDifferential
      InputTangent CentreTangent Residual)
    input candidate →
  add (cancellation dataSet)
    (inputDifferential dataSet input)
    (centreDifferential dataSet candidate)
  ≡ zero (cancellation dataSet) →
  candidate ≡ implicitAverageDerivative dataSet input
implicitDerivativeUnique dataSet input candidate linearizedEquation =
  trans
    (sym (inverseAfterCentre dataSet candidate))
    (cong (inverseCentreDifferential dataSet)
      (solveRightFromZero (cancellation dataSet)
        (inputDifferential dataSet input)
        (centreDifferential dataSet candidate)
        linearizedEquation))

record PhysicalFederbushAverageDerivative
    (InputTangent CentreTangent Residual : Set) : Set₁ where
  field
    implicitData : FederbushImplicitDifferential
      InputTangent CentreTangent Residual

    physicalDerivative : InputTangent → CentreTangent

    differentiatedFederbushEquation : ∀ input →
      add (cancellation implicitData)
        (inputDifferential implicitData input)
        (centreDifferential implicitData (physicalDerivative input))
      ≡ zero (cancellation implicitData)

open PhysicalFederbushAverageDerivative public

physicalAverageDerivativeEqualsImplicitFormula :
  ∀ {InputTangent CentreTangent Residual}
    (meaning : PhysicalFederbushAverageDerivative
      InputTangent CentreTangent Residual)
    input →
  physicalDerivative meaning input
  ≡ implicitAverageDerivative (implicitData meaning) input
physicalAverageDerivativeEqualsImplicitFormula meaning input =
  implicitDerivativeUnique
    (implicitData meaning)
    input
    (physicalDerivative meaning input)
    (differentiatedFederbushEquation meaning input)

cmp109FederbushImplicitDerivativeFormulaLevel : ProofLevel
cmp109FederbushImplicitDerivativeFormulaLevel = machineChecked

cmp109FederbushImplicitDerivativeUniquenessLevel : ProofLevel
cmp109FederbushImplicitDerivativeUniquenessLevel = machineChecked

physicalCMP109FederbushDifferentialIdentificationInputsLevel : ProofLevel
physicalCMP109FederbushDifferentialIdentificationInputsLevel = conditional

physicalCMP109FederbushCentreInvertibilityInputsLevel : ProofLevel
physicalCMP109FederbushCentreInvertibilityInputsLevel = conditional
