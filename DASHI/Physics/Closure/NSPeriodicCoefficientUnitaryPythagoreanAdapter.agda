module DASHI.Physics.Closure.NSPeriodicCoefficientUnitaryPythagoreanAdapter where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation as Potential
import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion as Leaves
import DASHI.Physics.Closure.NSCompactGammaConcreteBernsteinEnvelopeDomain as Bernstein
import DASHI.Physics.Closure.NSPeriodicCoefficientUnitaryNormAdapter as Unitary
import DASHI.Physics.Closure.NSPeriodicLerayBiotSavartNormReduction as Pythagorean
import DASHI.Physics.Closure.NSPeriodicOfficialNormIdentification as Official
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact constructor for the official coefficient-unitary norm package from
-- the Leray and Biot-Savart Pythagorean identities.
--
-- This removes the two free operator inequalities from the coefficient-unitary
-- adapter.  An inhabitant supplies the literal norm quantities and one
-- Pythagorean decomposition at each selected state; contractivity follows.
------------------------------------------------------------------------

record CoefficientUnitaryPythagoreanInputs
    {t : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t}
    (C : Potential.ThreeWayAdditiveCalculus A)
    (R : Leaves.ConcreteReserveLeaves A Time)
    (F : Leaves.RealFundamentalTheoremRealization A C R) : Set (lsuc t) where
  field
    bernstein : Bernstein.ConcreteBernsteinEnvelopeLeaves A C R F

    coefficientUnitaryL2 hSobolevNorm :
      Time → Bernstein.ShellState bernstein → Scalar A

    coefficientUnitaryShellL2 :
      Time → Nat → Bernstein.ShellState bernstein → Scalar A

    lerayInputL2 lerayOutputL2 :
      Time → Bernstein.ShellState bernstein → Scalar A

    biotSavartVorticityL2 biotSavartVelocityH1 :
      Time → Bernstein.ShellState bernstein → Scalar A

    normDecomposition : ∀ τ state →
      Pythagorean.PeriodicLerayBiotSavartNormInputs A

    lerayInputMeaning : ∀ τ state →
      Pythagorean.lerayInputNormSquared (normDecomposition τ state)
      ≡ lerayInputL2 τ state

    lerayOutputMeaning : ∀ τ state →
      Pythagorean.lerayOutputNormSquared (normDecomposition τ state)
      ≡ lerayOutputL2 τ state

    biotSavartVorticityMeaning : ∀ τ state →
      Pythagorean.vorticityNormSquared (normDecomposition τ state)
      ≡ biotSavartVorticityL2 τ state

    biotSavartVelocityMeaning : ∀ τ state →
      Pythagorean.biotSavartHomogeneousH1Squared
        (normDecomposition τ state)
      ≡ biotSavartVelocityH1 τ state

    CutoffUniform : Set t
    cutoffUniform : CutoffUniform

open CoefficientUnitaryPythagoreanInputs public

pythagoreanLerayBound :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : CoefficientUnitaryPythagoreanInputs A C R F) →
  ∀ τ state →
  _≤_ A (lerayOutputL2 I τ state) (lerayInputL2 I τ state)
pythagoreanLerayBound {A = A} I τ state =
  subst
    (λ upper → _≤_ A (lerayOutputL2 I τ state) upper)
    (lerayInputMeaning I τ state)
    (subst
      (λ lower →
        _≤_ A lower
          (Pythagorean.lerayInputNormSquared
            (normDecomposition I τ state)))
      (lerayOutputMeaning I τ state)
      (Pythagorean.periodicLerayProjectionContractive
        (normDecomposition I τ state)))

pythagoreanBiotSavartBound :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : CoefficientUnitaryPythagoreanInputs A C R F) →
  ∀ τ state →
  _≤_ A
    (biotSavartVelocityH1 I τ state)
    (biotSavartVorticityL2 I τ state)
pythagoreanBiotSavartBound {A = A} I τ state =
  subst
    (λ upper → _≤_ A (biotSavartVelocityH1 I τ state) upper)
    (biotSavartVorticityMeaning I τ state)
    (subst
      (λ lower →
        _≤_ A lower
          (Pythagorean.vorticityNormSquared
            (normDecomposition I τ state)))
      (biotSavartVelocityMeaning I τ state)
      (Pythagorean.periodicBiotSavartHomogeneousH1Bounded
        (normDecomposition I τ state)))

coefficientUnitaryPythagoreanToNormInputs :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  CoefficientUnitaryPythagoreanInputs A C R F →
  Unitary.CoefficientUnitaryNormInputs A C R F
coefficientUnitaryPythagoreanToNormInputs I = record
  { bernstein = bernstein I
  ; coefficientUnitaryL2 = coefficientUnitaryL2 I
  ; hSobolevNorm = hSobolevNorm I
  ; coefficientUnitaryShellL2 = coefficientUnitaryShellL2 I
  ; lerayInputL2 = lerayInputL2 I
  ; lerayOutputL2 = lerayOutputL2 I
  ; biotSavartVorticityL2 = biotSavartVorticityL2 I
  ; biotSavartVelocityH1 = biotSavartVelocityH1 I
  ; lerayProjectionBounded = pythagoreanLerayBound I
  ; biotSavartBounded = pythagoreanBiotSavartBound I
  ; CutoffUniform = CutoffUniform I
  ; cutoffUniform = cutoffUniform I
  }

coefficientUnitaryPythagoreanOfficialNorms :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : CoefficientUnitaryPythagoreanInputs A C R F) →
  Official.OfficialPeriodicNormIdentification
    A Time Nat (Bernstein.ShellState (bernstein I))
coefficientUnitaryPythagoreanOfficialNorms I =
  Unitary.coefficientUnitaryOfficialNormIdentification
    (coefficientUnitaryPythagoreanToNormInputs I)

------------------------------------------------------------------------
-- Status: Parseval, Leray contractivity, and Biot-Savart Ḣ¹ boundedness are
-- now assembled from one literal norm carrier plus exact Pythagorean splits.
-- The remaining carrier leaf is the real-vector proof of those splits and its
-- cutoff-uniform finite-sum interpretation.
------------------------------------------------------------------------

coefficientUnitaryPythagoreanAdapterLevel : ProofLevel
coefficientUnitaryPythagoreanAdapterLevel = machineChecked
