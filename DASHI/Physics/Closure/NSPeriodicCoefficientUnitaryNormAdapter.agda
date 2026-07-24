module DASHI.Physics.Closure.NSPeriodicCoefficientUnitaryNormAdapter where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation as Potential
import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion as Leaves
import DASHI.Physics.Closure.NSCompactGammaConcreteBernsteinEnvelopeDomain as Bernstein
import DASHI.Physics.Closure.NSPeriodicOfficialNormIdentification as Official
import DASHI.Physics.Closure.NSPeriodicOfficialNormBernsteinAdapter as Adapter
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact Parseval constructor for the frozen coefficient-unitary convention.
--
-- The physical L2 quantities in this convention are represented by the same
-- coefficient-space quantities.  Hence global and shell Parseval are
-- definitional equalities, not additional analytic assumptions.  Leray and
-- Biot-Savart operator estimates remain explicit and cutoff-uniform.
------------------------------------------------------------------------

record CoefficientUnitaryNormInputs
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

    lerayProjectionBounded : ∀ τ state →
      _≤_ A (lerayOutputL2 τ state) (lerayInputL2 τ state)

    biotSavartBounded : ∀ τ state →
      _≤_ A
        (biotSavartVelocityH1 τ state)
        (biotSavartVorticityL2 τ state)

    CutoffUniform : Set t
    cutoffUniform : CutoffUniform

open CoefficientUnitaryNormInputs public

coefficientUnitaryToBernsteinAdapterInputs :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  CoefficientUnitaryNormInputs A C R F →
  Adapter.OfficialNormBernsteinAdapterInputs A C R F
coefficientUnitaryToBernsteinAdapterInputs I = record
  { bernstein = bernstein I
  ; coefficientL2 = coefficientUnitaryL2 I
  ; physicalL2 = coefficientUnitaryL2 I
  ; hSobolevNorm = hSobolevNorm I
  ; shellCoefficientL2 = coefficientUnitaryShellL2 I
  ; shellPhysicalL2 = coefficientUnitaryShellL2 I
  ; lerayInputL2 = lerayInputL2 I
  ; lerayOutputL2 = lerayOutputL2 I
  ; biotSavartVorticityL2 = biotSavartVorticityL2 I
  ; biotSavartVelocityH1 = biotSavartVelocityH1 I
  ; parsevalPlancherel = λ τ state → refl
  ; shellParsevalPlancherel = λ τ shell state → refl
  ; lerayProjectionBounded = lerayProjectionBounded I
  ; biotSavartBounded = biotSavartBounded I
  ; CutoffUniform = CutoffUniform I
  ; cutoffUniform = cutoffUniform I
  }

coefficientUnitaryOfficialNormIdentification :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : CoefficientUnitaryNormInputs A C R F) →
  Official.OfficialPeriodicNormIdentification
    A Time Nat (Bernstein.ShellState (bernstein I))
coefficientUnitaryOfficialNormIdentification I =
  Adapter.concreteBernsteinToOfficialNormIdentification
    (coefficientUnitaryToBernsteinAdapterInputs I)

coefficientUnitaryGlobalParseval :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : CoefficientUnitaryNormInputs A C R F) →
  ∀ τ state →
  Official.coefficientL2 (coefficientUnitaryOfficialNormIdentification I) τ state
  ≡ Official.physicalL2 (coefficientUnitaryOfficialNormIdentification I) τ state
coefficientUnitaryGlobalParseval I τ state = refl

coefficientUnitaryShellParseval :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : CoefficientUnitaryNormInputs A C R F) →
  ∀ τ shell state →
  Official.shellCoefficientL2
    (coefficientUnitaryOfficialNormIdentification I) τ shell state
  ≡ Official.shellPhysicalL2
    (coefficientUnitaryOfficialNormIdentification I) τ shell state
coefficientUnitaryShellParseval I τ shell state = refl

------------------------------------------------------------------------
-- Status: Parseval and shell Parseval are closed for the frozen convention.
-- The remaining official-carrier analytic leaves are the actual Leray and
-- Biot-Savart bounds and their cutoff-uniform realization.
------------------------------------------------------------------------

coefficientUnitaryNormAdapterLevel : ProofLevel
coefficientUnitaryNormAdapterLevel = machineChecked
