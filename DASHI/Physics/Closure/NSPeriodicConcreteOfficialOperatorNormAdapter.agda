module DASHI.Physics.Closure.NSPeriodicConcreteOfficialOperatorNormAdapter where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier using (Vec3)
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation as Potential
import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion as Leaves
import DASHI.Physics.Closure.NSCompactGammaConcreteBernsteinEnvelopeDomain as Bernstein
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSPeriodicConcreteModeOperatorPythagorean as Concrete
import DASHI.Physics.Closure.NSPeriodicLerayBiotSavartNormReduction as Operator
import DASHI.Physics.Closure.NSPeriodicCoefficientUnitaryPythagoreanAdapter as Pythagorean
import DASHI.Physics.Closure.NSPeriodicOfficialNormIdentification as Official
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Official coefficient-unitary norm adapter with no free Leray or
-- Biot-Savart inequality fields.
--
-- The four operator norms below are the literal finite folds over the exact
-- duplicate-free cutoff cube.  Their Pythagorean decompositions are constructed
-- mode-by-mode, so cutoff uniformity is the unit witness: the operator constant
-- is exactly one for every N.
------------------------------------------------------------------------

record ConcreteOfficialOperatorNormInputs
    {t : Level}
    (O : Concrete.RealOrderCancellationAuthority)
    {Time : Set t}
    (C : Potential.ThreeWayAdditiveCalculus (Concrete.realNormArithmetic O))
    (R : Leaves.ConcreteReserveLeaves (Concrete.realNormArithmetic O) Time)
    (F : Leaves.RealFundamentalTheoremRealization
      (Concrete.realNormArithmetic O) C R) : Set (lsuc t) where
  field
    bernstein : Bernstein.ConcreteBernsteinEnvelopeLeaves
      (Concrete.realNormArithmetic O) C R F

    modeAuthority : ModeNorm.ConcretePeriodicModeNormAuthority

    cutoffIndex :
      Time → Bernstein.ShellState bernstein → Nat

    velocityCoefficient vorticityCoefficient :
      Time → Bernstein.ShellState bernstein →
      Z3.FourierMode → Vec3 ℝ

    coefficientUnitaryL2 hSobolevNorm :
      Time → Bernstein.ShellState bernstein → ℝ

    coefficientUnitaryShellL2 :
      Time → Nat → Bernstein.ShellState bernstein → ℝ

open ConcreteOfficialOperatorNormInputs public

literalLerayInput literalLerayOutput
  literalBiotSavartVorticity literalBiotSavartVelocityH1 :
  ∀ {t} {O : Concrete.RealOrderCancellationAuthority}
    {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus (Concrete.realNormArithmetic O)}
    {R : Leaves.ConcreteReserveLeaves (Concrete.realNormArithmetic O) Time}
    {F : Leaves.RealFundamentalTheoremRealization
      (Concrete.realNormArithmetic O) C R} →
  (I : ConcreteOfficialOperatorNormInputs O C R F) →
  Time → Bernstein.ShellState (bernstein I) → ℝ
literalLerayInput {O = O} I τ state =
  Concrete.lerayInputCutoffSum
    O
    (modeAuthority I)
    (cutoffIndex I τ state)
    (velocityCoefficient I τ state)
literalLerayOutput {O = O} I τ state =
  Concrete.lerayOutputCutoffSum
    O
    (modeAuthority I)
    (cutoffIndex I τ state)
    (velocityCoefficient I τ state)
literalBiotSavartVorticity {O = O} I τ state =
  Concrete.biotSavartInputCutoffSum
    O
    (modeAuthority I)
    (cutoffIndex I τ state)
    (vorticityCoefficient I τ state)
literalBiotSavartVelocityH1 {O = O} I τ state =
  Concrete.biotSavartOutputCutoffSum
    O
    (modeAuthority I)
    (cutoffIndex I τ state)
    (vorticityCoefficient I τ state)

literalOperatorDecomposition :
  ∀ {t} {O : Concrete.RealOrderCancellationAuthority}
    {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus (Concrete.realNormArithmetic O)}
    {R : Leaves.ConcreteReserveLeaves (Concrete.realNormArithmetic O) Time}
    {F : Leaves.RealFundamentalTheoremRealization
      (Concrete.realNormArithmetic O) C R} →
  (I : ConcreteOfficialOperatorNormInputs O C R F) →
  ∀ τ state →
  Operator.PeriodicLerayBiotSavartNormInputs
    (Concrete.realNormArithmetic O)
literalOperatorDecomposition {O = O} I τ state =
  Concrete.concreteCutoffOperatorNormInputs
    O
    (modeAuthority I)
    (cutoffIndex I τ state)
    (velocityCoefficient I τ state)
    (vorticityCoefficient I τ state)

concreteOfficialOperatorToPythagoreanInputs :
  ∀ {t} {O : Concrete.RealOrderCancellationAuthority}
    {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus (Concrete.realNormArithmetic O)}
    {R : Leaves.ConcreteReserveLeaves (Concrete.realNormArithmetic O) Time}
    {F : Leaves.RealFundamentalTheoremRealization
      (Concrete.realNormArithmetic O) C R} →
  ConcreteOfficialOperatorNormInputs O C R F →
  Pythagorean.CoefficientUnitaryPythagoreanInputs
    (Concrete.realNormArithmetic O) C R F
concreteOfficialOperatorToPythagoreanInputs I = record
  { bernstein = bernstein I
  ; coefficientUnitaryL2 = coefficientUnitaryL2 I
  ; hSobolevNorm = hSobolevNorm I
  ; coefficientUnitaryShellL2 = coefficientUnitaryShellL2 I
  ; lerayInputL2 = literalLerayInput I
  ; lerayOutputL2 = literalLerayOutput I
  ; biotSavartVorticityL2 = literalBiotSavartVorticity I
  ; biotSavartVelocityH1 = literalBiotSavartVelocityH1 I
  ; normDecomposition = literalOperatorDecomposition I
  ; lerayInputMeaning = λ τ state → refl
  ; lerayOutputMeaning = λ τ state → refl
  ; biotSavartVorticityMeaning = λ τ state → refl
  ; biotSavartVelocityMeaning = λ τ state → refl
  ; CutoffUniform = ⊤
  ; cutoffUniform = tt
  }

concreteOfficialOperatorNormIdentification :
  ∀ {t} {O : Concrete.RealOrderCancellationAuthority}
    {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus (Concrete.realNormArithmetic O)}
    {R : Leaves.ConcreteReserveLeaves (Concrete.realNormArithmetic O) Time}
    {F : Leaves.RealFundamentalTheoremRealization
      (Concrete.realNormArithmetic O) C R} →
  (I : ConcreteOfficialOperatorNormInputs O C R F) →
  Official.OfficialPeriodicNormIdentification
    (Concrete.realNormArithmetic O)
    Time
    Nat
    (Bernstein.ShellState (bernstein I))
concreteOfficialOperatorNormIdentification I =
  Pythagorean.coefficientUnitaryPythagoreanOfficialNorms
    (concreteOfficialOperatorToPythagoreanInputs I)

------------------------------------------------------------------------
-- Status: Parseval remains definitional in the coefficient-unitary convention;
-- Leray and Biot-Savart are now literal finite-sum theorems with exact constant
-- one and a constructed cutoff-uniformity witness.  The remaining official norm
-- work is the already isolated shell Bernstein/reconstruction realization and
-- the foundational real carrier authorities, not an operator estimate.
------------------------------------------------------------------------

concreteOfficialOperatorNormAdapterLevel : ProofLevel
concreteOfficialOperatorNormAdapterLevel = machineChecked
