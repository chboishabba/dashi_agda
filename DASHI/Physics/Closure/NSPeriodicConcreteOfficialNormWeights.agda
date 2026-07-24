module DASHI.Physics.Closure.NSPeriodicConcreteOfficialNormWeights where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicOfficialFiniteSumIdentification as Official
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal coefficient-unitary mode weights.
--
-- L2, homogeneous H1 and shell norms are folds over the same exact cutoff cube:
--
--   L2(k)    = |u_N(k)|²,
--   H1(k)    = |k|² |u_N(k)|²,
--   shell(k) = m_j(k)² |u_N(k)|².
--
-- The record also owns conjugate-symmetry compatibility of the coefficients and
-- evenness of every norm weight under k -> -k.
------------------------------------------------------------------------

record ConcreteCoefficientUnitaryWeightInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    multiply : Scalar A → Scalar A → Scalar A

    coefficientNormSquared : Nat → Z3.FourierMode → Scalar A
    modeNormSquared : Z3.FourierMode → Scalar A
    shellMultiplierSquared : Nat → Z3.FourierMode → Scalar A

    CoefficientRealityCompatible : Set
    coefficientRealityCompatible : CoefficientRealityCompatible

    coefficientNormNegationInvariant : ∀ N k →
      coefficientNormSquared N (Z3.negateMode k)
      ≡ coefficientNormSquared N k

    modeNormNegationInvariant : ∀ k →
      modeNormSquared (Z3.negateMode k) ≡ modeNormSquared k

    shellMultiplierNegationInvariant : ∀ shell k →
      shellMultiplierSquared shell (Z3.negateMode k)
      ≡ shellMultiplierSquared shell k

    multiplyCongruent : ∀ {a a′ b b′} →
      a ≡ a′ → b ≡ b′ → multiply a b ≡ multiply a′ b′

open ConcreteCoefficientUnitaryWeightInputs public

literalL2Weight literalH1Weight :
  ∀ {A : AbsorptionArithmetic} →
  ConcreteCoefficientUnitaryWeightInputs A →
  Nat → Z3.FourierMode → Scalar A
literalL2Weight W = coefficientNormSquared W
literalH1Weight W N k =
  multiply W (modeNormSquared W k) (coefficientNormSquared W N k)

literalShellWeightAt :
  ∀ {A : AbsorptionArithmetic} →
  ConcreteCoefficientUnitaryWeightInputs A →
  Nat → Nat → Z3.FourierMode → Scalar A
literalShellWeightAt W N shell k =
  multiply W
    (shellMultiplierSquared W shell k)
    (coefficientNormSquared W N k)

literalL2WeightNegationInvariant :
  ∀ {A : AbsorptionArithmetic}
    (W : ConcreteCoefficientUnitaryWeightInputs A) N k →
  literalL2Weight W N (Z3.negateMode k)
  ≡ literalL2Weight W N k
literalL2WeightNegationInvariant W =
  coefficientNormNegationInvariant W

literalH1WeightNegationInvariant :
  ∀ {A : AbsorptionArithmetic}
    (W : ConcreteCoefficientUnitaryWeightInputs A) N k →
  literalH1Weight W N (Z3.negateMode k)
  ≡ literalH1Weight W N k
literalH1WeightNegationInvariant W N k =
  multiplyCongruent W
    (modeNormNegationInvariant W k)
    (coefficientNormNegationInvariant W N k)

literalShellWeightNegationInvariant :
  ∀ {A : AbsorptionArithmetic}
    (W : ConcreteCoefficientUnitaryWeightInputs A) N shell k →
  literalShellWeightAt W N shell (Z3.negateMode k)
  ≡ literalShellWeightAt W N shell k
literalShellWeightNegationInvariant W N shell k =
  multiplyCongruent W
    (shellMultiplierNegationInvariant W shell k)
    (coefficientNormNegationInvariant W N k)

record ConcreteOfficialRealityCompatible
    {A : AbsorptionArithmetic}
    (W : ConcreteCoefficientUnitaryWeightInputs A) : Set where
  field
    cubeReality : Cube.CutoffCubeRealityCompatible
    coefficientReality : CoefficientRealityCompatible W

    l2WeightEven : ∀ N k →
      literalL2Weight W N (Z3.negateMode k)
      ≡ literalL2Weight W N k

    h1WeightEven : ∀ N k →
      literalH1Weight W N (Z3.negateMode k)
      ≡ literalH1Weight W N k

    shellWeightEven : ∀ N shell k →
      literalShellWeightAt W N shell (Z3.negateMode k)
      ≡ literalShellWeightAt W N shell k

open ConcreteOfficialRealityCompatible public

concreteOfficialRealityCompatible :
  ∀ {A : AbsorptionArithmetic}
    (W : ConcreteCoefficientUnitaryWeightInputs A) →
  ConcreteOfficialRealityCompatible W
concreteOfficialRealityCompatible W = record
  { cubeReality = Cube.cutoffCubeRealityCompatible
  ; coefficientReality = coefficientRealityCompatible W
  ; l2WeightEven = literalL2WeightNegationInvariant W
  ; h1WeightEven = literalH1WeightNegationInvariant W
  ; shellWeightEven = literalShellWeightNegationInvariant W
  }

concreteCoefficientUnitaryNormCarrier :
  ∀ {A : AbsorptionArithmetic} →
  ConcreteCoefficientUnitaryWeightInputs A →
  Official.ConcreteFiniteFourierNormCarrier A
concreteCoefficientUnitaryNormCarrier W = record
  { cutoffModes = Cube.cutoffModes
  ; InCutoff = Cube.InCutoffCube
  ; Listed = Cube._∈_
  ; DuplicateFree = Cube.NoDuplicates
  ; cutoffModeEnumerationComplete = Cube.cutoffModeEnumerationComplete
  ; cutoffModeEnumerationSound = Cube.cutoffModeEnumerationSound
  ; cutoffModeEnumerationNoDuplicates = Cube.cutoffModeEnumerationNoDuplicates
  ; l2ModeWeight = literalL2Weight W
  ; h1ModeWeight = literalH1Weight W
  ; shellModeWeight = literalShellWeightAt W
  ; RealityCompatible = ConcreteOfficialRealityCompatible W
  ; realityCompatible = concreteOfficialRealityCompatible W
  ; ZeroModeHandledExactlyOnce = Cube.ZeroModeHandledExactlyOnce
  ; zeroModeHandledExactlyOnce = Cube.zeroModeHandledExactlyOnce
  }

concreteOfficialFiniteSumIdentification :
  ∀ {A : AbsorptionArithmetic}
    (W : ConcreteCoefficientUnitaryWeightInputs A) N →
  Official.OfficialFiniteSumIdentification
    (concreteCoefficientUnitaryNormCarrier W) N
concreteOfficialFiniteSumIdentification W =
  Official.officialFiniteSumIdentification
    (concreteCoefficientUnitaryNormCarrier W)

------------------------------------------------------------------------
-- Status: the literal cube and all three official norm folds now use the same
-- Galerkin coefficients and reality convention.  The remaining norm theorem is
-- the analytic Parseval/Bernstein identification with physical-space norms.
------------------------------------------------------------------------

concreteOfficialNormWeightsLevel : ProofLevel
concreteOfficialNormWeightsLevel = machineChecked
