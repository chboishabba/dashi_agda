module DASHI.Physics.YangMills.BalabanClayGate4DecayStepToDyadicShellExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exponential-step decay to a dyadic shell majorant.
--
-- If one coarse random-walk step costs a factor q <= 1/2, then q^m <= 2^{-m}
-- for every shell depth m. Multiplication by the common shell amplitude gives
-- exactly the hypothesis consumed by the dyadic localization and rooted-sum
-- modules.
------------------------------------------------------------------------

record OrderedDecayPower (Bound : Set) : Set₁ where
  field
    one half : Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (multiply left right) (multiply leftUpper rightUpper)

open OrderedDecayPower public

power : ∀ {Bound} → OrderedDecayPower Bound → Bound → Nat → Bound
power algebra ratio zero = one algebra
power algebra ratio (suc exponent) =
  multiply algebra ratio (power algebra ratio exponent)

powerMonotone :
  ∀ {Bound}
    (algebra : OrderedDecayPower Bound)
    {left right} →
  LessEqual algebra left right →
  ∀ exponent →
  LessEqual algebra
    (power algebra left exponent)
    (power algebra right exponent)
powerMonotone algebra estimate zero =
  reflexive algebra (one algebra)
powerMonotone algebra estimate (suc exponent) =
  multiplyMonotone algebra estimate
    (powerMonotone algebra estimate exponent)

record DecayStepShellData (Bound : Set) : Set₁ where
  field
    algebra : OrderedDecayPower Bound
    amplitude decayStep : Bound
    shellNorm : Nat → Bound

    decayStepBelowHalf :
      LessEqual algebra decayStep (half algebra)

    shellByDecayPower : ∀ depth →
      LessEqual algebra
        (shellNorm depth)
        (multiply algebra amplitude (power algebra decayStep depth))

open DecayStepShellData public

shellBelowDyadicPower :
  ∀ {Bound}
    (dataSet : DecayStepShellData Bound)
    depth →
  LessEqual (algebra dataSet)
    (shellNorm dataSet depth)
    (multiply (algebra dataSet)
      (amplitude dataSet)
      (power (algebra dataSet) (half (algebra dataSet)) depth))
shellBelowDyadicPower dataSet depth =
  transitive (algebra dataSet)
    (shellByDecayPower dataSet depth)
    (multiplyMonotone (algebra dataSet)
      (reflexive (algebra dataSet) (amplitude dataSet))
      (powerMonotone (algebra dataSet)
        (decayStepBelowHalf dataSet) depth))

decayStepPowerMonotonicityLevel : ProofLevel
decayStepPowerMonotonicityLevel = machineChecked

decayStepToDyadicShellLevel : ProofLevel
decayStepToDyadicShellLevel = machineChecked

physicalBackgroundDecayStepBelowHalfInputsLevel : ProofLevel
physicalBackgroundDecayStepBelowHalfInputsLevel = conditional

physicalRandomWalkShellFromPropagatorInputsLevel : ProofLevel
physicalRandomWalkShellFromPropagatorInputsLevel = conditional
