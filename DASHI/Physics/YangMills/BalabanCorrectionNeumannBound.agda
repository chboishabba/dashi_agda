module DASHI.Physics.YangMills.BalabanCorrectionNeumannBound where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record CorrectionNeumannData
    (Index State Bound : Set) : Set₁ where
  field
    residual residualPower correction partialCorrection tail :
      Index → Nat → State → State
    weightedNorm : State → Bound
    multiply power : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    StrictlyBelowOne : Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    q correctionUpper : Bound
    qStrict : StrictlyBelowOne q
    residualPowerBound : ∀ index depth source →
      LessEqual (weightedNorm (residualPower index depth source))
        (multiply (power q q) (weightedNorm source))
    correctionSplit : ∀ index depth source →
      correction index depth source ≡ partialCorrection index depth source
    tailBound : ∀ index depth source →
      LessEqual (weightedNorm (tail index depth source))
        (multiply (multiply correctionUpper (power q q))
          (weightedNorm source))
    correctionBound : ∀ index depth source →
      LessEqual (weightedNorm (correction index depth source))
        (multiply correctionUpper (weightedNorm source))

open CorrectionNeumannData public

uniformCorrectionInverseBound :
  ∀ {Index State Bound : Set} →
  (dataSet : CorrectionNeumannData Index State Bound) →
  ∀ index depth source →
  LessEqual dataSet
    (weightedNorm dataSet (correction dataSet index depth source))
    (multiply dataSet (correctionUpper dataSet) (weightedNorm dataSet source))
uniformCorrectionInverseBound dataSet = correctionBound dataSet

correctionNeumannAssemblyLevel : ProofLevel
correctionNeumannAssemblyLevel = machineChecked
strictResidualAndGeometricSumInputsLevel : ProofLevel
strictResidualAndGeometricSumInputsLevel = conditional
