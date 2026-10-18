{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedBaseGlobalCommutatorRound800Exact where

------------------------------------------------------------------------
-- ROUND800 / GLOBAL B_sep = EIGHT TIMES OUTPUT-INDEXED MASKED R230 WORK
--
-- R799 proves the raw fixed-output identity
--
--   RawB_sep(k) = 8 W(M_k,C_sep,k).
--
-- R763's actual paired base row additionally masks the zero output.  R39
-- partitions the complete physical enumeration exactly by literal outputs.
-- Therefore define
--
--   CWork_sep(k) = 0                         if k = 0,
--                = W(M_k,C_sep,k)           otherwise.
--
-- Then on the SAME R791 fully-separated paired-base carrier:
--
--   B_sep = 8 * sum_{k in cutoffModes} CWork_sep(k).
--
-- This is an exact physical identification.  No estimate, norm, absolute
-- value, or shell majorization is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Data.List.Relation.Binary.Permutation.Propositional as Perm

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650SeparatedPairedNestedProductRuleRound791Exact as R791
import DASHI.Physics.Closure.NSTriadKNR650SeparatedPairedBaseCommutatorRound799Exact as R799

F : C3.RealField _
F = Rational.rationalRealField

module GlobalSeparatedBaseCommutator
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Sep =
    R791.SeparatedGlobalPairedNested
      physicalSystem S L H velocityTransverse

  module Id =
    R799.SeparatedBaseCommutator
      physicalSystem S L H velocityTransverse

  cutoff : Nat
  cutoff = Sep.cutoff

  items : List Physical.PhysicalTriadIncidence
  items = Physical.physicalTriadEnumeration cutoff

  separatedBaseFold : ℚ
  separatedBaseFold =
    R38.foldPower Sep.maskedPairedBaseRow items

  outputCommutatorWork : Z3.FourierMode → ℚ
  outputCommutatorWork output
    with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false =
    Work.coherentWork
      (Id.mixedFold output)
      (Id.commutatorFold output)

  sumOutputCommutatorWork : List Z3.FourierMode → ℚ
  sumOutputCommutatorWork [] = 0ℚ
  sumOutputCommutatorWork (output ∷ rest) =
    outputCommutatorWork output + sumOutputCommutatorWork rest

  globalSeparatedCommutatorWork : ℚ
  globalSeparatedCommutatorWork =
    sumOutputCommutatorWork (Cube.cutoffModes cutoff)

  outputBaseTarget : Z3.FourierMode → ℚ
  outputBaseTarget output with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false = Id.rawSeparatedBaseFold output

  actualRowAtOutput :
    (output : Z3.FourierMode) →
    R38.foldPower Sep.maskedPairedBaseRow
      (Output.physicalOutputFiber cutoff output)
    ≡ outputBaseTarget output
  actualRowAtOutput output
    with Output.modeEqual output Z3.zeroMode in outputZero
  ... | true =
    zeroGo
      (Output.physicalOutputFiber cutoff output)
      (λ beta member → Output.physicalOutputFiberSound member)
    where
    zeroGo :
      (xs : List Physical.PhysicalTriadIncidence) →
      ((beta : Physical.PhysicalTriadIncidence) →
        beta Cube.∈ xs → Physical.k beta ≡ output) →
      R38.foldPower Sep.maskedPairedBaseRow xs ≡ 0ℚ
    zeroGo [] allOutput = refl
    zeroGo (beta ∷ rest) allOutput
      rewrite allOutput beta (Cube.here refl)
            | outputZero
      with R781.ccTouched beta
    ... | true =
      zeroGo rest
        (λ chosen member → allOutput chosen (Cube.there member))
    ... | false =
      zeroGo rest
        (λ chosen member → allOutput chosen (Cube.there member))
  ... | false =
    rawGo
      (Output.physicalOutputFiber cutoff output)
      (λ beta member → Output.physicalOutputFiberSound member)
    where
    rawGo :
      (xs : List Physical.PhysicalTriadIncidence) →
      ((beta : Physical.PhysicalTriadIncidence) →
        beta Cube.∈ xs → Physical.k beta ≡ output) →
      R38.foldPower Sep.maskedPairedBaseRow xs
      ≡ R38.foldPower Id.rawMaskedPairedBaseRow xs
    rawGo [] allOutput = refl
    rawGo (beta ∷ rest) allOutput
      rewrite allOutput beta (Cube.here refl)
            | outputZero
      with R781.ccTouched beta
    ... | true =
      cong (0ℚ +_)
        (rawGo rest
          (λ chosen member → allOutput chosen (Cube.there member)))
    ... | false =
      cong
        (Id.Pair.pairedProductRuleOuterRow beta +_)
        (rawGo rest
          (λ chosen member → allOutput chosen (Cube.there member)))

  outputBaseIsEightCommutatorWork :
    (output : Z3.FourierMode) →
    R38.foldPower Sep.maskedPairedBaseRow
      (Output.physicalOutputFiber cutoff output)
    ≡ R799.eight * outputCommutatorWork output
  outputBaseIsEightCommutatorWork output
    with Output.modeEqual output Z3.zeroMode in outputZero
  ... | true =
    trans
      (actualRowAtOutput output)
      (solve (R799.eight ∷ []))
  ... | false =
    trans
      (actualRowAtOutput output)
      (Id.rawSeparatedBaseIsEightCommutatorWork output)

  concatFoldIsOutputWork :
    (outputs : List Z3.FourierMode) →
    R38.foldPower Sep.maskedPairedBaseRow
      (R39.concatOutputFibers cutoff outputs)
    ≡
    R799.eight * sumOutputCommutatorWork outputs
  concatFoldIsOutputWork [] =
    solve (R799.eight ∷ [])
  concatFoldIsOutputWork (output ∷ rest) =
    trans
      (R39.foldAppend Sep.maskedPairedBaseRow
        (Output.physicalOutputFiber cutoff output)
        (R39.concatOutputFibers cutoff rest))
      (trans
        (cong
          (R38.foldPower Sep.maskedPairedBaseRow
            (Output.physicalOutputFiber cutoff output) +_)
          (concatFoldIsOutputWork rest))
        (trans
          (cong
            (_+ R799.eight * sumOutputCommutatorWork rest)
            (outputBaseIsEightCommutatorWork output))
          (solve
            ( R799.eight
            ∷ outputCommutatorWork output
            ∷ sumOutputCommutatorWork rest
            ∷ []))))

  separatedBaseIsEightGlobalCommutatorWork :
    separatedBaseFold
    ≡ R799.eight * globalSeparatedCommutatorWork
  separatedBaseIsEightGlobalCommutatorWork =
    trans
      (sym
        (R38.foldPermutationInvariant
          Sep.maskedPairedBaseRow
          (R39.literalOutputPartitionPermutation cutoff)))
      (concatFoldIsOutputWork (Cube.cutoffModes cutoff))

round800SeparatedBaseIsEightGlobalMaskedR230Work : Bool
round800SeparatedBaseIsEightGlobalMaskedR230Work = true

round800ZeroOutputBranchPreservedExactly : Bool
round800ZeroOutputBranchPreservedExactly = true

round800UsesLiteralR39OutputPartition : Bool
round800UsesLiteralR39OutputPartition = true

round800IntroducesEstimate : Bool
round800IntroducesEstimate = false

round800W2Closed : Bool
round800W2Closed = false

round800ClayPromotion : Bool
round800ClayPromotion = false

round800SeparatedBaseIsEightGlobalMaskedR230WorkIsTrue :
  round800SeparatedBaseIsEightGlobalMaskedR230Work ≡ true
round800SeparatedBaseIsEightGlobalMaskedR230WorkIsTrue = refl

round800IntroducesEstimateIsFalse :
  round800IntroducesEstimate ≡ false
round800IntroducesEstimateIsFalse = refl

round800W2ClosedIsFalse :
  round800W2Closed ≡ false
round800W2ClosedIsFalse = refl

round800ClayPromotionIsFalse :
  round800ClayPromotion ≡ false
round800ClayPromotionIsFalse = refl
