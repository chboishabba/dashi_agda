module DASHI.Physics.YangMills.BalabanPath13GeneratedLDLStagedProofExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanRationalLDLCertificate
open import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLResidualsBExact public

------------------------------------------------------------------------
-- Staged exact reconstruction.
--
-- Instead of one 12-variable solve over all dense LDL squares, prove
--   R_k = d_k * ell_k^2 + R_{k+1}
-- one Schur stage at a time and compose the equalities propositionally.
------------------------------------------------------------------------

path13GapToResidual0Raw : ∀ a b c d e f g h i j k l →
  path13Energy (path13Coordinates a b c d e f g h i j k l)
    - oneEighteenth * path13NormSq (path13Coordinates a b c d e f g h i j k l)
  ≡ residual0 (path13Coordinates a b c d e f g h i j k l)
path13GapToResidual0Raw = ℚRing.solve-∀

path13GapToResidual0 : ∀ coordinate →
  path13Energy coordinate - oneEighteenth * path13NormSq coordinate
  ≡ residual0 coordinate
path13GapToResidual0 (path13Coordinates a b c d e f g h i j k l) =
  path13GapToResidual0Raw a b c d e f g h i j k l

residualStep0Raw : ∀ a b c d e f g h i j k l →
  residual0 (path13Coordinates a b c d e f g h i j k l)
  ≡ pivot0 * sq (form0 (path13Coordinates a b c d e f g h i j k l))
    + residual1 (path13Coordinates a b c d e f g h i j k l)
residualStep0Raw = ℚRing.solve-∀

residualStep0 : ∀ coordinate →
  residual0 coordinate
  ≡ pivot0 * sq (form0 coordinate) + residual1 coordinate
residualStep0 (path13Coordinates a b c d e f g h i j k l) =
  residualStep0Raw a b c d e f g h i j k l

residualStep1Raw : ∀ b c d e f g h i j k l →
  residual1 (path13Coordinates 0ℚ b c d e f g h i j k l)
  ≡ pivot1 * sq (form1 (path13Coordinates 0ℚ b c d e f g h i j k l))
    + residual2 (path13Coordinates 0ℚ b c d e f g h i j k l)
residualStep1Raw = ℚRing.solve-∀

residualStep1 : ∀ coordinate →
  residual1 coordinate
  ≡ pivot1 * sq (form1 coordinate) + residual2 coordinate
residualStep1 (path13Coordinates a b c d e f g h i j k l) =
  residualStep1Raw b c d e f g h i j k l

residualStep2Raw : ∀ c d e f g h i j k l →
  residual2 (path13Coordinates 0ℚ 0ℚ c d e f g h i j k l)
  ≡ pivot2 * sq (form2 (path13Coordinates 0ℚ 0ℚ c d e f g h i j k l))
    + residual3 (path13Coordinates 0ℚ 0ℚ c d e f g h i j k l)
residualStep2Raw = ℚRing.solve-∀

residualStep2 : ∀ coordinate →
  residual2 coordinate
  ≡ pivot2 * sq (form2 coordinate) + residual3 coordinate
residualStep2 (path13Coordinates a b c d e f g h i j k l) =
  residualStep2Raw c d e f g h i j k l

residualStep3Raw : ∀ d e f g h i j k l →
  residual3 (path13Coordinates 0ℚ 0ℚ 0ℚ d e f g h i j k l)
  ≡ pivot3 * sq (form3 (path13Coordinates 0ℚ 0ℚ 0ℚ d e f g h i j k l))
    + residual4 (path13Coordinates 0ℚ 0ℚ 0ℚ d e f g h i j k l)
residualStep3Raw = ℚRing.solve-∀

residualStep3 : ∀ coordinate →
  residual3 coordinate
  ≡ pivot3 * sq (form3 coordinate) + residual4 coordinate
residualStep3 (path13Coordinates a b c d e f g h i j k l) =
  residualStep3Raw d e f g h i j k l

residualStep4Raw : ∀ e f g h i j k l →
  residual4 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ e f g h i j k l)
  ≡ pivot4 * sq (form4 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ e f g h i j k l))
    + residual5 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ e f g h i j k l)
residualStep4Raw = ℚRing.solve-∀

residualStep4 : ∀ coordinate →
  residual4 coordinate
  ≡ pivot4 * sq (form4 coordinate) + residual5 coordinate
residualStep4 (path13Coordinates a b c d e f g h i j k l) =
  residualStep4Raw e f g h i j k l

residualStep5Raw : ∀ f g h i j k l →
  residual5 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ f g h i j k l)
  ≡ pivot5 * sq (form5 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ f g h i j k l))
    + residual6 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ f g h i j k l)
residualStep5Raw = ℚRing.solve-∀

residualStep5 : ∀ coordinate →
  residual5 coordinate
  ≡ pivot5 * sq (form5 coordinate) + residual6 coordinate
residualStep5 (path13Coordinates a b c d e f g h i j k l) =
  residualStep5Raw f g h i j k l

residualStep6Raw : ∀ g h i j k l →
  residual6 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ g h i j k l)
  ≡ pivot6 * sq (form6 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ g h i j k l))
    + residual7 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ g h i j k l)
residualStep6Raw = ℚRing.solve-∀

residualStep6 : ∀ coordinate →
  residual6 coordinate
  ≡ pivot6 * sq (form6 coordinate) + residual7 coordinate
residualStep6 (path13Coordinates a b c d e f g h i j k l) =
  residualStep6Raw g h i j k l

residualStep7Raw : ∀ h i j k l →
  residual7 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ h i j k l)
  ≡ pivot7 * sq (form7 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ h i j k l))
    + residual8 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ h i j k l)
residualStep7Raw = ℚRing.solve-∀

residualStep7 : ∀ coordinate →
  residual7 coordinate
  ≡ pivot7 * sq (form7 coordinate) + residual8 coordinate
residualStep7 (path13Coordinates a b c d e f g h i j k l) =
  residualStep7Raw h i j k l

residualStep8Raw : ∀ i j k l →
  residual8 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ i j k l)
  ≡ pivot8 * sq (form8 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ i j k l))
    + residual9 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ i j k l)
residualStep8Raw = ℚRing.solve-∀

residualStep8 : ∀ coordinate →
  residual8 coordinate
  ≡ pivot8 * sq (form8 coordinate) + residual9 coordinate
residualStep8 (path13Coordinates a b c d e f g h i j k l) =
  residualStep8Raw i j k l

residualStep9Raw : ∀ j k l →
  residual9 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ j k l)
  ≡ pivot9 * sq (form9 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ j k l))
    + residual10 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ j k l)
residualStep9Raw = ℚRing.solve-∀

residualStep9 : ∀ coordinate →
  residual9 coordinate
  ≡ pivot9 * sq (form9 coordinate) + residual10 coordinate
residualStep9 (path13Coordinates a b c d e f g h i j k l) =
  residualStep9Raw j k l

residualStep10Raw : ∀ k l →
  residual10 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ k l)
  ≡ pivot10 * sq (form10 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ k l))
    + residual11 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ k l)
residualStep10Raw = ℚRing.solve-∀

residualStep10 : ∀ coordinate →
  residual10 coordinate
  ≡ pivot10 * sq (form10 coordinate) + residual11 coordinate
residualStep10 (path13Coordinates a b c d e f g h i j k l) =
  residualStep10Raw k l

residualStep11Raw : ∀ l →
  residual11 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ l)
  ≡ pivot11 * sq (form11 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ l))
    + residual12 (path13Coordinates 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ l)
residualStep11Raw = ℚRing.solve-∀

residualStep11 : ∀ coordinate →
  residual11 coordinate
  ≡ pivot11 * sq (form11 coordinate) + residual12 coordinate
residualStep11 (path13Coordinates a b c d e f g h i j k l) =
  residualStep11Raw l

stagedSum12 : Path13Coordinates → ℚ
stagedSum12 coordinate = 0ℚ

stagedSum11 : Path13Coordinates → ℚ
stagedSum11 coordinate =
  pivot11 * sq (form11 coordinate) + stagedSum12 coordinate

stagedSum10 : Path13Coordinates → ℚ
stagedSum10 coordinate =
  pivot10 * sq (form10 coordinate) + stagedSum11 coordinate

stagedSum9 : Path13Coordinates → ℚ
stagedSum9 coordinate =
  pivot9 * sq (form9 coordinate) + stagedSum10 coordinate

stagedSum8 : Path13Coordinates → ℚ
stagedSum8 coordinate =
  pivot8 * sq (form8 coordinate) + stagedSum9 coordinate

stagedSum7 : Path13Coordinates → ℚ
stagedSum7 coordinate =
  pivot7 * sq (form7 coordinate) + stagedSum8 coordinate

stagedSum6 : Path13Coordinates → ℚ
stagedSum6 coordinate =
  pivot6 * sq (form6 coordinate) + stagedSum7 coordinate

stagedSum5 : Path13Coordinates → ℚ
stagedSum5 coordinate =
  pivot5 * sq (form5 coordinate) + stagedSum6 coordinate

stagedSum4 : Path13Coordinates → ℚ
stagedSum4 coordinate =
  pivot4 * sq (form4 coordinate) + stagedSum5 coordinate

stagedSum3 : Path13Coordinates → ℚ
stagedSum3 coordinate =
  pivot3 * sq (form3 coordinate) + stagedSum4 coordinate

stagedSum2 : Path13Coordinates → ℚ
stagedSum2 coordinate =
  pivot2 * sq (form2 coordinate) + stagedSum3 coordinate

stagedSum1 : Path13Coordinates → ℚ
stagedSum1 coordinate =
  pivot1 * sq (form1 coordinate) + stagedSum2 coordinate

stagedSum0 : Path13Coordinates → ℚ
stagedSum0 coordinate =
  pivot0 * sq (form0 coordinate) + stagedSum1 coordinate

residual11Decomposition : ∀ coordinate →
  residual11 coordinate ≡ stagedSum11 coordinate
residual11Decomposition = residualStep11

residual10Decomposition : ∀ coordinate →
  residual10 coordinate ≡ stagedSum10 coordinate
residual10Decomposition coordinate =
  trans
    (residualStep10 coordinate)
    (cong
      (λ rest → pivot10 * sq (form10 coordinate) + rest)
      (residual11Decomposition coordinate))

residual9Decomposition : ∀ coordinate →
  residual9 coordinate ≡ stagedSum9 coordinate
residual9Decomposition coordinate =
  trans
    (residualStep9 coordinate)
    (cong
      (λ rest → pivot9 * sq (form9 coordinate) + rest)
      (residual10Decomposition coordinate))

residual8Decomposition : ∀ coordinate →
  residual8 coordinate ≡ stagedSum8 coordinate
residual8Decomposition coordinate =
  trans
    (residualStep8 coordinate)
    (cong
      (λ rest → pivot8 * sq (form8 coordinate) + rest)
      (residual9Decomposition coordinate))

residual7Decomposition : ∀ coordinate →
  residual7 coordinate ≡ stagedSum7 coordinate
residual7Decomposition coordinate =
  trans
    (residualStep7 coordinate)
    (cong
      (λ rest → pivot7 * sq (form7 coordinate) + rest)
      (residual8Decomposition coordinate))

residual6Decomposition : ∀ coordinate →
  residual6 coordinate ≡ stagedSum6 coordinate
residual6Decomposition coordinate =
  trans
    (residualStep6 coordinate)
    (cong
      (λ rest → pivot6 * sq (form6 coordinate) + rest)
      (residual7Decomposition coordinate))

residual5Decomposition : ∀ coordinate →
  residual5 coordinate ≡ stagedSum5 coordinate
residual5Decomposition coordinate =
  trans
    (residualStep5 coordinate)
    (cong
      (λ rest → pivot5 * sq (form5 coordinate) + rest)
      (residual6Decomposition coordinate))

residual4Decomposition : ∀ coordinate →
  residual4 coordinate ≡ stagedSum4 coordinate
residual4Decomposition coordinate =
  trans
    (residualStep4 coordinate)
    (cong
      (λ rest → pivot4 * sq (form4 coordinate) + rest)
      (residual5Decomposition coordinate))

residual3Decomposition : ∀ coordinate →
  residual3 coordinate ≡ stagedSum3 coordinate
residual3Decomposition coordinate =
  trans
    (residualStep3 coordinate)
    (cong
      (λ rest → pivot3 * sq (form3 coordinate) + rest)
      (residual4Decomposition coordinate))

residual2Decomposition : ∀ coordinate →
  residual2 coordinate ≡ stagedSum2 coordinate
residual2Decomposition coordinate =
  trans
    (residualStep2 coordinate)
    (cong
      (λ rest → pivot2 * sq (form2 coordinate) + rest)
      (residual3Decomposition coordinate))

residual1Decomposition : ∀ coordinate →
  residual1 coordinate ≡ stagedSum1 coordinate
residual1Decomposition coordinate =
  trans
    (residualStep1 coordinate)
    (cong
      (λ rest → pivot1 * sq (form1 coordinate) + rest)
      (residual2Decomposition coordinate))

residual0Decomposition : ∀ coordinate →
  residual0 coordinate ≡ stagedSum0 coordinate
residual0Decomposition coordinate =
  trans
    (residualStep0 coordinate)
    (cong
      (λ rest → pivot0 * sq (form0 coordinate) + rest)
      (residual1Decomposition coordinate))

stagedSumMatchesTerms : ∀ coordinate →
  stagedSum0 coordinate ≡ sumTermValues path13Terms coordinate
stagedSumMatchesTerms coordinate = refl

energyGapBridgeRaw : ∀ x y → x ≡ y + (x - y)
energyGapBridgeRaw = ℚRing.solve-∀

path13LDLDecomposition : ∀ coordinate →
  path13Energy coordinate
  ≡ oneEighteenth * path13NormSq coordinate
    + sumTermValues path13Terms coordinate
path13LDLDecomposition coordinate =
  trans
    (energyGapBridgeRaw
      (path13Energy coordinate)
      (oneEighteenth * path13NormSq coordinate))
    (cong
      (λ remainder → oneEighteenth * path13NormSq coordinate + remainder)
      (trans
        (path13GapToResidual0 coordinate)
        (trans
          (residual0Decomposition coordinate)
          (stagedSumMatchesTerms coordinate))))

path13LDLCertificate : RationalLDLCertificate Path13Coordinates
path13LDLCertificate = record
  { normSq = path13NormSq
  ; energy = path13Energy
  ; coercivityConstant = oneEighteenth
  ; terms = path13Terms
  ; decomposition = path13LDLDecomposition
  }

path13Poincare : ∀ coordinate →
  oneEighteenth * path13NormSq coordinate ≤ path13Energy coordinate
path13Poincare = ldlCertificatePoincare path13LDLCertificate

path13GeneratedLDLReconstructionLevel : ProofLevel
path13GeneratedLDLReconstructionLevel = machineChecked

path13GeneratedLDLConsumptionLevel : ProofLevel
path13GeneratedLDLConsumptionLevel = machineChecked
