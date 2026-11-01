module DASHI.Physics.YangMills.BalabanSU2AdjointOrderedReduction where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; oneR)
open import DASHI.Physics.YangMills.BalabanSU2AdjointTransportExact
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using (_:=_; _:+_; _:*_)

------------------------------------------------------------------------
-- Ordered reduction of the exact SU(2) displacement identity.
--
-- The polynomial theorem below exposes the discarded Cauchy--Schwarz square:
--
--   main(q,v) + 4 <Im q,v>² = 4 ||Im q||² ||v||².
--
-- Consequently the one-link displacement estimate requires only the standard
-- ordered fact that this explicit square is nonnegative.  No operator norm,
-- exponential chart, or radius is hidden in the algebraic theorem.
------------------------------------------------------------------------

fourDotSquareR : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
fourDotSquareR b c d x y z =
  fourR *R squareR (imaginaryDotVectorR b c d x y z)

fourImaginaryTimesVectorR : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
fourImaginaryTimesVectorR b c d x y z =
  fourR *R
    (imaginaryNormSqR b c d *R vectorNormSqR x y z)

unitMainPlusDotSquareExact : ∀ b c d x y z →
  unitAdjointDisplacementMainR b c d x y z
    +R fourDotSquareR b c d x y z
  ≡ fourImaginaryTimesVectorR b c d x y z
unitMainPlusDotSquareExact =
  solveComputed 6
    (λ b c d x y z →
      unitAdjointDisplacementMainP b c d x y z
        :+ (fourP :* squareP (imaginaryDotVectorP b c d x y z))
      := fourP :*
        (imaginaryNormSqP b c d :* vectorNormSqP x y z))
    computed

record SU2AdjointSquareOrder : Set₁ where
  field
    LessEqual : ℝ → ℝ → Set
    Nonnegative : ℝ → Set
    baseBelowBasePlusNonnegative : ∀ base remainder →
      Nonnegative remainder →
      LessEqual base (base +R remainder)
    fourDotSquareNonnegative : ∀ b c d x y z →
      Nonnegative (fourDotSquareR b c d x y z)

open SU2AdjointSquareOrder public

unitAdjointMainUpper :
  (ordered : SU2AdjointSquareOrder) →
  ∀ b c d x y z →
  LessEqual ordered
    (unitAdjointDisplacementMainR b c d x y z)
    (fourImaginaryTimesVectorR b c d x y z)
unitAdjointMainUpper ordered b c d x y z
  rewrite sym (unitMainPlusDotSquareExact b c d x y z) =
  baseBelowBasePlusNonnegative ordered
    (unitAdjointDisplacementMainR b c d x y z)
    (fourDotSquareR b c d x y z)
    (fourDotSquareNonnegative ordered b c d x y z)

unitQuaternionAdjointDisplacementUpper :
  (ordered : SU2AdjointSquareOrder) →
  ∀ a b c d x y z →
  qNormSqR a b c d ≡ oneR →
  LessEqual ordered
    (adjointDisplacementSqR a b c d x y z)
    (fourImaginaryTimesVectorR b c d x y z)
unitQuaternionAdjointDisplacementUpper ordered a b c d x y z unit
  rewrite adjointDisplacementOnUnitQuaternion a b c d x y z unit =
  unitAdjointMainUpper ordered b c d x y z

su2AdjointDiscardedSquareIdentityLevel : ProofLevel
su2AdjointDiscardedSquareIdentityLevel = computed

su2AdjointOrderedSquareReductionLevel : ProofLevel
su2AdjointOrderedSquareReductionLevel = machineChecked

su2ImaginaryPartRadiusInputLevel : ProofLevel
su2ImaginaryPartRadiusInputLevel = conditional

su2SquaredNormToOperatorNormInputLevel : ProofLevel
su2SquaredNormToOperatorNormInputLevel = conditional
