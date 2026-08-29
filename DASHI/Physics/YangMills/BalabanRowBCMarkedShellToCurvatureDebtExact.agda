module DASHI.Physics.YangMills.BalabanRowBCMarkedShellToCurvatureDebtExact where

------------------------------------------------------------------------
-- ROW B -> ROW C TEMPORAL CROSS-POLLINATION
--
-- If the SAME differentiated marked shell that closes Row B also dominates the
-- negative same-density curvature debt of Row C, and its combined shell ratio
-- is no larger than the repository's 17/32 contraction ratio, then the existing
-- curvature-debt compiler applies with no additional summability theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanRowBActivityEntropyToShellEnergyExact as B
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondIterationExact as Iter
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact as Tail
import DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact as Curv

powNonnegative : ∀ ratio →
  0ℚ ≤ ratio → ∀ depth → 0ℚ ≤ Iter.pow ratio depth
powNonnegative ratio ratioNN zero = ℚP.nonNegative⁻¹ 1ℚ
powNonnegative ratio ratioNN (suc depth) =
  B.mulNN ratioNN (powNonnegative ratio ratioNN depth)

powMonotoneNonnegative : ∀ {lower upper} →
  0ℚ ≤ lower → 0ℚ ≤ upper → lower ≤ upper →
  ∀ depth → Iter.pow lower depth ≤ Iter.pow upper depth
powMonotoneNonnegative lowerNN upperNN lowerBelow zero = ℚP.≤-refl
powMonotoneNonnegative {lower} {upper}
    lowerNN upperNN lowerBelow (suc depth) =
  ℚP.*-mono-≤
    lowerNN lowerBelow
    (powNonnegative lower lowerNN depth)
    (powMonotoneNonnegative lowerNN upperNN lowerBelow depth)

record MarkedShellCurvatureDomination : Set₁ where
  field
    marked : B.MarkedActivityEntropyShellData
    curvatureDebt : Nat → ℚ

    curvatureDebtNonnegative : ∀ depth → 0ℚ ≤ curvatureDebt depth
    curvatureBelowMarkedShell : ∀ depth →
      curvatureDebt depth ≤ B.shellEnergy marked depth

    combinedRatioBelowTheta :
      B.combinedShellRatio marked ≤ Iter.theta

open MarkedShellCurvatureDomination public

markedShellBelowSeventeenThirtySecond :
  (dataSet : MarkedShellCurvatureDomination) → ∀ depth →
  B.shellEnergy (marked dataSet) depth
  ≤ B.combinedBaseEnergy (marked dataSet) * Iter.thetaPower depth
markedShellBelowSeventeenThirtySecond dataSet depth =
  let
    source = marked dataSet
    ratio = B.combinedShellRatio source
    base = B.combinedBaseEnergy source

    shellBound = B.activityEntropyGiveGeometricShellEnergy source depth

    powerBound : Iter.pow ratio depth ≤ Iter.thetaPower depth
    powerBound = powMonotoneNonnegative
      (B.combinedShellRatioNonnegative source)
      Iter.thetaNonnegative
      (combinedRatioBelowTheta dataSet)
      depth

    scaledPower = Norm.scaleNonnegative
      base (B.combinedBaseEnergyNonnegative source) powerBound
  in
  ℚP.≤-trans shellBound scaledPower

asGeometricNegativeCurvatureDebt :
  MarkedShellCurvatureDomination → Curv.GeometricNegativeCurvatureDebt
asGeometricNegativeCurvatureDebt dataSet = record
  { Curv.GeometricNegativeCurvatureDebt.debtAtScale = curvatureDebt dataSet
  ; Curv.GeometricNegativeCurvatureDebt.debtNonnegative =
      curvatureDebtNonnegative dataSet
  ; Curv.GeometricNegativeCurvatureDebt.amplitude =
      B.combinedBaseEnergy (marked dataSet)
  ; Curv.GeometricNegativeCurvatureDebt.amplitudeNonnegative =
      B.combinedBaseEnergyNonnegative (marked dataSet)
  ; Curv.GeometricNegativeCurvatureDebt.geometricDebtBound =
      λ depth →
        ℚP.≤-trans
          (curvatureBelowMarkedShell dataSet depth)
          (markedShellBelowSeventeenThirtySecond dataSet depth)
  }

markedShellCurvatureDebtUniformBound :
  (dataSet : MarkedShellCurvatureDomination) → ∀ count →
  Curv.finiteCurvatureDebt (asGeometricNegativeCurvatureDebt dataSet) count
  ≤ Tail.tailFactor * B.combinedBaseEnergy (marked dataSet)
markedShellCurvatureDebtUniformBound dataSet count =
  Curv.finiteCurvatureDebtUniformBound
    (asGeometricNegativeCurvatureDebt dataSet) count

rowBCMarkedShellToCurvatureCarrierLevel : ProofLevel
rowBCMarkedShellToCurvatureCarrierLevel = machineChecked

rowBCMarkedShellToUniformCurvatureDebtLevel : ProofLevel
rowBCMarkedShellToUniformCurvatureDebtLevel = machineChecked

-- Physical seam: identify `curvatureDebt` with the negative Hessian/Heat-Doob
-- shell debt on the SAME literal compact-group Gibbs density and prove its
-- pointwise domination by the differentiated CMP116 marked shell.  Spatial
-- influence/clustering remains a separate Row-C requirement.
literalSameDensityCurvatureBelowMarkedShellLevel : ProofLevel
literalSameDensityCurvatureBelowMarkedShellLevel = conditional
