module DASHI.Physics.YangMills.BalabanCMP109WalshCharacterOrbitCancellationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I. Generation of Effective Actions in a Small Field Approximation
-- and a Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.  Section 5, especially (5.6)--(5.8).
--
-- Jean-Pierre Serre, "Linear Representations of Finite Groups",
-- Springer, 1977. DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Round57 already transports Bałaban's coordinate-reflection/permutation laws
-- to the generated 4^4 Brillouin grid and obtains the four geometric orbits.
-- Here we use the reflection subgroup (C2)^4 one level earlier: on any scalar
-- contribution satisfying the SAME source covariance, every nontrivial Walsh
-- character coefficient of a full sign orbit vanishes exactly before interval
-- arithmetic.  The trivial coefficient is exactly 16 times the contribution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _*_; _+_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact as Walsh
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact as Source

signMaskAct : Cube.Subset4 → Grid.GridCell4 → Grid.GridCell4
signMaskAct Cube.empty cell = cell
signMaskAct Cube.s0 cell = Action.act Action.flip0 cell
signMaskAct Cube.s1 cell = Action.act Action.flip1 cell
signMaskAct Cube.s2 cell = Action.act Action.flip2 cell
signMaskAct Cube.s3 cell = Action.act Action.flip3 cell
signMaskAct Cube.s01 cell = Action.act Action.flip1 (Action.act Action.flip0 cell)
signMaskAct Cube.s02 cell = Action.act Action.flip2 (Action.act Action.flip0 cell)
signMaskAct Cube.s03 cell = Action.act Action.flip3 (Action.act Action.flip0 cell)
signMaskAct Cube.s12 cell = Action.act Action.flip2 (Action.act Action.flip1 cell)
signMaskAct Cube.s13 cell = Action.act Action.flip3 (Action.act Action.flip1 cell)
signMaskAct Cube.s23 cell = Action.act Action.flip3 (Action.act Action.flip2 cell)
signMaskAct Cube.s012 cell =
  Action.act Action.flip2 (Action.act Action.flip1 (Action.act Action.flip0 cell))
signMaskAct Cube.s013 cell =
  Action.act Action.flip3 (Action.act Action.flip1 (Action.act Action.flip0 cell))
signMaskAct Cube.s023 cell =
  Action.act Action.flip3 (Action.act Action.flip2 (Action.act Action.flip0 cell))
signMaskAct Cube.s123 cell =
  Action.act Action.flip3 (Action.act Action.flip2 (Action.act Action.flip1 cell))
signMaskAct Cube.s0123 cell =
  Action.act Action.flip3
    (Action.act Action.flip2
      (Action.act Action.flip1 (Action.act Action.flip0 cell)))

signMaskContributionInvariant :
  ∀ {contribution : Grid.GridCell4 → ℚ} →
  Source.CMP109ScalarEuclideanSymmetry contribution →
  (signMask : Cube.Subset4) →
  (cell : Grid.GridCell4) →
  contribution cell ≡ contribution (signMaskAct signMask cell)
signMaskContributionInvariant symmetry Cube.empty cell = refl
signMaskContributionInvariant symmetry Cube.s0 cell =
  Source.reflectionInvariant symmetry Source.reflect0 cell
signMaskContributionInvariant symmetry Cube.s1 cell =
  Source.reflectionInvariant symmetry Source.reflect1 cell
signMaskContributionInvariant symmetry Cube.s2 cell =
  Source.reflectionInvariant symmetry Source.reflect2 cell
signMaskContributionInvariant symmetry Cube.s3 cell =
  Source.reflectionInvariant symmetry Source.reflect3 cell
signMaskContributionInvariant symmetry Cube.s01 cell =
  trans
    (Source.reflectionInvariant symmetry Source.reflect0 cell)
    (Source.reflectionInvariant symmetry Source.reflect1 (Action.act Action.flip0 cell))
signMaskContributionInvariant symmetry Cube.s02 cell =
  trans
    (Source.reflectionInvariant symmetry Source.reflect0 cell)
    (Source.reflectionInvariant symmetry Source.reflect2 (Action.act Action.flip0 cell))
signMaskContributionInvariant symmetry Cube.s03 cell =
  trans
    (Source.reflectionInvariant symmetry Source.reflect0 cell)
    (Source.reflectionInvariant symmetry Source.reflect3 (Action.act Action.flip0 cell))
signMaskContributionInvariant symmetry Cube.s12 cell =
  trans
    (Source.reflectionInvariant symmetry Source.reflect1 cell)
    (Source.reflectionInvariant symmetry Source.reflect2 (Action.act Action.flip1 cell))
signMaskContributionInvariant symmetry Cube.s13 cell =
  trans
    (Source.reflectionInvariant symmetry Source.reflect1 cell)
    (Source.reflectionInvariant symmetry Source.reflect3 (Action.act Action.flip1 cell))
signMaskContributionInvariant symmetry Cube.s23 cell =
  trans
    (Source.reflectionInvariant symmetry Source.reflect2 cell)
    (Source.reflectionInvariant symmetry Source.reflect3 (Action.act Action.flip2 cell))
signMaskContributionInvariant symmetry Cube.s012 cell =
  trans
    (Source.reflectionInvariant symmetry Source.reflect0 cell)
    (trans
      (Source.reflectionInvariant symmetry Source.reflect1 (Action.act Action.flip0 cell))
      (Source.reflectionInvariant symmetry Source.reflect2
        (Action.act Action.flip1 (Action.act Action.flip0 cell))))
signMaskContributionInvariant symmetry Cube.s013 cell =
  trans
    (Source.reflectionInvariant symmetry Source.reflect0 cell)
    (trans
      (Source.reflectionInvariant symmetry Source.reflect1 (Action.act Action.flip0 cell))
      (Source.reflectionInvariant symmetry Source.reflect3
        (Action.act Action.flip1 (Action.act Action.flip0 cell))))
signMaskContributionInvariant symmetry Cube.s023 cell =
  trans
    (Source.reflectionInvariant symmetry Source.reflect0 cell)
    (trans
      (Source.reflectionInvariant symmetry Source.reflect2 (Action.act Action.flip0 cell))
      (Source.reflectionInvariant symmetry Source.reflect3
        (Action.act Action.flip2 (Action.act Action.flip0 cell))))
signMaskContributionInvariant symmetry Cube.s123 cell =
  trans
    (Source.reflectionInvariant symmetry Source.reflect1 cell)
    (trans
      (Source.reflectionInvariant symmetry Source.reflect2 (Action.act Action.flip1 cell))
      (Source.reflectionInvariant symmetry Source.reflect3
        (Action.act Action.flip2 (Action.act Action.flip1 cell))))
signMaskContributionInvariant symmetry Cube.s0123 cell =
  trans
    (Source.reflectionInvariant symmetry Source.reflect0 cell)
    (trans
      (Source.reflectionInvariant symmetry Source.reflect1 (Action.act Action.flip0 cell))
      (trans
        (Source.reflectionInvariant symmetry Source.reflect2
          (Action.act Action.flip1 (Action.act Action.flip0 cell)))
        (Source.reflectionInvariant symmetry Source.reflect3
          (Action.act Action.flip2
            (Action.act Action.flip1 (Action.act Action.flip0 cell))))))

signedOrbitWalshCoefficient :
  (Grid.GridCell4 → ℚ) →
  Cube.Subset4 → Grid.GridCell4 → ℚ
signedOrbitWalshCoefficient contribution character cell =
  Sums.sumRational Cube.allSubsets4
    (λ signMask →
      Walsh.walshCharacter character signMask
      * contribution (signMaskAct signMask cell))

signedOrbitCollapsesToConstantCharacterSum :
  ∀ {contribution : Grid.GridCell4 → ℚ} →
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution) →
  (character : Cube.Subset4) →
  (cell : Grid.GridCell4) →
  signedOrbitWalshCoefficient contribution character cell
  ≡ Walsh.walshCoefficient
      (Walsh.constantFunction (contribution cell)) character
signedOrbitCollapsesToConstantCharacterSum symmetry character cell =
  Sums.sumRationalCong Cube.allSubsets4 _ _
    (λ signMask →
      cong (λ value → Walsh.walshCharacter character signMask * value)
        (sym (signMaskContributionInvariant symmetry signMask cell)))

nontrivialSignedOrbitCharacterVanishes :
  ∀ {contribution : Grid.GridCell4 → ℚ}
    {character : Cube.Subset4} →
  Source.CMP109ScalarEuclideanSymmetry contribution →
  Walsh.NontrivialWalshCharacter character →
  (cell : Grid.GridCell4) →
  signedOrbitWalshCoefficient contribution character cell ≡ 0ℚ
nontrivialSignedOrbitCharacterVanishes symmetry nontrivial cell =
  trans
    (signedOrbitCollapsesToConstantCharacterSum symmetry _ cell)
    (Walsh.nontrivialWalshKillsConstant nontrivial (contribution cell))

trivialSignedOrbitCharacterIsSixteenTimesContribution :
  ∀ {contribution : Grid.GridCell4 → ℚ} →
  Source.CMP109ScalarEuclideanSymmetry contribution →
  (cell : Grid.GridCell4) →
  signedOrbitWalshCoefficient contribution Cube.empty cell
  ≡ (+ 16 / 1) * contribution cell
trivialSignedOrbitCharacterIsSixteenTimesContribution symmetry cell =
  trans
    (signedOrbitCollapsesToConstantCharacterSum symmetry Cube.empty cell)
    (Walsh.trivialWalshConstantIsSixteen (contribution cell))

cmp109SignCharacterCancellationLevel : ProofLevel
cmp109SignCharacterCancellationLevel = machineChecked

cmp109TrivialCharacterOrbitFactorLevel : ProofLevel
cmp109TrivialCharacterOrbitFactorLevel = machineChecked

literalWilsonFaddeevPopovHaarScalarIsCMP109ProjectionLevel : ProofLevel
literalWilsonFaddeevPopovHaarScalarIsCMP109ProjectionLevel = conditional
