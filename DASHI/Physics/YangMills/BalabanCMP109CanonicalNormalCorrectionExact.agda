module DASHI.Physics.YangMills.BalabanCMP109CanonicalNormalCorrectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Wojciech Dybalski, Alexander Stottmeister, Yoh Tanimoto,
-- "The Bałaban variational problem in the non-linear sigma model",
-- arXiv:2403.09800 (2024). No DOI recorded in the manuscript.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the kernel-line normal correction from an existential witness to a
-- canonical finite object.  If the reopened normal remainder is genuinely
-- one-quarter Lipschitz on the selected finite coordinate carrier, then two
-- solutions of the SAME source equation
--
--       c + R(c) = r
--
-- differ by a homogeneous quarter-contractive equation.  The existing finite
-- reopening theorem therefore forces their l1 difference to zero, and the
-- proof-bearing finite selector upgrades zero l1 norm to coordinatewise
-- equality.
--
-- No continuity of the parameter-to-correction map is used.  Consequently a
-- family of chosen solutions is canonical pointwise as soon as existence is
-- known, exactly as needed for
--
--       gamma_h(t) = A + t h + N_A c_h(t).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis

record QuarterContractiveNormalCorrectionProblem (Index : Set) : Set₁ where
  field
    selector : Basis.FiniteSelector Index
    residual : Reopen.Vector Index → Reopen.Vector Index
    source : Reopen.Vector Index

    quarterLipschitz : ∀ left right →
      L1.vectorL1 (Basis.elements selector)
        (Reopen.vectorDifference (residual left) (residual right))
      ≤ Quarter.oneQuarter
          * L1.vectorL1 (Basis.elements selector)
              (Reopen.vectorDifference left right)

open QuarterContractiveNormalCorrectionProblem public

Solution :
  ∀ {Index} → QuarterContractiveNormalCorrectionProblem Index →
  Reopen.Vector Index → Set
Solution problem correction =
  Reopen.IdentityPlusResidualEquation
    (residual problem) correction (source problem)

differenceResidual :
  ∀ {Index} (problem : QuarterContractiveNormalCorrectionProblem Index) →
  Reopen.Vector Index → Reopen.Vector Index →
  Reopen.Vector Index → Reopen.Vector Index
differenceResidual problem left right _ =
  Reopen.vectorDifference (residual problem left) (residual problem right)

solutionDifferenceEquation :
  ∀ {Index}
    (problem : QuarterContractiveNormalCorrectionProblem Index)
    left right →
  Solution problem left →
  Solution problem right →
  Reopen.IdentityPlusResidualEquation
    (differenceResidual problem left right)
    (Reopen.vectorDifference left right)
    Reopen.zeroVector
solutionDifferenceEquation problem left right leftSol rightSol row =
  let
    x = left row
    y = right row
    rx = residual problem left row
    ry = residual problem right row
    s = source problem row
  in
  trans
    (ℚRing.solve-∀ x y rx ry :
      (x - y) + (rx - ry) ≡ (x + rx) - (y + ry))
    (trans
      (cong₂ _-_ (leftSol row) (rightSol row))
      (ℚRing.solve-∀ s : s - s ≡ 0ℚ))

solutionDifferenceQuarterBound :
  ∀ {Index}
    (problem : QuarterContractiveNormalCorrectionProblem Index)
    left right →
  L1.vectorL1 (Basis.elements (selector problem))
    (differenceResidual problem left right
      (Reopen.vectorDifference left right))
  ≤ Quarter.oneQuarter
      * L1.vectorL1 (Basis.elements (selector problem))
          (Reopen.vectorDifference left right)
solutionDifferenceQuarterBound problem left right =
  quarterLipschitz problem left right

quarterContractiveNormalCorrectionUnique :
  ∀ {Index}
    (problem : QuarterContractiveNormalCorrectionProblem Index)
    left right →
  Solution problem left →
  Solution problem right →
  ∀ coordinate → left coordinate ≡ right coordinate
quarterContractiveNormalCorrectionUnique problem left right leftSol rightSol coordinate =
  let
    differenceZero = Quarter.oneQuarterHomogeneousPointwiseZero
      (selector problem)
      (differenceResidual problem left right)
      (Reopen.vectorDifference left right)
      (solutionDifferenceEquation problem left right leftSol rightSol)
      (solutionDifferenceQuarterBound problem left right)
      coordinate
    l = left coordinate
    r = right coordinate
  in
  trans
    (sym (ℚRing.solve-∀ l r : (l - r) + r ≡ l))
    (trans
      (cong (_+ r) differenceZero)
      (ℚRing.solve-∀ r : 0ℚ + r ≡ r))

------------------------------------------------------------------------
-- Canonical parameterized correction.
------------------------------------------------------------------------

record CanonicalNormalCorrectionFamily (Parameter Index : Set) : Set₁ where
  field
    problem : Parameter → QuarterContractiveNormalCorrectionProblem Index
    correction : Parameter → Reopen.Vector Index
    solves : ∀ parameter → Solution (problem parameter) (correction parameter)

open CanonicalNormalCorrectionFamily public

canonicalCorrectionIsUnique :
  ∀ {Parameter Index}
    (family : CanonicalNormalCorrectionFamily Parameter Index)
    parameter candidate →
  Solution (problem family parameter) candidate →
  ∀ coordinate →
    candidate coordinate ≡ correction family parameter coordinate
canonicalCorrectionIsUnique family parameter candidate candidateSol =
  quarterContractiveNormalCorrectionUnique
    (problem family parameter)
    candidate
    (correction family parameter)
    candidateSol
    (solves family parameter)

cmp109QuarterContractiveNormalCorrectionUniquenessLevel : ProofLevel
cmp109QuarterContractiveNormalCorrectionUniquenessLevel = machineChecked

cmp109CanonicalNormalCorrectionFamilyLevel : ProofLevel
cmp109CanonicalNormalCorrectionFamilyLevel = machineChecked
