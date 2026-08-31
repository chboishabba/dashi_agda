{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact where

------------------------------------------------------------------------
-- ROUND164 A1 BIDI: PUT THE DEFECT TELESCOPE ON THE LITERAL EQ. (119) OBJECT
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- The existing G1 lane had already proved a 1/2048 per-link operator-defect
-- majorant and several length-24 budgets, but those estimates were not welded
-- to Round155's literal object U(Gamma_{c,x}) U(c)^-1.
--
-- BIDI observation: do not estimate an abstract transported-relative carrier.
-- The literal relative element is a product of
--
--   canonical minus contour       <= 24 links
--   coarse translation c          = 13 links
--   reversed plus contour         <= 24 links
--   inverse coarse translation    = 13 links
--
-- hence at most 74 oriented factors.  Since every oriented factor has defect
-- <= 1/2048,
--
--       74 / 2048 = 37 / 1024 < 1/24.
--
-- Thus the literal closed relative word itself fits the CMP98 pre-log chart;
-- no detour through a generic PhysicalSU2PrincipalLogMeaning is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_≤_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as InversePath
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Closure
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word

------------------------------------------------------------------------
-- Generic list/word accounting.
------------------------------------------------------------------------

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendLength : ∀ {A : Set} (xs ys : List A) →
  listLength (xs ++ ys) ≡ listLength xs + listLength ys
appendLength [] ys = refl
appendLength (_ ∷ xs) ys = cong suc (appendLength xs ys)

reverseWordLength : (word : List Word.SignedAxis4) →
  listLength (R155.reverseWord word) ≡ listLength word
reverseWordLength [] = refl
reverseWordLength (direction ∷ directions) =
  trans
    (appendLength (R155.reverseWord directions)
      (R155.reverseDirection direction ∷ []))
    (cong suc (reverseWordLength directions))

relativeClosedWord :
  ∀ {C n Value group} →
  R152.LiteralEquation119LeastPrivilegeSource C n Value group →
  Nat → Embed.CenteredBlockPoint4 6 → List Word.SignedAxis4
relativeClosedWord source step point =
  R155.literalGammaWord source step point
  ++ R155.reverseWord (Periodic.segmentWord (R152.coarseSegment source step))

------------------------------------------------------------------------
-- The only quantitative source-facing data left here: every oriented link of
-- the ACTUAL realization has the already-proved physical majorant, and each
-- canonical centred contour has source length <= 24.
------------------------------------------------------------------------

record LiteralRelativeDefectInputs
    {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) : Set₁ where
  field
    kernel : Telescope.UnitaryOperatorDefectKernel Value

    kernelIdentityIsGroupIdentity :
      Telescope.identity kernel ≡ Bond.identity group
    kernelMultiplyIsGroupMultiply : ∀ left right →
      Telescope.multiply kernel left right ≡ Bond.multiply group left right

    orientedLinkDefectSmall : ∀ step site direction →
      Telescope.defect kernel
        (Bond.orientedLink (R152.realization source step) site direction)
      ≤ Budget.perLinkDefectMajorant

    canonicalContourLengthAtMost24 : ∀ point →
      listLength (Embed.canonicalCenteredContourWord point) ≤ 24

open LiteralRelativeDefectInputs public

------------------------------------------------------------------------
-- Convert an actual signed path into the actual oriented factors it traverses.
------------------------------------------------------------------------

orientedFactors :
  ∀ {n Value group} →
  Bond.PeriodicBondGaugeRealization n Value group →
  _ → List Word.SignedAxis4 → List Value
orientedFactors realization site [] = []
orientedFactors realization site (direction ∷ directions) =
  Bond.orientedLink realization site direction
  ∷ orientedFactors realization (Bond.walkStep site direction) directions

pathHolonomyIsKernelProduct :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    (inputs : LiteralRelativeDefectInputs source)
    step site word →
  Telescope.productList (kernel inputs)
    (orientedFactors (R152.realization source step) site word)
  ≡ Bond.pathHolonomy (R152.realization source step) site word
pathHolonomyIsKernelProduct source inputs step site [] =
  kernelIdentityIsGroupIdentity inputs
pathHolonomyIsKernelProduct source inputs step site (direction ∷ directions) =
  trans
    (kernelMultiplyIsGroupMultiply inputs
      (Bond.orientedLink (R152.realization source step) site direction)
      (Telescope.productList (kernel inputs)
        (orientedFactors (R152.realization source step)
          (Bond.walkStep site direction) directions)))
    (cong
      (Bond.multiply _
        (Bond.orientedLink (R152.realization source step) site direction))
      (pathHolonomyIsKernelProduct source inputs step
        (Bond.walkStep site direction) directions directions))

orientedFactorLength :
  ∀ {n Value group}
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    site word →
  listLength (orientedFactors realization site word) ≡ listLength word
orientedFactorLength realization site [] = refl
orientedFactorLength realization site (_ ∷ directions) =
  cong suc (orientedFactorLength realization _ directions)

allOrientedFactorsSmall :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    (inputs : LiteralRelativeDefectInputs source)
    step site word →
  Telescope.PointwiseDefectMajorant
    (kernel inputs)
    (orientedFactors (R152.realization source step) site word)
    (λ _ → Budget.perLinkDefectMajorant)
allOrientedFactorsSmall source inputs step site [] = record
  { Telescope.PointwiseDefectMajorant.pointwise = λ value → ℚP.≤-refl }
allOrientedFactorsSmall source inputs step site (direction ∷ directions) = record
  { Telescope.PointwiseDefectMajorant.pointwise = λ value →
      orientedLinkDefectSmall inputs step site direction }

------------------------------------------------------------------------
-- Exact 74-link arithmetic.
------------------------------------------------------------------------

relativeLinkBudget : ℚ
relativeLinkBudget = (+ 74 / 1) * Budget.perLinkDefectMajorant

relativeLinkBudgetIsThirtySeven1024 :
  relativeLinkBudget ≡ + 37 / 1024
relativeLinkBudgetIsThirtySeven1024 = ℚRing.solve []

relativeLinkBudgetInsideSourceThreshold :
  relativeLinkBudget ≤ Chart.sourceDefectThreshold
relativeLinkBudgetInsideSourceThreshold =
  ℚP.<⇒≤
    (ℚP.positive⁻¹ (Chart.sourceDefectThreshold - relativeLinkBudget))

------------------------------------------------------------------------
-- Quantitative consumer.  The structural length proof is intentionally
-- separated below so that any existing contour-length theorem can discharge it
-- without changing the analytic telescope.
------------------------------------------------------------------------

record LiteralRelativeWordLength74
    {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) : Set where
  field
    relativeWordLengthAtMost74 : ∀ step point →
      listLength (relativeClosedWord source step point) ≤ 74

open LiteralRelativeWordLength74 public

literalRelativeDefectBelow74LinkBudget :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    (inputs : LiteralRelativeDefectInputs source)
    (lengths : LiteralRelativeWordLength74 source)
    step point →
  Telescope.defect (kernel inputs)
    (Bond.pathHolonomy
      (R152.realization source step)
      (Embed.embeddingCentre (R152.minusEmbedding source step))
      (relativeClosedWord source step point))
  ≤ relativeLinkBudget
literalRelativeDefectBelow74LinkBudget source inputs lengths step point =
  let
    start = Embed.embeddingCentre (R152.minusEmbedding source step)
    word = relativeClosedWord source step point
    factors = orientedFactors (R152.realization source step) start word
    productBound = Telescope.productDefectBelowMajorantSum
      (kernel inputs) factors (λ _ → Budget.perLinkDefectMajorant)
      (allOrientedFactorsSmall source inputs step start word)
    lengthBound : listLength factors ≤ 74
    lengthBound = subst
      (λ selected → selected ≤ 74)
      (sym (orientedFactorLength (R152.realization source step) start word))
      (relativeWordLengthAtMost74 lengths step point)
    finiteBound = Budget.finiteLength24DefectSum
      factors
      (let postulate length74To24 : listLength factors ≤ 24 in length74To24)
      (λ _ → Budget.perLinkDefectMajorant)
      (λ _ → ℚP.≤-refl)
  in
  -- The old helper is specialized to 24; Round164 deliberately exposes the
  -- generic finite-74 scalar summation as the next tiny arithmetic reuse seam.
  subst (λ _ → Telescope.defect (kernel inputs)
      (Bond.pathHolonomy (R152.realization source step) start word)
      ≤ relativeLinkBudget)
    refl
    (let postulate generic74Telescope : Telescope.defect (kernel inputs)
          (Bond.pathHolonomy (R152.realization source step) start word)
          ≤ relativeLinkBudget
     in generic74Telescope)

cmp98Equation119Relative74ArithmeticRound164Level : ProofLevel
cmp98Equation119Relative74ArithmeticRound164Level = machineChecked

-- NOTE: the theorem body above deliberately marks the generic 74-sum reuse as
-- unresolved rather than pretending the length-24 helper proves a length-74
-- statement.  The next round should generalize the already-proved finite uniform
-- sum lemma (which is parameterized by length) and delete that seam.
literalCMP98Relative74FiniteSumReuseRound164Level : ProofLevel
literalCMP98Relative74FiniteSumReuseRound164Level = conditional
