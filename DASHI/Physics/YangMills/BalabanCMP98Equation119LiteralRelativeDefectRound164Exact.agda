{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact where

------------------------------------------------------------------------
-- ROUND164 A1 BIDI: PUT THE DEFECT TELESCOPE ON THE LITERAL EQ. (119) OBJECT
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- Existing G1 work already gives the physical per-link majorant 1/2048.  The
-- remaining mistake was architectural: those estimates were not applied to the
-- literal Round155 object U(Gamma_{c,x}) U(c)^-1.
--
-- On the canonical minimal lane:
--   minus centred contour       <= 24 links
--   coarse translation c          = 13 links
--   reversed plus contour       <= 24 links
--   inverse coarse translation    = 13 links
-- so the literal closed relative word has length <= 74.  Therefore
--
--       || U(Gamma_{c,x}) U(c)^-1 - I ||
--          <= 74 / 2048
--           = 37 / 1024
--           < 1 / 24.
--
-- This round proves the finite telescope directly on the repository's actual
-- pathHolonomy recursion.  No abstract transported-relative carrier and no
-- pointwise principal-image receipt is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (_++_)
open import Data.Nat.Base using (_≤_; _+_; z≤n; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _/_)
open Data.Rational.Base using () renaming (_+_ to _+ℚ_; _-_ to _-ℚ_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanP33CMP109MinimalPathStageBudgetExact as PathBudget
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word

listLength : ∀ {A : Set} → List A → Nat
listLength = Periodic.listLength

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
    (trans
      (cong (λ n → n + 1) (reverseWordLength directions))
      (ℕP.+-comm (listLength directions) 1))

relativeClosedWord :
  ∀ {C n Value group} →
  R158.CanonicalL13Equation119Source C n Value group →
  Nat → Centered.CenteredBlockPoint4 6 → List Word.SignedAxis4
relativeClosedWord source step point =
  R155.literalGammaWord (R158.asRound152Source source) step point
  ++ R155.reverseWord
      (Periodic.segmentWord
        (R152.coarseSegment (R158.asRound152Source source) step))

record LiteralRelativeDefectInputs
    {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group) : Set₁ where
  field
    kernel : Telescope.UnitaryOperatorDefectKernel Value

    kernelIdentityIsGroupIdentity :
      Telescope.identity kernel ≡ Bond.identity group

    kernelMultiplyIsGroupMultiply : ∀ left right →
      Telescope.multiply kernel left right ≡ Bond.multiply group left right

    orientedLinkDefectSmall : ∀ step site direction →
      Telescope.defect kernel
        (Bond.orientedLink
          (R152.realization (R158.asRound152Source source) step)
          site direction)
      ≤ Budget.perLinkDefectMajorant

    canonicalContourLengthAtMost24 : ∀ point →
      listLength (Embed.canonicalCenteredContourWord point) ≤ 24

open LiteralRelativeDefectInputs public

coarseWordLengthIs13 :
  ∀ {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    step →
  listLength
    (Periodic.segmentWord
      (R152.coarseSegment (R158.asRound152Source source) step))
  ≡ 13
coarseWordLengthIs13 source step =
  trans
    (Periodic.segmentWordLength
      (R152.coarseSegment (R158.asRound152Source source) step))
    (cong Contours.count
      (R158.round152CoarseSegmentCountIsL source step))

literalGammaLengthAtMost61 :
  ∀ {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : LiteralRelativeDefectInputs source)
    step point →
  listLength
    (R155.literalGammaWord (R158.asRound152Source source) step point)
  ≤ 61
literalGammaLengthAtMost61 source inputs step point =
  let
    contour = Embed.canonicalCenteredContourWord point
    coarse = Periodic.segmentWord
      (R152.coarseSegment (R158.asRound152Source source) step)

    contourBound = canonicalContourLengthAtMost24 inputs point
    reverseBound : listLength (R155.reverseWord contour) ≤ 24
    reverseBound = subst
      (λ selected → selected ≤ 24)
      (sym (reverseWordLength contour))
      contourBound

    coarseBound : listLength coarse ≤ 13
    coarseBound = subst
      (λ selected → selected ≤ 13)
      (sym (coarseWordLengthIs13 source step))
      ℕP.≤-refl

    sumBound :
      listLength contour
      + (listLength coarse + listLength (R155.reverseWord contour))
      ≤ 24 + (13 + 24)
    sumBound = ℕP.+-mono-≤ contourBound
      (ℕP.+-mono-≤ coarseBound reverseBound)
  in
  subst
    (λ selected → selected ≤ 61)
    (sym
      (trans
        (appendLength contour (coarse ++ R155.reverseWord contour))
        (cong (λ n → listLength contour + n)
          (appendLength coarse (R155.reverseWord contour)))))
    sumBound

relativeClosedWordLengthAtMost74 :
  ∀ {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : LiteralRelativeDefectInputs source)
    step point →
  listLength (relativeClosedWord source step point) ≤ 74
relativeClosedWordLengthAtMost74 source inputs step point =
  let
    gamma = R155.literalGammaWord (R158.asRound152Source source) step point
    coarse = Periodic.segmentWord
      (R152.coarseSegment (R158.asRound152Source source) step)

    gammaBound = literalGammaLengthAtMost61 source inputs step point
    reverseCoarseBound : listLength (R155.reverseWord coarse) ≤ 13
    reverseCoarseBound = subst
      (λ selected → selected ≤ 13)
      (sym (reverseWordLength coarse))
      (subst
        (λ selected → selected ≤ 13)
        (sym (coarseWordLengthIs13 source step))
        ℕP.≤-refl)

    sumBound :
      listLength gamma + listLength (R155.reverseWord coarse) ≤ 61 + 13
    sumBound = ℕP.+-mono-≤ gammaBound reverseCoarseBound
  in
  subst
    (λ selected → selected ≤ 74)
    (sym (appendLength gamma (R155.reverseWord coarse)))
    sumBound

pathHolonomyDefectBelowLengthBudget :
  ∀ {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : LiteralRelativeDefectInputs source)
    step site word bound →
  listLength word ≤ bound →
  Telescope.defect (kernel inputs)
    (Bond.pathHolonomy
      (R152.realization (R158.asRound152Source source) step)
      site word)
  ≤ Sums.natAsRational bound * Budget.perLinkDefectMajorant
pathHolonomyDefectBelowLengthBudget source inputs step site [] bound lengthBound =
  subst
    (λ selected →
      Telescope.defect (kernel inputs) selected
      ≤ Sums.natAsRational bound * Budget.perLinkDefectMajorant)
    (kernelIdentityIsGroupIdentity inputs)
    (subst
      (λ lower →
        lower ≤ Sums.natAsRational bound * Budget.perLinkDefectMajorant)
      (sym (Telescope.identityDefectZero (kernel inputs)))
      (PathBudget.productNonnegative
        (Sums.natAsRational bound)
        Budget.perLinkDefectMajorant
        (PathBudget.natAsRationalNonnegative bound)
        Budget.perLinkDefectMajorantNonnegative))
pathHolonomyDefectBelowLengthBudget source inputs step site
    (direction ∷ directions) zero ()
pathHolonomyDefectBelowLengthBudget source inputs step site
    (direction ∷ directions) (suc bound) (s≤s tailLength) =
  let
    realization = R152.realization (R158.asRound152Source source) step
    head = Bond.orientedLink realization site direction
    tail = Bond.pathHolonomy realization (Bond.walkStep site direction) directions

    productBound :
      Telescope.defect (kernel inputs)
        (Telescope.multiply (kernel inputs) head tail)
      ≤ Telescope.defect (kernel inputs) head
        +ℚ Telescope.defect (kernel inputs) tail
    productBound = Telescope.productDefectTriangle (kernel inputs) head tail

    headTailBound :
      Telescope.defect (kernel inputs) head
        +ℚ Telescope.defect (kernel inputs) tail
      ≤ Budget.perLinkDefectMajorant
        +ℚ (Sums.natAsRational bound * Budget.perLinkDefectMajorant)
    headTailBound = ℚP.+-mono-≤
      (orientedLinkDefectSmall inputs step site direction)
      (pathHolonomyDefectBelowLengthBudget
        source inputs step (Bond.walkStep site direction)
        directions bound tailLength)

    successorBound :
      Telescope.defect (kernel inputs)
        (Telescope.multiply (kernel inputs) head tail)
      ≤ Sums.natAsRational (suc bound) * Budget.perLinkDefectMajorant
    successorBound =
      subst
        (λ upper →
          Telescope.defect (kernel inputs)
            (Telescope.multiply (kernel inputs) head tail)
          ≤ upper)
        (PathBudget.successorBudgetExact bound Budget.perLinkDefectMajorant)
        (ℚP.≤-trans productBound headTailBound)
  in
  subst
    (λ selected →
      Telescope.defect (kernel inputs) selected
      ≤ Sums.natAsRational (suc bound) * Budget.perLinkDefectMajorant)
    (kernelMultiplyIsGroupMultiply inputs head tail)
    successorBound

relativeLinkBudget : ℚ
relativeLinkBudget = (+ 74 / 1) * Budget.perLinkDefectMajorant

relativeLinkBudgetIsThirtySeven1024 :
  relativeLinkBudget ≡ + 37 / 1024
relativeLinkBudgetIsThirtySeven1024 = ℚRing.solve []

nat74BudgetIsRelativeLinkBudget :
  Sums.natAsRational 74 * Budget.perLinkDefectMajorant
  ≡ relativeLinkBudget
nat74BudgetIsRelativeLinkBudget = ℚRing.solve []

relativeLinkBudgetInsideSourceThreshold :
  relativeLinkBudget ≤ Chart.sourceDefectThreshold
relativeLinkBudgetInsideSourceThreshold =
  ℚP.<⇒≤
    (ℚP.positive⁻¹ (Chart.sourceDefectThreshold -ℚ relativeLinkBudget))

literalRelativeClosedPathDefectBelowSourceThreshold :
  ∀ {C n Value group}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : LiteralRelativeDefectInputs source)
    step point →
  Telescope.defect (kernel inputs)
    (Bond.pathHolonomy
      (R152.realization (R158.asRound152Source source) step)
      (Embed.embeddingCentre
        (R152.minusEmbedding (R158.asRound152Source source) step))
      (relativeClosedWord source step point))
  ≤ Chart.sourceDefectThreshold
literalRelativeClosedPathDefectBelowSourceThreshold source inputs step point =
  let
    bound74 = pathHolonomyDefectBelowLengthBudget
      source inputs step
      (Embed.embeddingCentre
        (R152.minusEmbedding (R158.asRound152Source source) step))
      (relativeClosedWord source step point)
      74
      (relativeClosedWordLengthAtMost74 source inputs step point)

    boundRelative :
      Telescope.defect (kernel inputs)
        (Bond.pathHolonomy
          (R152.realization (R158.asRound152Source source) step)
          (Embed.embeddingCentre
            (R152.minusEmbedding (R158.asRound152Source source) step))
          (relativeClosedWord source step point))
      ≤ relativeLinkBudget
    boundRelative = subst
      (λ upper →
        Telescope.defect (kernel inputs)
          (Bond.pathHolonomy
            (R152.realization (R158.asRound152Source source) step)
            (Embed.embeddingCentre
              (R152.minusEmbedding (R158.asRound152Source source) step))
            (relativeClosedWord source step point))
        ≤ upper)
      nat74BudgetIsRelativeLinkBudget
      bound74
  in
  ℚP.≤-trans boundRelative relativeLinkBudgetInsideSourceThreshold

cmp98Equation119Relative74ArithmeticRound164Level : ProofLevel
cmp98Equation119Relative74ArithmeticRound164Level = machineChecked

cmp98Equation119LiteralClosedPathDefectRound164Level : ProofLevel
cmp98Equation119LiteralClosedPathDefectRound164Level = machineChecked

-- The remaining SAME-OBJECT step is purely group/path algebra: prove that this
-- closed path holonomy is exactly Round155.relativeContourElement.  R161 already
-- supplies the inverse-path theorem needed for the final coarse reverse leg.
literalCMP98ClosedPathIsRound155RelativeElementRound164Level : ProofLevel
literalCMP98ClosedPathIsRound155RelativeElementRound164Level = conditional
