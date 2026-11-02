module DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact where

------------------------------------------------------------------------
-- K04d: REUSE THE ORIGINAL BISHOP DIRICHLET/BASEL MAJORANT OWNER.
--
-- This is NOT a new abstract summation authority. The literal
-- existing BishopBaselReciprocalSquareConvergenceExact supplies
-- sum_{n >= 1} 1/n^2; EllipticDirichletBaselMajorantExact already
-- compiles an eventual |a_n| <= 1/(n+1)^2 into native Bishop
-- convergence. Apply the same comparison independently to both
-- coordinates of a literal complex Dirichlet term family.
--
-- Finite stages and limits are built using the original Bishop
-- Sequence.SeriesOf and Sequence.lim on the original real carrier.
-- The implementation is independent of the intended future exp/log
-- n^(-s), so a real source must still identify each term with its
-- actual logarithmic/exponential construction and prove the
-- all-index local majorant. In particular, the generic original
-- RiemannAnalyticSubstrate does not define its own n^(-s) terms,
-- and Meromorphic is opaque. No zero/sieve/eta/automorphic theorem
-- may be substituted for this same-object obligation.
--
-- Historical origins: Dirichlet (19th c.), Riemann (1859),
-- Basel reciprocal-square majorant, Bishop/Bridges (1985),
-- Zachary Murray (2022, arXiv:2205.08354).
-- Code ownership: original DASHI BishopBasel... and
-- EllipticDirichletBaselMajorantExact, original Bishop Real/Sequence;
-- new composition is DASHI's, source-written / kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Mathematics.Automorphic.EllipticDirichletBaselMajorantExact as Majorant
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext

-- The function is a literal Nat-indexed complex series on the
-- ORIGINAL Bishop Cartesian complex, not the legacy constructed-real
-- or an unrelated automorphic L-function carrier.
BishopDirichletTermFamily : Set
BishopDirichletTermFamily = BC.BishopComplex → Nat → BC.BishopComplex

realTerm : BishopDirichletTermFamily → BC.BishopComplex → Nat → R.ℝ
realTerm term s n = BC.re (term s n)

imagTerm : BishopDirichletTermFamily → BC.BishopComplex → Nat → R.ℝ
imagTerm term s n = BC.im (term s n)

dirichletPartial :
  BishopDirichletTermFamily → BC.BishopComplex → Nat →
  BC.BishopComplex
dirichletPartial term s n =
  BC.bishop-complex
    (Seq.SeriesOf (realTerm term s) n)
    (Seq.SeriesOf (imagTerm term s) n)

-- Local pointwise comparison hypotheses. Constructing n^(-s) and
-- proving these facts in a sigma>=2 region is the remaining TERM gate;
-- the convergence compiler below is already an original repo theorem.
record BishopDirichletBaselMajorantAt
  (term : BishopDirichletTermFamily)
  (s : BC.BishopComplex) : Set where
  field
    dominationStart : Nat
    realDomination :
      (n : Nat) → dominationStart ≤ n →
      R._≤_
        (R.∣_∣ (realTerm term s n))
        (Basel.baselTerm n)
    imagDomination :
      (n : Nat) → dominationStart ≤ n →
      R._≤_
        (R.∣_∣ (imagTerm term s n))
        (Basel.baselTerm n)

open BishopDirichletBaselMajorantAt public

realDirichletConvergent :
  (term : BishopDirichletTermFamily) (s : BC.BishopComplex) →
  BishopDirichletBaselMajorantAt term s →
  Seq._isConvergent (Seq.SeriesOf (realTerm term s))
realDirichletConvergent term s bound =
  Majorant.baselDominatedDirichletSeriesConvergent
    (realTerm term s)
    (dominationStart bound)
    (realDomination bound)

imagDirichletConvergent :
  (term : BishopDirichletTermFamily) (s : BC.BishopComplex) →
  BishopDirichletBaselMajorantAt term s →
  Seq._isConvergent (Seq.SeriesOf (imagTerm term s))
imagDirichletConvergent term s bound =
  Majorant.baselDominatedDirichletSeriesConvergent
    (imagTerm term s)
    (dominationStart bound)
    (imagDomination bound)

-- The actual Bishop-complex infinite series value.
dirichletValue :
  (term : BishopDirichletTermFamily) (s : BC.BishopComplex) →
  (bound : BishopDirichletBaselMajorantAt term s) →
  BC.BishopComplex
dirichletValue term s bound =
  BC.bishop-complex
    (Seq.lim (realDirichletConvergent term s bound))
    (Seq.lim (imagDirichletConvergent term s bound))

-- This is a genuine CONSTRUCTIVE convergence theorem on BOTH original
-- Bishop coordinate sequences, not a claim about an abstract Set field.
dirichletPartialConverges :
  (term : BishopDirichletTermFamily) (s : BC.BishopComplex) →
  (bound : BishopDirichletBaselMajorantAt term s) →
  (Seq._ConvergesTo_
    (λ n → BC.re (dirichletPartial term s n))
    (BC.re (dirichletValue term s bound)))
  ×
  (Seq._ConvergesTo_
    (λ n → BC.im (dirichletPartial term s n))
    (BC.im (dirichletValue term s bound)))
dirichletPartialConverges term s bound =
  proj₂ (realDirichletConvergent term s bound)
  ,
  proj₂ (imagDirichletConvergent term s bound)

------------------------------------------------------------------------
-- K04d COHERENCE: THE BISHOP LIMIT IS INDEPENDENT OF THE PROOF
-- OF BASEL DOMINATION.
--
-- A Dirichlet-series value is selected by Sequence.lim from a
-- convergence witness. Two legitimate witnesses may have different
-- dominationStart indices and different inequality proofs. The
-- original Bishop uniqueness-of-limits theorem proves that the
-- resulting complex values agree in BOTH actual Bishop coordinates.
-- No proof irrelevance axiom, opaque analytic function or new
-- summation mechanism is used.
------------------------------------------------------------------------

dirichletRealValueIndependentOfMajorant :
  (term : BishopDirichletTermFamily)
  (s : BC.BishopComplex)
  (first second : BishopDirichletBaselMajorantAt term s) →
  R._≃_
    (BC.re (dirichletValue term s first))
    (BC.re (dirichletValue term s second))
dirichletRealValueIndependentOfMajorant term s first second =
  Seq.uniqueness-of-limits
    (proj₂ (realDirichletConvergent term s first))
    (proj₂ (realDirichletConvergent term s second))

dirichletImagValueIndependentOfMajorant :
  (term : BishopDirichletTermFamily)
  (s : BC.BishopComplex)
  (first second : BishopDirichletBaselMajorantAt term s) →
  R._≃_
    (BC.im (dirichletValue term s first))
    (BC.im (dirichletValue term s second))
dirichletImagValueIndependentOfMajorant term s first second =
  Seq.uniqueness-of-limits
    (proj₂ (imagDirichletConvergent term s first))
    (proj₂ (imagDirichletConvergent term s second))

dirichletValueIndependentOfMajorant :
  (term : BishopDirichletTermFamily)
  (s : BC.BishopComplex)
  (first second : BishopDirichletBaselMajorantAt term s) →
  (R._≃_
    (BC.re (dirichletValue term s first))
    (BC.re (dirichletValue term s second)))
  ×
  (R._≃_
    (BC.im (dirichletValue term s first))
    (BC.im (dirichletValue term s second)))
dirichletValueIndependentOfMajorant term s first second =
  dirichletRealValueIndependentOfMajorant term s first second
  ,
  dirichletImagValueIndependentOfMajorant term s first second

------------------------------------------------------------------------
-- K04d SAME-OBJECT EXTENSIONALITY: source terms, not names.
-- Once two independently constructed Dirichlet term families are
-- pointwise equivalent on the SAME Bishop analytic argument, the
-- original finite-series extensionality theorem identifies their
-- Bishop limits. This is the exact bridge required to weld
-- exp(-s log n) to a separately given zeta half-plane series.
-- Neither term equality nor the Basel majorants are fabricated here.
dirichletValuesRespectTermwiseEquality :
  (left right : BishopDirichletTermFamily)
  (s : BC.BishopComplex)
  (leftBound : BishopDirichletBaselMajorantAt left s)
  (rightBound : BishopDirichletBaselMajorantAt right s) →
  ((n : Nat) →
    R._≃_ (realTerm left s n) (realTerm right s n)) →
  ((n : Nat) →
    R._≃_ (imagTerm left s n) (imagTerm right s n)) →
  (R._≃_
    (BC.re (dirichletValue left s leftBound))
    (BC.re (dirichletValue right s rightBound)))
  ×
  (R._≃_
    (BC.im (dirichletValue left s leftBound))
    (BC.im (dirichletValue right s rightBound)))
dirichletValuesRespectTermwiseEquality
    left right s leftBound rightBound realSame imagSame =
  Ext.termwiseEquivalentSeriesHaveEquivalentLimits
    realSame
    (proj₂ (realDirichletConvergent left s leftBound))
    (proj₂ (realDirichletConvergent right s rightBound))
  ,
  Ext.termwiseEquivalentSeriesHaveEquivalentLimits
    imagSame
    (proj₂ (imagDirichletConvergent left s leftBound))
    (proj₂ (imagDirichletConvergent right s rightBound))

------------------------------------------------------------------------
-- The exact Basel series is already present at the INTEGER 2 point.
-- This concrete data is not yet the real-variable ζ(π_M); an actual
-- log/exp n^(-s) model must identify it as one of its fibres.
baselComplexTerm : Nat → BC.BishopComplex
baselComplexTerm n =
  BC.bishop-complex (Basel.baselTerm n) R.0ℝ

baselRealPartial : Nat → R.ℝ
baselRealPartial = Seq.SeriesOf Basel.baselTerm

baselIntegerTwoRealConverges :
  Seq._ConvergesTo_ baselRealPartial Basel.baselLimit
baselIntegerTwoRealConverges =
  proj₂ Basel.baselSeriesConvergent


------------------------------------------------------------------------
-- TRUE INTEGER-TWO DIRICHLET FIBRE.
--
-- This is the actual constructive sum of the literal coefficients
-- 1/(n+1)^2 on the original real carrier, including the zero imaginary
-- component. It is a BASE FIBRE and not yet proof that a separately
-- constructed analytic ζ coincides at s=2 or at Machin pi.
------------------------------------------------------------------------

baselComplexPartial : Nat → BC.BishopComplex
baselComplexPartial n =
  BC.bishop-complex (baselRealPartial n) R.0ℝ

baselIntegerTwoComplexConverges :
  (Seq._ConvergesTo_
    (λ n → BC.re (baselComplexPartial n))
    Basel.baselLimit)
  ×
  (Seq._ConvergesTo_
    (λ n → BC.im (baselComplexPartial n))
    R.0ℝ)
baselIntegerTwoComplexConverges =
  baselIntegerTwoRealConverges
  ,
  Seq.xₙ≃c⇒xₙ→c (λ {(suc n) → RP.≃-refl})

-- Same-object weld with the original Riemann half-plane function.
-- Its evidence MUST be the actual function value and the actual
-- concrete term family, not the opaque ZetaEqualsDirichletSeries Set.
record OriginalHalfPlaneDirichletAgreement
  (functions : BC.BishopComplexAnalyticFunctionLayer)
  (halfPlane : Analytic.ZetaHalfPlaneLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (term : BishopDirichletTermFamily)
  (s : BC.BishopComplex) : Set where
  field
    seriesBound : BishopDirichletBaselMajorantAt term s
    halfPlaneRealIsDirichlet :
      R._≃_
        (BC.re
          (BC.apply functions
            (Analytic.ZetaHalfPlaneLayer.zetaHalfPlane halfPlane) s))
        (BC.re (dirichletValue term s seriesBound))
    halfPlaneImagIsDirichlet :
      R._≃_
        (BC.im
          (BC.apply functions
            (Analytic.ZetaHalfPlaneLayer.zetaHalfPlane halfPlane) s))
        (BC.im (dirichletValue term s seriesBound))

open OriginalHalfPlaneDirichletAgreement public

module AtOriginalCompletedZeta
  (functions : BC.BishopComplexAnalyticFunctionLayer)
  (gamma : Analytic.GammaMellinLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (halfPlane : Analytic.ZetaHalfPlaneLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (completed : Analytic.CompletedRiemannZeta
    (BC.bishopComplexAnalyticCarrier functions) gamma halfPlane)
  (term : BishopDirichletTermFamily)
  where

  originalZetaValue : BC.BishopComplex → BC.BishopComplex
  originalZetaValue s =
    BC.apply functions (Analytic.CompletedRiemannZeta.zeta completed) s

  -- Two paths at the SAME original s: original completed ζ via
  -- original agreesWithHalfPlane, and the concrete Bishop summation.
  originalCompletedZetaRealAgreesWithDirichlet :
    (s : BC.BishopComplex) →
    Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne halfPlane s →
    (agreement : OriginalHalfPlaneDirichletAgreement
      functions halfPlane term s) →
    R._≃_
      (BC.re (originalZetaValue s))
      (BC.re (dirichletValue term s (seriesBound agreement)))
  originalCompletedZetaRealAgreesWithDirichlet s domain agreement =
    RP.≃-trans
      (subst
        (λ value → R._≃_ (BC.re (originalZetaValue s)) value)
        (cong BC.re
          (Analytic.CompletedRiemannZeta.agreesWithHalfPlane
            completed s domain))
        RP.≃-refl)
      (halfPlaneRealIsDirichlet agreement)

  originalCompletedZetaImagAgreesWithDirichlet :
    (s : BC.BishopComplex) →
    Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne halfPlane s →
    (agreement : OriginalHalfPlaneDirichletAgreement
      functions halfPlane term s) →
    R._≃_
      (BC.im (originalZetaValue s))
      (BC.im (dirichletValue term s (seriesBound agreement)))
  originalCompletedZetaImagAgreesWithDirichlet s domain agreement =
    RP.≃-trans
      (subst
        (λ value → R._≃_ (BC.im (originalZetaValue s)) value)
        (cong BC.im
          (Analytic.CompletedRiemannZeta.agreesWithHalfPlane
            completed s domain))
        RP.≃-refl)
      (halfPlaneImagIsDirichlet agreement)

------------------------------------------------------------------------
-- COMPLETE ORIGINAL BISHOP INTEGER-2 BASEL INSTANCE.
--
-- The previously generic comparison witness is now constructed for
-- the ACTUAL rational source terms, and its compiled limit is proved
-- equivalent to the original Basel owner (rather than a second
-- symbolic "zeta value"). This is the one special analytic fibre
-- which the repository can already realize without Bishop log/exp.
------------------------------------------------------------------------

baselIntegerTwoTermFamily : BishopDirichletTermFamily
baselIntegerTwoTermFamily s n = baselComplexTerm n

zeroAbsBelowBasel :
  ∀ n →
  R._≤_
    (R.∣ R.0ℝ ∣)
    (Basel.baselTerm n)
zeroAbsBelowBasel n =
  RP.≤-respˡ-≃
    (RP.≃-symm
      (RP.nonNegx⇒∣x∣≃x
        (RP.0≤x⇒nonNegx RP.≤-refl)))
    (RP.nonNegx⇒0≤x (Basel.baselTermNonnegative n))

baselIntegerTwoMajorant :
  (s : BC.BishopComplex) →
  BishopDirichletBaselMajorantAt baselIntegerTwoTermFamily s
baselIntegerTwoMajorant s = record
  { dominationStart = zero
  ; realDomination = λ n _ →
      RP.≤-reflexive (Basel.absoluteBaselTerm n)
  ; imagDomination = λ n _ → zeroAbsBelowBasel n
  }

baselCompiledRealLimitIsOriginal :
  (s : BC.BishopComplex) →
  R._≃_
    (BC.re
      (dirichletValue
        baselIntegerTwoTermFamily s
        (baselIntegerTwoMajorant s)))
    Basel.baselLimit
baselCompiledRealLimitIsOriginal s =
  Seq.uniqueness-of-limits
    (proj₂
      (realDirichletConvergent
        baselIntegerTwoTermFamily s
        (baselIntegerTwoMajorant s)))
    baselIntegerTwoRealConverges

baselCompiledImagLimitIsZero :
  (s : BC.BishopComplex) →
  R._≃_
    (BC.im
      (dirichletValue
        baselIntegerTwoTermFamily s
        (baselIntegerTwoMajorant s)))
    R.0ℝ
baselCompiledImagLimitIsZero s =
  Seq.uniqueness-of-limits
    (proj₂
      (imagDirichletConvergent
        baselIntegerTwoTermFamily s
        (baselIntegerTwoMajorant s)))
    (Seq.xₙ≃c⇒xₙ→c
      (λ {(suc n) → RP.≃-refl}))
