module DASHI.Analysis.BishopDirichletUniformBaselTailsExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY: ONE EXPLICIT CUTOFF FOR THE WHOLE DIRICHLET REGION.
--
-- No new summation, limit, norm or analytic-domain machinery.
-- We reuse the PINNED vendor/bishop Sequence.∑-triangle-inequality,
-- Sequence.∑-mono-≤ and Sequence.cauchyConvergenceTest-if for the
-- previously constructed Basel series. The same cutoff works for
-- every member of any region whose ORIGINAL Bishop source terms
-- satisfy the actual all-index Basel domination.
--
-- This is a genuine uniform finite-tail theorem, but not by itself
-- local uniform convergence to the sum or continuity of the original
-- opaque zeta function. Those need the term-domination and same-object
-- identification at the actual Machin neighborhood.
--
-- Attribution: Bishop/Bridges, Murray 2022, pinned viktorcsimma/bishop;
-- DASHI Basel and EllipticDirichletBaselMajorantExact owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base as Nat using (_≤_; _≥_; NonZero)
import Data.Nat.Properties as NatP
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; _/_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet

------------------------------------------------------------------------
-- This Nat cutoff is an actual output of the vendored Bishop Cauchy
-- convergence test applied to the proved original Basel series.
------------------------------------------------------------------------

baselUniformTailCutoff :
  (k : Nat) → .{{_ : NonZero k}} → Nat
baselUniformTailCutoff k =
  suc (proj₁
    (Seq.cauchyConvergenceTest-if
      Basel.baselTerm Basel.baselSeriesConvergent k))

orderedBaselDominatedTailSmall :
  (terms : Nat → R.ℝ) →
  ((index : Nat) →
    R._≤_ (R.∣ terms index ∣) (Basel.baselTerm index)) →
  (k : Nat) → .{{_ : NonZero k}} →
  (m n : Nat) →
  m ≤ n →
  m ≥ baselUniformTailCutoff k →
  n ≥ baselUniformTailCutoff k →
  R._≤_
    (R.∣ Seq.∑ terms m n ∣)
    (R._⋆ (+ 1 / k))
orderedBaselDominatedTailSmall terms dominated k m n m≤n mPast nPast =
  RP.≤-trans
    (Seq.∑-triangle-inequality terms m n m≤n)
    (RP.≤-trans
      (Seq.∑-mono-≤ dominated m n m≤n)
      (RP.≤-trans
        (RP.x≤∣x∣ {x = Seq.∑ Basel.baselTerm m n})
        (proj₂
          (Seq.cauchyConvergenceTest-if
            Basel.baselTerm Basel.baselSeriesConvergent k)
          m n mPast nPast)))

-- The cauchy test is symmetric in m,n. For n<=m use the original
-- Bishop negate-and-swap finite-sum identity, not an assumed
-- positivity of a reversed finite tail.
baselDominatedFiniteTailSmall :
  (terms : Nat → R.ℝ) →
  ((index : Nat) →
    R._≤_ (R.∣ terms index ∣) (Basel.baselTerm index)) →
  (k : Nat) → .{{_ : NonZero k}} →
  (m n : Nat) →
  m ≥ baselUniformTailCutoff k →
  n ≥ baselUniformTailCutoff k →
  R._≤_
    (R.∣ Seq.∑ terms m n ∣)
    (R._⋆ (+ 1 / k))
baselDominatedFiniteTailSmall terms dominated k m n mPast nPast
    with NatP.≤-total m n
... | inj₁ m≤n =
  orderedBaselDominatedTailSmall
    terms dominated k m n m≤n mPast nPast
... | inj₂ n≤m =
  RP.≤-respˡ-≃
    (RP.≃-trans
      (RP.≃-symm
        (RP.∣-x∣≃∣x∣ {x = Seq.∑ terms m n}))
      (RP.∣-∣-cong (Seq.neg-flips-∑ terms m n)))
    (orderedBaselDominatedTailSmall
      terms dominated k n m n≤m nPast mPast)

------------------------------------------------------------------------
-- One COMMON N(k), independent of s, bounds BOTH actual complex
-- coordinates in the selected region.
------------------------------------------------------------------------

record RegionBaselDomination
  (terms : Dirichlet.BishopDirichletTermFamily)
  (Region : BC.BishopComplex → Set) : Set₁ where
  field
    realEverywhere :
      (s : BC.BishopComplex) → Region s →
      (index : Nat) →
      R._≤_
        (R.∣ Dirichlet.realTerm terms s index ∣)
        (Basel.baselTerm index)
    imagEverywhere :
      (s : BC.BishopComplex) → Region s →
      (index : Nat) →
      R._≤_
        (R.∣ Dirichlet.imagTerm terms s index ∣)
        (Basel.baselTerm index)

open RegionBaselDomination public

regionRealUniformFiniteTail :
  (terms : Dirichlet.BishopDirichletTermFamily) →
  (Region : BC.BishopComplex → Set) →
  RegionBaselDomination terms Region →
  (k : Nat) → .{{_ : NonZero k}} →
  (s : BC.BishopComplex) → Region s →
  (m n : Nat) →
  m ≥ baselUniformTailCutoff k →
  n ≥ baselUniformTailCutoff k →
  R._≤_
    (R.∣ Seq.∑ (Dirichlet.realTerm terms s) m n ∣)
    (R._⋆ (+ 1 / k))
regionRealUniformFiniteTail terms Region bound k s inside m n mPast nPast =
  baselDominatedFiniteTailSmall
    (Dirichlet.realTerm terms s)
    (realEverywhere bound s inside)
    k m n mPast nPast

regionImagUniformFiniteTail :
  (terms : Dirichlet.BishopDirichletTermFamily) →
  (Region : BC.BishopComplex → Set) →
  RegionBaselDomination terms Region →
  (k : Nat) → .{{_ : NonZero k}} →
  (s : BC.BishopComplex) → Region s →
  (m n : Nat) →
  m ≥ baselUniformTailCutoff k →
  n ≥ baselUniformTailCutoff k →
  R._≤_
    (R.∣ Seq.∑ (Dirichlet.imagTerm terms s) m n ∣)
    (R._⋆ (+ 1 / k))
regionImagUniformFiniteTail terms Region bound k s inside m n mPast nPast =
  baselDominatedFiniteTailSmall
    (Dirichlet.imagTerm terms s)
    (imagEverywhere bound s inside)
    k m n mPast nPast


------------------------------------------------------------------------
-- SAME PROOF WITNESS -> POINTWISE COMPLEX DIRICHLET LIMITS.
-- No second convergence authority and no hidden choice of a majorant:
-- uniform region domination contains the exact all-index comparison.
------------------------------------------------------------------------

regionPointwiseMajorant :
  (terms : Dirichlet.BishopDirichletTermFamily) →
  (Region : BC.BishopComplex → Set) →
  (bound : RegionBaselDomination terms Region) →
  (s : BC.BishopComplex) → Region s →
  Dirichlet.BishopDirichletBaselMajorantAt terms s
regionPointwiseMajorant terms Region bound s inside = record
  { Dirichlet.dominationStart = zero
  ; Dirichlet.realDomination = λ index _ →
      realEverywhere bound s inside index
  ; Dirichlet.imagDomination = λ index _ →
      imagEverywhere bound s inside index
  }

regionDirichletValue :
  (terms : Dirichlet.BishopDirichletTermFamily) →
  (Region : BC.BishopComplex → Set) →
  (bound : RegionBaselDomination terms Region) →
  (s : BC.BishopComplex) → Region s →
  BC.BishopComplex
regionDirichletValue terms Region bound s inside =
  Dirichlet.dirichletValue terms s
    (regionPointwiseMajorant terms Region bound s inside)

regionValueConvergesCoordinatewise :
  (terms : Dirichlet.BishopDirichletTermFamily) →
  (Region : BC.BishopComplex → Set) →
  (bound : RegionBaselDomination terms Region) →
  (s : BC.BishopComplex) → (inside : Region s) →
  (Seq._ConvergesTo_
    (λ index →
      BC.re (Dirichlet.dirichletPartial terms s index))
    (BC.re (regionDirichletValue terms Region bound s inside)))
  ×
  (Seq._ConvergesTo_
    (λ index →
      BC.im (Dirichlet.dirichletPartial terms s index))
    (BC.im (regionDirichletValue terms Region bound s inside)))
regionValueConvergesCoordinatewise terms Region bound s inside =
  Dirichlet.dirichletPartialConverges terms s
    (regionPointwiseMajorant terms Region bound s inside)


------------------------------------------------------------------------
-- COMPLETE UNIFORM TO-LIMIT TAIL ESTIMATE, not only finite Cauchy.
--
-- For any *existing actual Bishop convergence witness*, the same
-- all-index Basel cutoff controls |limit - partialSum_N| uniformly
-- over any family of terms dominated by the original Basel series.
--
-- We use original Sequence.∣xₙ∣→∣x₀∣, subsequence convergence,
-- finite sum, and order closure under limits; no extra limiting
-- oracle and no different real carrier. The pointwise limit already
-- exists by the original Bishop comparison theorem.
------------------------------------------------------------------------

partialMinusIsFiniteTail :
  (terms : Nat → R.ℝ) (m n : Nat) →
  R._≃_
    (R._-_ (Seq.SeriesOf terms n) (Seq.SeriesOf terms m))
    (Seq.∑ terms m n)
partialMinusIsFiniteTail terms zero n =
  let open RP.ℝ-Solver
  in solve 1 (λ prefix → prefix ⊖ Κ 0ℚᵘ ⊜ prefix)
     RP.≃-refl (Seq.SeriesOf terms n)
partialMinusIsFiniteTail terms (suc m) n = RP.≃-refl

baselDominatedUniformLimitError :
  (terms : Nat → R.ℝ) →
  (dominated : (index : Nat) →
    R._≤_ (R.∣ terms index ∣) (Basel.baselTerm index)) →
  (convergent : Seq._isConvergent (Seq.SeriesOf terms)) →
  (k : Nat) → .{{_ : NonZero k}} →
  (m : Nat) →
  m ≥ baselUniformTailCutoff k →
  R._≤_
    (R.∣
      R._-_
        (Seq.lim convergent)
        (Seq.SeriesOf terms m)
    ∣)
    (R._⋆ (+ 1 / k))
baselDominatedUniformLimitError
    terms dominated convergent k m mPast =
  let
    cutoff = baselUniformTailCutoff k
    partial = Seq.SeriesOf terms
    limit = Seq.lim convergent
    shifted : Nat → R.ℝ
    shifted n = partial (n + cutoff)

    shiftedConverges : Seq._ConvergesTo_ shifted limit
    shiftedConverges =
      Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
        (Seq.subseq*
          ((λ n → n + cutoff)
          , (λ n → RP.≃-refl)
          , (λ n → NatP.n<1+n (n + cutoff))))
        convergent

    constantNegative : Nat → R.ℝ
    constantNegative n = R.- (partial m)

    constantConverges :
      Seq._isConvergent constantNegative
    constantConverges =
      R.- (partial m)
      , Seq.xₙ≃c⇒xₙ→c
          (λ {(suc n) → RP.≃-refl})

    differenceConverges :
      Seq._ConvergesTo_
        (λ n → R._-_ (shifted n) (partial m))
        (R._-_ limit (partial m))
    differenceConverges =
      Seq.xₙ+yₙ→x₀+y₀
        (limit , shiftedConverges)
        constantConverges

    absConvergent :
      Seq._isConvergent
        (λ n → R.∣ R._-_ (shifted n) (partial m) ∣)
    absConvergent =
      (R.∣ R._-_ limit (partial m) ∣)
      , Seq.∣xₙ∣→∣x₀∣
          ((R._-_ limit (partial m)) , differenceConverges)

    boundEach : (n : Nat) →
      R._≤_
        (R.∣ R._-_ (shifted n) (partial m) ∣)
        (R._⋆ (+ 1 / k))
    boundEach n =
      RP.≤-respˡ-≃
        (RP.∣-∣-cong
          (partialMinusIsFiniteTail terms m (n + cutoff)))
        (baselDominatedFiniteTailSmall
          terms dominated k m (n + cutoff)
          mPast (NatP.m≤n+m cutoff n))
  in
  Seq.xₙ≤y⇒limxₙ≤y
    boundEach
    absConvergent

regionRealUniformLimitError :
  (terms : Dirichlet.BishopDirichletTermFamily) →
  (Region : BC.BishopComplex → Set) →
  (bound : RegionBaselDomination terms Region) →
  (k : Nat) → .{{_ : NonZero k}} →
  (s : BC.BishopComplex) →
  (inside : Region s) →
  (m : Nat) →
  m ≥ baselUniformTailCutoff k →
  R._≤_
    (R.∣
      R._-_
        (BC.re (regionDirichletValue terms Region bound s inside))
        (Seq.SeriesOf (Dirichlet.realTerm terms s) m)
    ∣)
    (R._⋆ (+ 1 / k))
regionRealUniformLimitError terms Region bound k s inside m mPast =
  baselDominatedUniformLimitError
    (Dirichlet.realTerm terms s)
    (realEverywhere bound s inside)
    (Dirichlet.realDirichletConvergent terms s
      (regionPointwiseMajorant terms Region bound s inside))
    k m mPast

regionImagUniformLimitError :
  (terms : Dirichlet.BishopDirichletTermFamily) →
  (Region : BC.BishopComplex → Set) →
  (bound : RegionBaselDomination terms Region) →
  (k : Nat) → .{{_ : NonZero k}} →
  (s : BC.BishopComplex) →
  (inside : Region s) →
  (m : Nat) →
  m ≥ baselUniformTailCutoff k →
  R._≤_
    (R.∣
      R._-_
        (BC.im (regionDirichletValue terms Region bound s inside))
        (Seq.SeriesOf (Dirichlet.imagTerm terms s) m)
    ∣)
    (R._⋆ (+ 1 / k))
regionImagUniformLimitError terms Region bound k s inside m mPast =
  baselDominatedUniformLimitError
    (Dirichlet.imagTerm terms s)
    (imagEverywhere bound s inside)
    (Dirichlet.imagDirichletConvergent terms s
      (regionPointwiseMajorant terms Region bound s inside))
    k m mPast
