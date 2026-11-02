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
