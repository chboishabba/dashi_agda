module DASHI.Analysis.BishopRiemannDirichletExponentialTermExact where

------------------------------------------------------------------------
-- K04d: SOURCE-NATIVE EXPONENTIAL REPRESENTATION OF n^(-s).
--
-- We reuse, rather than reimplement:
--   - BishopSetoidComplexExact.expC, compiled from the original
--     Bishop factorial exponential and Round11 sine/cosine;
--   - BishopRiemannAnalyticSetoidExpReuseExact, proving the literal
--     Bishop pair isomorphism with the ORIGINAL Riemann zeta carrier;
--   - BishopRiemannDirichletBaselSameObjectExact, compiling eventual
--     domination by 1/(n+1)^2 into actual complex series convergence.
--
-- For any candidate positive-Nat real logarithm logNat n (=log(n+1)),
-- the exponent is (-Re(s)*logNat n, -Im(s)*logNat n).  The term
-- expC of that literal original Bishop pair is therefore constructed
-- on the ACTUAL Riemann-Bishop carrier, with exact coordinate identity.
--
-- This does NOT produce a genuine Nat-logarithm or prove
-- exp(log(n+1)) = n+1; those source-side properties remain owed.
-- Nor does it infer a sigma>=2 majorant, local uniform convergence,
-- equality with original ZetaHalfPlaneLayer, or continuity from a
-- free logNat argument. The actual theorem below consumes a real,
-- unhidden all-index Basel domination witness.
--
-- Attribution: Dirichlet, Riemann (1859); Bishop/Bridges (1985);
-- Murray (2022, arXiv:2205.08354); original DASHI Bishop complex,
-- complex exponential and elliptic/Dirichlet comparison owners.
-- Source-written Agda; kernel verification pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_)

import Real as R
import Sequence as Seq
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as A
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopRiemannAnalyticSetoidExpReuseExact as ExpBridge
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E

-- The exact logarithm of positive Nat is still the next nontrivial
-- mathematical lemma. Its expected argument is the indexed integer n+1.
NatLogCandidate : Set
NatLogCandidate = Nat → R.ℝ

bishopNegativeSLn :
  NatLogCandidate → A.BishopComplex → Nat → A.BishopComplex
bishopNegativeSLn logNat s n =
  A.bishop-complex
    (R._*_ (R.-_ (A.re s)) (logNat n))
    (R._*_ (R.-_ (A.im s)) (logNat n))

-- Actual existing Bishop exponential, NOT an unspecified Series value.
bishopDirichletExponentialTerm :
  C.BishopSetoidComplexTranscendentals →
  NatLogCandidate →
  Dirichlet.BishopDirichletTermFamily
bishopDirichletExponentialTerm T logNat s n =
  ExpBridge.bishopAnalyticComplexExp T (bishopNegativeSLn logNat s n)

-- Definitional coordinates: we are genuinely evaluating the original
-- Bishop exponential, sine and cosine at minus s times a REAL log.
bishopDirichletExponentialReal :
  (T : C.BishopSetoidComplexTranscendentals)
  (logNat : NatLogCandidate)
  (s : A.BishopComplex)
  (n : Nat) →
  A.re (bishopDirichletExponentialTerm T logNat s n)
    ≡ R._*_
        (Exp.bishopExp
          (R._*_ (R.-_ (A.re s)) (logNat n)))
        (E.bishopCos
          (C.dataSet T)
          (R._*_ (R.-_ (A.im s)) (logNat n)))
bishopDirichletExponentialReal T logNat s n = refl

bishopDirichletExponentialImag :
  (T : C.BishopSetoidComplexTranscendentals)
  (logNat : NatLogCandidate)
  (s : A.BishopComplex)
  (n : Nat) →
  A.im (bishopDirichletExponentialTerm T logNat s n)
    ≡ R._*_
        (Exp.bishopExp
          (R._*_ (R.-_ (A.re s)) (logNat n)))
        (E.bishopSin
          (C.dataSet T)
          (R._*_ (R.-_ (A.im s)) (logNat n)))
bishopDirichletExponentialImag T logNat s n = refl

-- This is a genuine convergence result for the CONSTRUCTED terms,
-- provided the analytic positivity/logarithm/majorant obligations
-- can be proved. No new source oracle or duplicate comparison proof.
bishopExponentialDirichletConvergesFromBasel :
  (T : C.BishopSetoidComplexTranscendentals)
  (logNat : NatLogCandidate)
  (s : A.BishopComplex)
  (domination :
    Dirichlet.BishopDirichletBaselMajorantAt
      (bishopDirichletExponentialTerm T logNat) s) →
  (Seq._ConvergesTo_
    (λ n →
      A.re (Dirichlet.dirichletPartial
        (bishopDirichletExponentialTerm T logNat) s n))
    (A.re (Dirichlet.dirichletValue
      (bishopDirichletExponentialTerm T logNat) s domination)))
  ×
  (Seq._ConvergesTo_
    (λ n →
      A.im (Dirichlet.dirichletPartial
        (bishopDirichletExponentialTerm T logNat) s n))
    (A.im (Dirichlet.dirichletValue
      (bishopDirichletExponentialTerm T logNat) s domination)))
bishopExponentialDirichletConvergesFromBasel
  T logNat s domination =
  Dirichlet.dirichletPartialConverges
    (bishopDirichletExponentialTerm T logNat) s domination
