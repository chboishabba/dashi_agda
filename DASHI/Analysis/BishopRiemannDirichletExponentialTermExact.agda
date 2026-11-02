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

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_)

import Real as R
import Sequence as Seq
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as A
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopRiemannAnalyticSetoidExpReuseExact as ExpBridge
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialCauchyProductExact as ExpAdd
import DASHI.Foundations.BishopInverseSquareProductExact as Inverse
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Foundations.BishopNatRealPositiveExact as NatPositive
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as BaselNat
import RealProperties as RP

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

------------------------------------------------------------------------
-- SOURCE-OWNED NAT LOG CANDIDATE VIA -log(1 - x), NOT A FRESH LOG.
--
-- For m=n+1>1 choose x=(m-1)/m in (0,1). The source's
-- Bishop negative-log-one-minus power series is CONVERGENT at x
-- when its original InOpenUnitInterval evidence is supplied.
-- log(1)=0 is handled separately, since x=0 need not be covered
-- by an open *strictly positive* unit-interval predicate.
--
-- Missing: actual membership for each rational x, plus native proof
-- that this constructed series is an inverse of Exp.bishopExp and
-- agrees with log(m). This is a genuine candidate construction,
-- not an automatic global log theorem.
------------------------------------------------------------------------

natLogArgument : Nat → R.ℝ
natLogArgument n =
  R._⋆ (+ suc n / suc (suc n))

natLogViaOriginalNegativeLog :
  (T : C.BishopSetoidComplexTranscendentals) →
  ((n : Nat) →
    E.InOpenUnitInterval (C.dataSet T) (natLogArgument n)) →
  NatLogCandidate
natLogViaOriginalNegativeLog T inside zero = R.0ℝ
natLogViaOriginalNegativeLog T inside (suc n) =
  E.bishopNegativeLogOneMinus
    (C.dataSet T)
    (natLogArgument n)
    (inside n)

natLogAtOneIsZero :
  (T : C.BishopSetoidComplexTranscendentals) →
  (inside : (n : Nat) →
    E.InOpenUnitInterval (C.dataSet T) (natLogArgument n)) →
  natLogViaOriginalNegativeLog T inside zero ≡ R.0ℝ
natLogAtOneIsZero T inside = refl

natLogSuccessorHasOriginalSeriesConvergence :
  (T : C.BishopSetoidComplexTranscendentals) →
  (inside : (n : Nat) →
    E.InOpenUnitInterval (C.dataSet T) (natLogArgument n)) →
  (n : Nat) →
  Seq._ConvergesTo_
    (Seq.SeriesOf
      (E.negativeLogOneMinusTerm
        (C.dataSet T) (natLogArgument n)))
    (natLogViaOriginalNegativeLog T inside (suc n))
natLogSuccessorHasOriginalSeriesConvergence T inside n =
  E.bishopNegativeLogConvergence
    (C.dataSet T) (natLogArgument n) (inside n)

-- The selected n^(-s) term now uses the original, genuinely
-- convergent Bishop -log(1-x) series for its log candidate,
-- and the already-constructed original Bishop exp/sin/cos series.
-- Only membership is supplied; the key exp∘log and majorant
-- identities are NOT inferred from mere convergence.
bishopDirichletTermFromOriginalLogSeries :
  (T : C.BishopSetoidComplexTranscendentals) →
  (inside : (n : Nat) →
    E.InOpenUnitInterval (C.dataSet T) (natLogArgument n)) →
  Dirichlet.BishopDirichletTermFamily
bishopDirichletTermFromOriginalLogSeries T inside =
  bishopDirichletExponentialTerm T
    (natLogViaOriginalNegativeLog T inside)


------------------------------------------------------------------------
-- K04d LOG-INVERSE -> RECIPROCAL: A NEW CONCRETE REDUCTION.
--
-- The remaining exp(log(n+1)) theorem is a genuine series theorem;
-- it is NOT assumed globally or replaced by a legacy logarithm.
-- Once supplied for the selected original Bishop log candidate,
-- the *already proved* exp(x)*exp(-x)=1 and the original Bishop
-- inverse-uniqueness theorem force its negative exponential to be
-- the actual inverse of the embedded positive natural number.
-- The canonical Nat reciprocal identification then gives 1/(n+1).
------------------------------------------------------------------------

negativeExponentialAtNatLogIsCanonicalReciprocal :
  (logNat : NatLogCandidate) (n : Nat) →
  R._≃_
    (Exp.bishopExp (logNat n))
    (NatReal.natReal (suc n)) →
  R._≃_
    (Exp.bishopExp (R.- (logNat n)))
    (Inverse.inverse
      (NatReal.natReal (suc n))
      (Reciprocal.xNonzero
        (NatPositive.natRealSuccessorStrictlyPositive n)))
negativeExponentialAtNatLogIsCanonicalReciprocal logNat n correct =
  RP.≃-symm
    (Inverse.inverseFromCancellation
      (NatReal.natReal (suc n))
      (Exp.bishopExp (R.- (logNat n)))
      (Reciprocal.xNonzero
        (NatPositive.natRealSuccessorStrictlyPositive n))
      candidateCancels)
  where
    candidateCancels :
      R._≃_
        (R._*_
          (Exp.bishopExp (R.- (logNat n)))
          (NatReal.natReal (suc n)))
        R.1ℝ
    candidateCancels =
      RP.≃-trans
        (RP.*-congˡ (RP.≃-symm correct))
        (RP.≃-trans
          (RP.*-comm
            (Exp.bishopExp (R.- (logNat n)))
            (Exp.bishopExp (logNat n)))
          (ExpAdd.bishopExpTimesNegativeIsOne (logNat n)))

negativeExponentialAtNatLogIsEmbeddedReciprocal :
  (logNat : NatLogCandidate) (n : Nat) →
  R._≃_
    (Exp.bishopExp (logNat n))
    (NatReal.natReal (suc n)) →
  R._≃_
    (Exp.bishopExp (R.- (logNat n)))
    (R._⋆ (BaselNat.reciprocalNatRational n))
negativeExponentialAtNatLogIsEmbeddedReciprocal logNat n correct =
  RP.≃-trans
    (negativeExponentialAtNatLogIsCanonicalReciprocal
      logNat n correct)
    (BaselNat.natRealInverseIsEmbeddedReciprocal n)
