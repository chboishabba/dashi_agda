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

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
import Data.Nat.Properties as NatP
open import Data.Nat.Base using (_≤_; _<_; _≥_; NonZero; z≤n)
open import Data.Integer.Base as Int using (+_; +<+)
open import Data.Rational.Unnormalised as Rat using (_/_; 0ℚᵘ; 1ℚᵘ; _<_)
import Data.Rational.Unnormalised.Properties as RatP
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import Real as R
import Sequence as Seq
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as A
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopRiemannAnalyticSetoidExpReuseExact as ExpBridge
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Analysis.BishopDirichletUniformBaselTailsExact as UniformTails
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpPositive
import DASHI.Foundations.BishopExponentialCauchyProductExact as ExpAdd
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopInverseSquareProductExact as Inverse
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Foundations.BishopNatRealPositiveExact as NatPositive
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as BaselNat
import RealProperties as RP

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Foundations.BishopRound11TrigAtZeroExact as Origin
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as TrigCong
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopMachinPiRationalWindowExact as MachinWindow
open import Relation.Nullary.Decidable.Core using (toWitness)

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

------------------------------------------------------------------------
-- RATIONAL LOG ARGUMENT: THE TRUE OPEN UNIT INTERVAL.
--
-- For every n >= 0, x_n = (n+1)/(n+2) lies strictly between
-- zero and one, both as an unnormalised rational and as the
-- actual embedded Bishop real. The configured SeriesData's
-- InOpenUnitInterval is still an independent predicate: a
-- bridge into that field is made explicit below and NEVER
-- silently identified with these strict order relations.
------------------------------------------------------------------------

natLogArgumentPositiveRational :
  (n : Nat) →
  Rat._<_ Rat.0ℚᵘ (+ suc n / suc (suc n))
natLogArgumentPositiveRational n =
  RatP.positive⁻¹ (+ suc n / suc (suc n))

natLogArgumentBelowOneRational :
  (n : Nat) →
  Rat._<_ (+ suc n / suc (suc n)) Rat.1ℚᵘ
natLogArgumentBelowOneRational n =
  Rat.*<* (Int.+<+ cross)
  where
    cross : suc (suc n * 1) ≤ 1 * suc (suc n)
    cross =
      let open NatP.≤-Reasoning
      in begin
        suc (suc n * 1)
          ≡⟨ cong suc (NatP.*-identityʳ (suc n)) ⟩
        suc (suc n)
          ≡⟨ sym (NatP.*-identityˡ (suc (suc n))) ⟩
        1 * suc (suc n)
      ∎

natLogArgumentPositiveBishop :
  (n : Nat) → R._<_ R.0ℝ (natLogArgument n)
natLogArgumentPositiveBishop n =
  RP.p<q⇒p⋆<q⋆
    Rat.0ℚᵘ (+ suc n / suc (suc n))
    (natLogArgumentPositiveRational n)

natLogArgumentBelowOneBishop :
  (n : Nat) → R._<_ (natLogArgument n) R.1ℝ
natLogArgumentBelowOneBishop n =
  RP.p<q⇒p⋆<q⋆
    (+ suc n / suc (suc n)) Rat.1ℚᵘ
    (natLogArgumentBelowOneRational n)

configuredNatLogArgumentsInside :
  (T : C.BishopSetoidComplexTranscendentals) →
  ((x : R.ℝ) →
    R._<_ R.0ℝ x →
    R._<_ x R.1ℝ →
    E.InOpenUnitInterval (C.dataSet T) x) →
  (n : Nat) →
  E.InOpenUnitInterval (C.dataSet T) (natLogArgument n)
configuredNatLogArgumentsInside T bridge n =
  bridge (natLogArgument n)
    (natLogArgumentPositiveBishop n)
    (natLogArgumentBelowOneBishop n)

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

------------------------------------------------------------------------
-- LOG(1) IS ALREADY CLOSED: the source Nat logarithm at the first
-- coefficient is literally zero. Thus exp_B(log_B 1)=1 follows
-- from the original (independent) Bishop exponential-zero theorem.
-- All remaining log-inverse work can be restricted to Nat successors.
------------------------------------------------------------------------

originalNatLogAtOneExpIsOne :
  (T : C.BishopSetoidComplexTranscendentals) →
  (inside : (n : Nat) →
    E.InOpenUnitInterval (C.dataSet T) (natLogArgument n)) →
  R._≃_
    (Exp.bishopExp (natLogViaOriginalNegativeLog T inside zero))
    (NatReal.natReal (suc zero))
originalNatLogAtOneExpIsOne T inside =
  ExpPositive.bishopExpZero

originalNatLogInverseFromPositiveSuccessors :
  (T : C.BishopSetoidComplexTranscendentals) →
  (inside : (n : Nat) →
    E.InOpenUnitInterval (C.dataSet T) (natLogArgument n)) →
  ((n : Nat) →
    R._≃_
      (Exp.bishopExp
        (natLogViaOriginalNegativeLog T inside (suc n)))
      (NatReal.natReal (suc (suc n)))) →
  (n : Nat) →
  R._≃_
    (Exp.bishopExp (natLogViaOriginalNegativeLog T inside n))
    (NatReal.natReal (suc n))
originalNatLogInverseFromPositiveSuccessors T inside successorInverse zero =
  originalNatLogAtOneExpIsOne T inside
originalNatLogInverseFromPositiveSuccessors T inside successorInverse (suc n) =
  successorInverse n

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


------------------------------------------------------------------------
-- K04d REAL EXPONENTIAL FIBRE AT s = 2:
-- exp_B(-2 log_B(n+1)) = 1/(n+1)^2 after the *same-object*
-- positive logarithm inversion has been established.
-- The target is Basel.baselTerm n, not an unrelated rational model.
-- This is a precise conditional reduction, not a surrogate proof of
-- the open exp(log n) identity or complex sine/cosine at zero.
------------------------------------------------------------------------

negativeDoubleNatLogExponentialIsBasel :
  (logNat : NatLogCandidate) (n : Nat) →
  R._≃_
    (Exp.bishopExp (logNat n))
    (NatReal.natReal (suc n)) →
  R._≃_
    (Exp.bishopExp
      (R._+_ (R.- (logNat n)) (R.- (logNat n))))
    (Basel.baselTerm n)
negativeDoubleNatLogExponentialIsBasel logNat n correct =
  RP.≃-trans
    (ExpAdd.bishopExpAdd
      (R.- (logNat n))
      (R.- (logNat n)))
    (RP.≃-trans
      (RP.*-cong
        (negativeExponentialAtNatLogIsEmbeddedReciprocal
          logNat n correct)
        (negativeExponentialAtNatLogIsEmbeddedReciprocal
          logNat n correct))
      (RP.≃-trans
        (RP.≃-symm
          (RP.⋆-distrib-*
            (BaselNat.reciprocalNatRational n)
            (BaselNat.reciprocalNatRational n)))
        (RP.⋆-cong
          (BaselNat.reciprocalNatSquareIsBaselRational n))))

negativeTwoNatLogExponentialIsBasel :
  (logNat : NatLogCandidate) (n : Nat) →
  R._≃_
    (Exp.bishopExp (logNat n))
    (NatReal.natReal (suc n)) →
  R._≃_
    (Exp.bishopExp
      (R._*_
        (R.- (R._⋆ (+ 2 / 1)))
        (logNat n)))
    (Basel.baselTerm n)
negativeTwoNatLogExponentialIsBasel logNat n correct =
  RP.≃-trans
    (ExpCong.bishopExpCongruent
      (let open RP.ℝ-Solver
       in solve 1
         (λ l →
           (⊝ (Κ (+ 2 / 1))) ⊗ l
           ⊜ (⊝ l) ⊕ (⊝ l))
         RP.≃-refl
         (logNat n)))
    (negativeDoubleNatLogExponentialIsBasel logNat n correct)

------------------------------------------------------------------------
-- ACTUAL ORIGINAL SOURCE SPECIALIZATION AT INTEGER-TWO.
--
-- Here the logarithm is precisely the original convergent
-- Bishop -log(1-x) series from the configured elementary data,
-- not an arbitrary logNat function. With the remaining original
-- exp/log inverse evidence, its real negative-two coefficient
-- agrees with the independently proved Basel term for EVERY n.
------------------------------------------------------------------------

originalSeriesNatLogAtTwoIsBasel :
  (T : C.BishopSetoidComplexTranscendentals) →
  (inside : (n : Nat) →
    E.InOpenUnitInterval (C.dataSet T) (natLogArgument n)) →
  ((n : Nat) →
    R._≃_
      (Exp.bishopExp (natLogViaOriginalNegativeLog T inside n))
      (NatReal.natReal (suc n))) →
  (n : Nat) →
  R._≃_
    (Exp.bishopExp
      (R._*_
        (R.- (R._⋆ (+ 2 / 1)))
        (natLogViaOriginalNegativeLog T inside n)))
    (Basel.baselTerm n)
originalSeriesNatLogAtTwoIsBasel T inside logInverse n =
  negativeTwoNatLogExponentialIsBasel
    (natLogViaOriginalNegativeLog T inside)
    n
    (logInverse n)


------------------------------------------------------------------------
-- K04d SOURCE-NATIVE EXPONENT-TWO COMPLEX COEFFICIENT.
--
-- The previous lemma proved only the real exp(-2*log(n+1)) factor.
-- Here the COMPLEX term is the actual Riemann-Bishop analytic carrier's
-- original source exponent. At zero imaginary input the original Round11
-- sine/cosine power series equal zero/one (independently proved above).
-- Thus its real/imaginary parts are Basel.baselTerm and zero.
-- This consumes ONLY the still-open exp(log(n+1)) identity; it does not
-- smuggle a different complex realisation or classical trigonometry.
------------------------------------------------------------------------

sourceExponentTwo : A.BishopComplex
sourceExponentTwo = A.bishop-complex (R._⋆ (+ 2 / 1)) R.0ℝ

sourceExponentTwoImaginaryArgumentZero :
  (logNat : NatLogCandidate) (n : Nat) →
  R._≃_
    (R._*_ (R.- R.0ℝ) (logNat n))
    R.0ℝ
sourceExponentTwoImaginaryArgumentZero logNat n =
  let open RP.ℝ-Solver
  in solve 1
    (λ argument → (⊝ Κ Rat.0ℚᵘ) ⊗ argument ⊜ Κ Rat.0ℚᵘ)
    RP.≃-refl (logNat n)

sourceExponentTwoRealIsBasel :
  (inputs : Round11.Round11BishopCutset)
  (logNat : NatLogCandidate)
  (n : Nat) →
  R._≃_
    (Exp.bishopExp (logNat n))
    (NatReal.natReal (suc n)) →
  R._≃_
    (A.re
      (bishopDirichletExponentialTerm
        (Route.round11MachinTranscendentals inputs)
        logNat sourceExponentTwo n))
    (Basel.baselTerm n)
sourceExponentTwoRealIsBasel inputs logNat n logInverse =
  RP.≃-trans
    (RP.*-cong
      (negativeTwoNatLogExponentialIsBasel logNat n logInverse)
      (RP.≃-trans
        (TrigCong.bishopCosCongruent
          (Round11.round11ConcreteTermIdentification inputs)
          (sourceExponentTwoImaginaryArgumentZero logNat n))
        (Origin.round11CosineAtZero inputs)))
    (RP.*-identityʳ (Basel.baselTerm n))

sourceExponentTwoImagIsZero :
  (inputs : Round11.Round11BishopCutset)
  (logNat : NatLogCandidate)
  (n : Nat) →
  R._≃_
    (A.im
      (bishopDirichletExponentialTerm
        (Route.round11MachinTranscendentals inputs)
        logNat sourceExponentTwo n))
    R.0ℝ
sourceExponentTwoImagIsZero inputs logNat n =
  RP.≃-trans
    (RP.*-cong
      RP.≃-refl
      (RP.≃-trans
        (TrigCong.bishopSinCongruent
          (Round11.round11ConcreteTermIdentification inputs)
          (sourceExponentTwoImaginaryArgumentZero logNat n))
        (Origin.round11SineAtZero inputs)))
    (let open RP.ℝ-Solver
     in solve 1
       (λ expFactor → expFactor ⊗ Κ Rat.0ℚᵘ ⊜ Κ Rat.0ℚᵘ)
       RP.≃-refl
       (Exp.bishopExp
         (R._*_ (R.- (R._⋆ (+ 2 / 1))) (logNat n))))

-- No domination authority: reconstruct the comparison witness
-- from the literal coefficient equality and the ORIGINAL Basel owner.
sourceExponentTwoBaselMajorant :
  (inputs : Round11.Round11BishopCutset)
  (logNat : NatLogCandidate) →
  ((n : Nat) →
    R._≃_
      (Exp.bishopExp (logNat n))
      (NatReal.natReal (suc n))) →
  Dirichlet.BishopDirichletBaselMajorantAt
    (bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs) logNat)
    sourceExponentTwo
sourceExponentTwoBaselMajorant inputs logNat logInverse = record
  { Dirichlet.dominationStart = zero
  ; Dirichlet.realDomination = λ n _ →
      RP.≤-respˡ-≃
        (RP.≃-symm
          (RP.∣-∣-cong
            (sourceExponentTwoRealIsBasel
              inputs logNat n (logInverse n))))
        (RP.≤-reflexive (Basel.absoluteBaselTerm n))
  ; Dirichlet.imagDomination = λ n _ →
      RP.≤-respˡ-≃
        (RP.≃-symm
          (RP.∣-∣-cong
            (sourceExponentTwoImagIsZero inputs logNat n)))
        (Dirichlet.zeroAbsBelowBasel n)
  }


------------------------------------------------------------------------
-- ACTUAL COMPLEX DIRICHLET LIMIT AT s=2 IS THE ORIGINAL BISHOP BASEL
-- LIMIT. This consumes the literal native Nat-log inverse, not an
-- unidentified analytic zeta function.
------------------------------------------------------------------------

sourceExponentTwoSumIsOriginalBasel :
  (inputs : Round11.Round11BishopCutset)
  (logNat : NatLogCandidate) →
  (inverseLaw : (n : Nat) →
    R._≃_ (Exp.bishopExp (logNat n))
           (NatReal.natReal (suc n))) →
  let
    terms =
      bishopDirichletExponentialTerm
        (Route.round11MachinTranscendentals inputs) logNat
    bound = sourceExponentTwoBaselMajorant inputs logNat inverseLaw
  in
  (R._≃_
    (A.re (Dirichlet.dirichletValue terms sourceExponentTwo bound))
    Basel.baselLimit)
  ×
  (R._≃_
    (A.im (Dirichlet.dirichletValue terms sourceExponentTwo bound))
    R.0ℝ)
sourceExponentTwoSumIsOriginalBasel inputs logNat inverseLaw =
  let
    terms =
      bishopDirichletExponentialTerm
        (Route.round11MachinTranscendentals inputs) logNat
    bound = sourceExponentTwoBaselMajorant inputs logNat inverseLaw
    same =
      Dirichlet.dirichletValuesRespectTermwiseEquality
        terms Dirichlet.baselIntegerTwoTermFamily sourceExponentTwo
        bound (Dirichlet.baselIntegerTwoMajorant sourceExponentTwo)
        (λ n → sourceExponentTwoRealIsBasel
          inputs logNat n (inverseLaw n))
        (λ n → sourceExponentTwoImagIsZero inputs logNat n)
  in
  RP.≃-trans
    (proj₁ same)
    (Dirichlet.baselCompiledRealLimitIsOriginal sourceExponentTwo)
  ,
  RP.≃-trans
    (proj₂ same)
    (Dirichlet.baselCompiledImagLimitIsZero sourceExponentTwo)

-- Concrete original -log(1-x) source, not an arbitrary NatLogCandidate.
originalSourceExponentTwoSumIsBasel :
  (inputs : Round11.Round11BishopCutset) →
  (inside : (n : Nat) →
    E.InOpenUnitInterval
      (Round11.elementarySeries inputs) (natLogArgument n)) →
  (inverseLaw : (n : Nat) →
    R._≃_
      (Exp.bishopExp
        (natLogViaOriginalNegativeLog
          (Route.round11MachinTranscendentals inputs) inside n))
      (NatReal.natReal (suc n))) →
  let
    logNat =
      natLogViaOriginalNegativeLog
        (Route.round11MachinTranscendentals inputs) inside
    terms = bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs) logNat
    bound = sourceExponentTwoBaselMajorant inputs logNat inverseLaw
  in
  (R._≃_
    (A.re (Dirichlet.dirichletValue terms sourceExponentTwo bound))
    Basel.baselLimit)
  ×
  (R._≃_
    (A.im (Dirichlet.dirichletValue terms sourceExponentTwo bound))
    R.0ℝ)
originalSourceExponentTwoSumIsBasel inputs inside inverseLaw =
  sourceExponentTwoSumIsOriginalBasel
    inputs
    (natLogViaOriginalNegativeLog
      (Route.round11MachinTranscendentals inputs) inside)
    inverseLaw

------------------------------------------------------------------------
-- K04d: UNIFORM TAILS FOR THE ACTUAL CONSTRUCTED COMPLEX s=2 SERIES.
--
-- This specializes the pinned Bishop Basel Cauchy test to BOTH
-- actual source complex coordinates, and uses ONE cutoff for ALL
-- m,n. The only remaining hypothesis is the same source exp(log Nat)
-- inverse as the previously established exact coefficient equality.
-- No separate analytic convergence or new common modulus is assumed.
------------------------------------------------------------------------

sourceExponentTwoUniformFiniteTails :
  (inputs : Round11.Round11BishopCutset)
  (logNat : NatLogCandidate)
  (inverseLaw : (n : Nat) →
    R._≃_
      (Exp.bishopExp (logNat n))
      (NatReal.natReal (suc n))) →
  (k : Nat) → .{{_ : NonZero k}} →
  (m n : Nat) →
  m ≥ UniformTails.baselUniformTailCutoff k →
  n ≥ UniformTails.baselUniformTailCutoff k →
  let
    terms = bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs) logNat
  in
  (R._≤_
    (R.∣ Seq.∑ (Dirichlet.realTerm terms sourceExponentTwo) m n ∣)
    (R._⋆ (+ 1 / k)))
  ×
  (R._≤_
    (R.∣ Seq.∑ (Dirichlet.imagTerm terms sourceExponentTwo) m n ∣)
    (R._⋆ (+ 1 / k)))
sourceExponentTwoUniformFiniteTails
    inputs logNat inverseLaw k m n mPast nPast =
  let
    terms = bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs) logNat
    majorant =
      sourceExponentTwoBaselMajorant inputs logNat inverseLaw
  in
  UniformTails.baselDominatedFiniteTailSmall
    (Dirichlet.realTerm terms sourceExponentTwo)
    (λ index → Dirichlet.realDomination majorant index z≤n)
    k m n mPast nPast
  ,
  UniformTails.baselDominatedFiniteTailSmall
    (Dirichlet.imagTerm terms sourceExponentTwo)
    (λ index → Dirichlet.imagDomination majorant index z≤n)
    k m n mPast nPast

originalSourceExponentTwoUniformFiniteTails :
  (inputs : Round11.Round11BishopCutset) →
  (inside : (n : Nat) →
    E.InOpenUnitInterval
      (Round11.elementarySeries inputs) (natLogArgument n)) →
  (inverseLaw : (n : Nat) →
    R._≃_
      (Exp.bishopExp
        (natLogViaOriginalNegativeLog
          (Route.round11MachinTranscendentals inputs) inside n))
      (NatReal.natReal (suc n))) →
  (k : Nat) → .{{_ : NonZero k}} →
  (m n : Nat) →
  m ≥ UniformTails.baselUniformTailCutoff k →
  n ≥ UniformTails.baselUniformTailCutoff k →
  let
    terms = bishopDirichletTermFromOriginalLogSeries
      (Route.round11MachinTranscendentals inputs) inside
  in
  (R._≤_
    (R.∣ Seq.∑ (Dirichlet.realTerm terms sourceExponentTwo) m n ∣)
    (R._⋆ (+ 1 / k)))
  ×
  (R._≤_
    (R.∣ Seq.∑ (Dirichlet.imagTerm terms sourceExponentTwo) m n ∣)
    (R._⋆ (+ 1 / k)))
originalSourceExponentTwoUniformFiniteTails
    inputs inside inverseLaw k m n mPast nPast =
  sourceExponentTwoUniformFiniteTails
    inputs
    (natLogViaOriginalNegativeLog
      (Route.round11MachinTranscendentals inputs) inside)
    inverseLaw k m n mPast nPast


------------------------------------------------------------------------
-- K04d REAL-AXIS SOURCE EXPONENTIAL IDENTITY, ALL BISHOP SIGMA.
-- No log-inverse, Basel domination, or completed-zeta agreement
-- required. It is the actual source's original complex expC
-- and the same Round11 sine/cosine at zero, at EVERY real sigma.
------------------------------------------------------------------------

sourceRealAxisExponent : R.ℝ → A.BishopComplex
sourceRealAxisExponent sigma =
  A.bishop-complex sigma R.0ℝ

sourceRealAxisExponentialRealCoefficient :
  (inputs : Round11.Round11BishopCutset)
  (logNat : NatLogCandidate)
  (sigma : R.ℝ)
  (n : Nat) →
  R._≃_
    (A.re
      (bishopDirichletExponentialTerm
        (Route.round11MachinTranscendentals inputs)
        logNat (sourceRealAxisExponent sigma) n))
    (Exp.bishopExp
      (R._*_ (R.- sigma) (logNat n)))
sourceRealAxisExponentialRealCoefficient inputs logNat sigma n =
  RP.≃-trans
    (RP.*-cong
      RP.≃-refl
      (RP.≃-trans
        (TrigCong.bishopCosCongruent
          (Round11.round11ConcreteTermIdentification inputs)
          (sourceExponentTwoImaginaryArgumentZero logNat n))
        (Origin.round11CosineAtZero inputs)))
    (RP.*-identityʳ
      (Exp.bishopExp (R._*_ (R.- sigma) (logNat n))))

sourceRealAxisExponentialImaginaryZero :
  (inputs : Round11.Round11BishopCutset)
  (logNat : NatLogCandidate)
  (sigma : R.ℝ)
  (n : Nat) →
  R._≃_
    (A.im
      (bishopDirichletExponentialTerm
        (Route.round11MachinTranscendentals inputs)
        logNat (sourceRealAxisExponent sigma) n))
    R.0ℝ
sourceRealAxisExponentialImaginaryZero inputs logNat sigma n =
  RP.≃-trans
    (RP.*-cong
      RP.≃-refl
      (RP.≃-trans
        (TrigCong.bishopSinCongruent
          (Round11.round11ConcreteTermIdentification inputs)
          (sourceExponentTwoImaginaryArgumentZero logNat n))
        (Origin.round11SineAtZero inputs)))
    (let open RP.ℝ-Solver
     in solve 1
       (λ realFactor → realFactor ⊗ Κ Rat.0ℚᵘ ⊜ Κ Rat.0ℚᵘ)
       RP.≃-refl
       (Exp.bishopExp
         (R._*_ (R.- sigma) (logNat n))))


------------------------------------------------------------------------
-- K04d: THE SELECTED *ACTUAL MACHIN REAL* IS IN Re(s)>2.
-- This is a genuine geometric precondition for the Basel-majorized
-- Dirichlet neighborhood, beyond merely proving Re(s)>1. It reuses
-- the ORIGINAL constructive 3<pi_M<22/7 interval.
------------------------------------------------------------------------

twoBelowThreeRational : Rat._<_ (+ 2 / 1) (+ 3 / 1)
twoBelowThreeRational =
  toWitness {a? = RatP._<?_ (+ 2 / 1) (+ 3 / 1)} _

twoBelowMachinBishopPi :
  R._<_ (R._⋆ (+ 2 / 1)) Machin.bishopMachinPi
twoBelowMachinBishopPi =
  RP.<-trans
    (RP.p<q⇒p⋆<q⋆
      (+ 2 / 1) (+ 3 / 1)
      twoBelowThreeRational)
    MachinWindow.threeBelowMachinPi

machinSourceRealPoint : A.BishopComplex
machinSourceRealPoint =
  sourceRealAxisExponent Machin.bishopMachinPi

machinSourceRealPartAboveTwo :
  R._<_ (R._⋆ (+ 2 / 1)) (A.re machinSourceRealPoint)
machinSourceRealPartAboveTwo =
  twoBelowMachinBishopPi
