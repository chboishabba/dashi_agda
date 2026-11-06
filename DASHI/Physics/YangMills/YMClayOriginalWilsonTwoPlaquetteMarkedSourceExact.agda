module DASHI.Physics.YangMills.YMClayOriginalWilsonTwoPlaquetteMarkedSourceExact where

------------------------------------------------------------------------
-- Y.02: ACTUAL ORIGINAL TWO PLAQUETTES ARE THE TWO SOURCE DIRECTIONS.
--
-- Select arbitrary positive plaquettes p and q on the ORIGINAL side
-- (n+1) periodic four-torus. Their actual gauge-invariant Wilson mark
--
--   F_p(U) = 1 - ReTr(U_p)/N
--
-- is constructed from the existing actual noncommutative native path
-- holonomy and cyclic real trace, not an abstract source-direction Set.
-- A single actual original finite Wilson-Gibbs measure defines every
-- coefficient of the normalized two-marked source polynomial.
--
-- The full finite two-source functional is gauge-invariant, and the
-- source polynomial and original connected covariance are attached to
-- the very same (p,q) marks. Physical support/distance calibration and
-- CMP116 *localized* response are deliberately not inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_;
    0ℝ; _≤ℝ_; _<ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicBondPointwiseExact as Pointwise
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGaugeHaarExact as GaugeHaar
import DASHI.Physics.YangMills.YMClaySUNConstructedPeriodicGaugeCodecExact as Constructed
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Original
import DASHI.Physics.YangMills.YMClayOriginalWilsonAffineMarkedPartitionExact as Affine
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  OriginalLinks : Nat → Set
  OriginalLinks n = Variable.SUNPeriodicLinks theory n

  PlaquetteAt : Nat → Set
  PlaquetteAt n = Plaquette.PeriodicPlaquette n

  -- Literal physically selected gauge-invariant trace deficit.
  originalPlaquetteMark :
    (n : Nat) → PlaquetteAt n → OriginalLinks n → ℝ
  originalPlaquetteMark n p links =
    1ℝ -ℝ
      Trace.matrixWilsonValue traceData
        (Variable.periodicSUNPositivePlaquette theory n links p)

  originalPlaquetteMarkGaugeInvariant :
    ∀ n p links (gamma : Variable.SUNPeriodicGauge theory n) →
    originalPlaquetteMark n p
      (Variable.periodicSUNGaugeTransform theory n links gamma)
    ≡ originalPlaquetteMark n p links
  originalPlaquetteMarkGaugeInvariant n p links gamma =
    cong (1ℝ -ℝ_)
      (Variable.periodicSUNPositivePlaquetteGaugeTrace
        theory traceData n links gamma p)

  originalPlaquetteMarkPointwise :
    ∀ n p (left right : OriginalLinks n) →
    Pointwise.VariableBondPointwise theory n left right →
    originalPlaquetteMark n p left ≡
      originalPlaquetteMark n p right
  originalPlaquetteMarkPointwise n p left right same =
    cong (1ℝ -ℝ_)
      (cong (Trace.matrixWilsonValue traceData)
        (Pointwise.variablePositivePlaquettePointwise
          theory n left right same p))

  originalTwoPlaquetteAffineTest :
    ∀ n (p q : PlaquetteAt n) → ℝ → ℝ → OriginalLinks n → ℝ
  originalTwoPlaquetteAffineTest n p q s t links =
    (1ℝ +ℝ s *ℝ originalPlaquetteMark n p links)
    *ℝ
    (1ℝ +ℝ t *ℝ originalPlaquetteMark n q links)

  originalTwoPlaquetteAffineTestPointwise :
    ∀ n (p q : PlaquetteAt n) s t →
    GaugeHaar.PeriodicPointwiseObservable
      theory traceData exponential n (beta n)
      oneLink bilateral
      (Codec.decodeOriginalBonds (suc n))
      divide (originalTwoPlaquetteAffineTest n p q s t)
  originalTwoPlaquetteAffineTestPointwise n p q s t = record
    { GaugeHaar.PeriodicPointwiseObservable.congruentAt =
        λ left right same →
          cong₂ _*ℝ_
            (cong (λ mark → 1ℝ +ℝ s *ℝ mark)
              (originalPlaquetteMarkPointwise n p left right same))
            (cong (λ mark → 1ℝ +ℝ t *ℝ mark)
              (originalPlaquetteMarkPointwise n q left right same))
    }

  -- Same selected original Wilson partition at every n.
  actualOriginalTwoPlaquetteNormalizedSource :
    ∀ n (p q : PlaquetteAt n) → ℝ → ℝ → ℝ
  actualOriginalTwoPlaquetteNormalizedSource n p q =
    Affine.originalNormalizedAffineMarkedPartition
      theory traceData exponential beta oneLink bilateral divide
      n (originalPlaquetteMark n p) (originalPlaquetteMark n q)

  actualTwoPlaquetteSourceIsGaugeInvariant :
    ∀ n (p q : PlaquetteAt n) s t
      (gamma : Variable.SUNPeriodicGauge theory n) →
    Physical.normalizedExpectation
      (Original.originalWilsonMeasure
        theory traceData exponential beta oneLink bilateral divide n)
      (λ links →
        originalTwoPlaquetteAffineTest n p q s t
          (Variable.periodicSUNGaugeTransform theory n links gamma))
    ≡ actualOriginalTwoPlaquetteNormalizedSource n p q s t
  actualTwoPlaquetteSourceIsGaugeInvariant n p q s t gamma =
    Constructed.actualPeriodicGaugeNormalized
      theory traceData exponential n (beta n)
      oneLink bilateral divide
      (originalTwoPlaquetteAffineTest n p q s t)
      (originalTwoPlaquetteAffineTestPointwise n p q s t)
      gamma

  -- The ORIGINAL two physical plaquette labels have an exact source
  -- polynomial from the same underlying normalized Haar/Gibbs measure.
  originalTwoPlaquetteActualMomentPolynomial :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (divideSelf : ∀ denominator →
      0ℝ <ℝ denominator → divide denominator denominator ≡ 1ℝ)
    (divideAdd : ∀ denominator →
      0ℝ <ℝ denominator → ∀ left right →
      divide (left +ℝ right) denominator
      ≡ divide left denominator +ℝ divide right denominator)
    (divideScale : ∀ denominator →
      0ℝ <ℝ denominator → ∀ scalar numerator →
      divide (scalar *ℝ numerator) denominator
      ≡ scalar *ℝ divide numerator denominator)
    ∀ n (p q : PlaquetteAt n) s t →
    actualOriginalTwoPlaquetteNormalizedSource n p q s t
    ≡
    Affine.originalNormalizedMomentPolynomial
      theory traceData exponential beta oneLink bilateral divide
      n (originalPlaquetteMark n p) (originalPlaquetteMark n q) s t
  originalTwoPlaquetteActualMomentPolynomial
      ordered strictToWeak strict divideSelf divideAdd divideScale
      n p q s t =
    Affine.originalNormalizedAffineIsLiteralMomentPolynomial
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak strict divideSelf divideAdd divideScale
      n (originalPlaquetteMark n p) (originalPlaquetteMark n q) s t

  -- The new source uses the SAME literal two-plaquette marks that enter
  -- the existing original Wilson normalized-cumulant theorem.
  originalTwoPlaquetteMixedJetIsActualWilsonCovariance :
    ∀ n (p q : PlaquetteAt n) →
    let jet = Original.originalWilsonLiteralJetDirections
          theory traceData exponential beta oneLink bilateral divide n
        left = originalPlaquetteMark n p
        right = originalPlaquetteMark n q
    in
    Cumulant.literalMixedSecondLogDerivative jet
      (Cumulant.sourceDirectionOf jet left)
      (Cumulant.sourceDirectionOf jet right)
    ≡
    Cumulant.connectedCovariance
      (Original.originalWilsonMomentAlgebra
        theory traceData exponential beta oneLink bilateral divide n)
      left right
  originalTwoPlaquetteMixedJetIsActualWilsonCovariance n p q =
    Original.originalWilsonMixedJetIsOriginalConnectedCumulant
      theory traceData exponential beta oneLink bilateral divide
      n (originalPlaquetteMark n p) (originalPlaquetteMark n q)

-- The selected source p,q now has actual original finite Wilson
-- semantics and gauge-invariance. Physical separation/time calibration
-- and *CMP116 uniform marked localization* still require the actual
-- one-trajectory physical estimates; no Wilson mass gap follows.
