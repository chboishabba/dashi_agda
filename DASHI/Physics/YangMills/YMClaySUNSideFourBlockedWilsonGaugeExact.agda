module DASHI.Physics.YangMills.YMClaySUNSideFourBlockedWilsonGaugeExact where

------------------------------------------------------------------------
-- R445.P02 selected 4D YM physical observable join:
-- SAME original SUN period-four fine links and period-two coarse links.
--
-- Source owners:
-- * YMClayNativeSideFourTwoBlockEndpointExact:
--     proof of exact native SU(N) blocked-link gauge covariance at the
--     real four-dimensional side-four -> side-two blocking;
-- * YMClaySUNVariablePeriodicGibbsGaugeExact:
--     the ORIGINAL Wilson plaquette, six positive-plane action and Gibbs;
-- * YMClaySUNVariablePeriodicBondPointwiseExact:
--     pointwise congruence of the SAME original Wilson/Gibbs expressions.
--
-- Result: construct original selected coarse Wilson plaquette/6-plane
-- observable and Gibbs density as functions of the actual fine links
-- after noncommutative ordered 2-link blocking, and prove that all
-- three are invariant under the ORIGINAL fine site gauge transformation.
--
-- This is NOT a Wilson-action equality between fine and coarse scales:
-- the effective Gibbs weight after integrating out the fine links may
-- contain new interactions, counterterms and polymer corrections. This
-- file makes NO claim that the native coarse Wilson density equals the
-- actual pushforward of the fine Gibbs measure. No continuum or gap.
--
-- Source-written: no new local postulate or field extensionality; exact
-- Agda kernel and transitive real-analysis authority audits still OPEN.
-- Wilson, Bałaban, Haar and earlier DASHI theorem owners retain credit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicBondPointwiseExact as Pointwise
import DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact as Block
import DASHI.Physics.YangMills.YMClayNativeSideFourTwoBlockEndpointExact as Endpoint
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
  where

  FineLinks : Set
  FineLinks = Variable.SUNPeriodicLinks theory 3

  FineGauge : Set
  FineGauge = Variable.SUNPeriodicGauge theory 3

  CoarseLinks : Set
  CoarseLinks = Variable.SUNPeriodicLinks theory 1

  fineToCoarse : FineLinks → CoarseLinks
  fineToCoarse = Block.nativeSUNBlockLinks {m = 1} {l = 1} theory

  gaugeToCoarse :
    FineGauge → Variable.SUNPeriodicGauge theory 1
  gaugeToCoarse =
    Block.nativeSUNBlockGauge {m = 1} {l = 1} theory

  blockFineGaugeCoarsePointwise :
    ∀ fine gamma →
    Pointwise.VariableBondPointwise theory 1
      (fineToCoarse
        (Variable.periodicSUNGaugeTransform theory 3 fine gamma))
      (Variable.periodicSUNGaugeTransform theory 1
        (fineToCoarse fine) (gaugeToCoarse gamma))
  blockFineGaugeCoarsePointwise fine gamma =
    Endpoint.sideFourSUNBlockGaugeCovariant theory fine gamma

  -- Actual original coarse Wilson plaquette holonomy, not a finite
  -- quaternion surrogate or a newly selected action.
  blockedSelectedPlaquette :
    FineLinks → Plaquette.PeriodicPlaquette 1 →
    SUN.SUNMatrixElement theory
  blockedSelectedPlaquette fine =
    Variable.periodicSUNPositivePlaquette theory 1
      (fineToCoarse fine)

  blockedSelectedPlaquetteGauge :
    ∀ fine gamma plaquette →
    blockedSelectedPlaquette
      (Variable.periodicSUNGaugeTransform theory 3 fine gamma)
      plaquette
    ≡
    Variable.periodicSUNPositivePlaquette theory 1
      (Variable.periodicSUNGaugeTransform theory 1
        (fineToCoarse fine) (gaugeToCoarse gamma))
      plaquette
  blockedSelectedPlaquetteGauge fine gamma plaquette =
    Pointwise.variablePositivePlaquettePointwise
      theory 1
      (fineToCoarse
        (Variable.periodicSUNGaugeTransform theory 3 fine gamma))
      (Variable.periodicSUNGaugeTransform theory 1
        (fineToCoarse fine) (gaugeToCoarse gamma))
      (blockFineGaugeCoarsePointwise fine gamma)
      plaquette

  -- Under local gauge changes a plaquette is conjugated. Its Wilson
  -- real trace, not the group-valued plaquette itself, is invariant.
  blockedSelectedPlaquetteWilsonGauge :
    ∀ fine gamma plaquette →
    Trace.matrixWilsonValue traceData
      (blockedSelectedPlaquette
        (Variable.periodicSUNGaugeTransform theory 3 fine gamma)
        plaquette)
    ≡
    Trace.matrixWilsonValue traceData
      (blockedSelectedPlaquette fine plaquette)
  blockedSelectedPlaquetteWilsonGauge fine gamma plaquette =
    trans
      (cong (Trace.matrixWilsonValue traceData)
        (blockedSelectedPlaquetteGauge fine gamma plaquette))
      (Variable.periodicSUNPositivePlaquetteGaugeTrace
        theory traceData 1
        (fineToCoarse fine)
        (gaugeToCoarse gamma) plaquette)

  blockedSelectedSixDeficit : FineLinks → ℝ
  blockedSelectedSixDeficit fine =
    Variable.periodicSUNSixDeficit theory traceData 1
      (fineToCoarse fine)

  blockedSelectedSixDeficitGaugeInvariant :
    ∀ fine gamma →
    blockedSelectedSixDeficit
      (Variable.periodicSUNGaugeTransform theory 3 fine gamma)
    ≡ blockedSelectedSixDeficit fine
  blockedSelectedSixDeficitGaugeInvariant fine gamma =
    trans
      (Pointwise.variableSixWilsonDeficitPointwise
        theory traceData 1
        (fineToCoarse
          (Variable.periodicSUNGaugeTransform theory 3 fine gamma))
        (Variable.periodicSUNGaugeTransform theory 1
          (fineToCoarse fine) (gaugeToCoarse gamma))
        (blockFineGaugeCoarsePointwise fine gamma))
      (Variable.periodicSUNSixDeficitGaugeInvariant
        theory traceData 1 (fineToCoarse fine)
        (gaugeToCoarse gamma))

  blockedSelectedWilsonAction : ℝ → FineLinks → ℝ
  blockedSelectedWilsonAction beta fine =
    Variable.periodicSUNWilsonAction theory traceData 1 beta
      (fineToCoarse fine)

  blockedSelectedWilsonActionGaugeInvariant :
    ∀ beta fine gamma →
    blockedSelectedWilsonAction beta
      (Variable.periodicSUNGaugeTransform theory 3 fine gamma)
    ≡ blockedSelectedWilsonAction beta fine
  blockedSelectedWilsonActionGaugeInvariant beta fine gamma =
    trans
      (Pointwise.variableWilsonActionPointwise
        theory traceData 1 beta
        (fineToCoarse
          (Variable.periodicSUNGaugeTransform theory 3 fine gamma))
        (Variable.periodicSUNGaugeTransform theory 1
          (fineToCoarse fine) (gaugeToCoarse gamma))
        (blockFineGaugeCoarsePointwise fine gamma))
      (Variable.periodicSUNWilsonActionGaugeInvariant
        theory traceData 1 beta (fineToCoarse fine)
        (gaugeToCoarse gamma))

  blockedSelectedGibbsDensity :
    Exp.StrictPositiveRealExponential → ℝ →
    FineLinks → ℝ
  blockedSelectedGibbsDensity exponential beta fine =
    Variable.periodicSUNGibbsDensity
      theory traceData exponential 1 beta (fineToCoarse fine)

  blockedSelectedGibbsDensityGaugeInvariant :
    ∀ exponential beta fine gamma →
    blockedSelectedGibbsDensity exponential beta
      (Variable.periodicSUNGaugeTransform theory 3 fine gamma)
    ≡ blockedSelectedGibbsDensity exponential beta fine
  blockedSelectedGibbsDensityGaugeInvariant
      exponential beta fine gamma =
    trans
      (Pointwise.variableGibbsDensityPointwise
        theory traceData exponential 1 beta
        (fineToCoarse
          (Variable.periodicSUNGaugeTransform theory 3 fine gamma))
        (Variable.periodicSUNGaugeTransform theory 1
          (fineToCoarse fine) (gaugeToCoarse gamma))
        (blockFineGaugeCoarsePointwise fine gamma))
      (Variable.periodicSUNGibbsDensityGaugeInvariant
        theory traceData exponential 1 beta
        (fineToCoarse fine) (gaugeToCoarse gamma))
