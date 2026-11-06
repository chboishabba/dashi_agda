module DASHI.Physics.YangMills.YMClaySUNNativeSixPlaneFullC3FromInverseTraceExact where

------------------------------------------------------------------------
-- R443 SAME-NATIVE-SOURCE COMPLETION CANDIDATE (6 Nov 2026).
--
-- Existing LOCAL native SU(N) six-plane C3:
--   YMClaySUNMatrixNativeSixPlaneC3FromInverseTraceExact
-- Existing GLOBAL actual 4^4-site real Fubini:
--   YMClaySUNMatrixSpatialC3RealFubiniExact
--
-- Compose those exact owners, eliminating the formerly independent
-- full-six-plane C3 ACTION/DENSITY premise for the literal finite
-- pure-Wilson native SU(N) source. Only the physical real-trace
-- inversion authority is explicitly supplied.
--
-- Not the full CMP119 E/R/B/V source. Not constructed real SU(N)
-- compact Haar, the R443 closed 1024-vector permutation equality,
-- R445 continuum, CMP116 decay, OS mass gap or Clay.
-- Source written / Agda kernel and transitive trust not checked.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; -ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeInversePlaquetteRealTraceExact as Inverse
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSixPlaneC3FromInverseTraceExact as Local
import DASHI.Physics.YangMills.YMClaySUNMatrixSpatialC3RealFubiniExact as Global
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

-- The 256-site native SU(N) six-positive-plane deficit, on the SAME
-- original side-four bond carrier, is C3 invariant.
nativeSUNSixPlaneDeficitC3 :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (inverseLaw : Inverse.SUNRealTraceInverseOnNative theory traceData)
    (links : Native.SUNSideFourLinks N theory) →
  Gibbs.nativeSUNSixWilsonDeficit theory traceData
    (Weld.nativeForwardC3Bonds links)
  ≡ Gibbs.nativeSUNSixWilsonDeficit theory traceData links
nativeSUNSixPlaneDeficitC3 theory traceData inverseLaw links =
  Global.nativeSUNSixDeficitC3FromLocal theory traceData links
    (Local.nativeSUNSixAtC3FromInverseRealTrace
      theory traceData inverseLaw links)

-- The original beta-weighted native Wilson action is not an independent
-- chosen C3 weight: derive it from that same native six-plane local proof.
nativeSUNWilsonActionC3 :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (inverseLaw : Inverse.SUNRealTraceInverseOnNative theory traceData)
    (beta : ℝ) (links : Native.SUNSideFourLinks N theory) →
  Gibbs.nativeSUNWilsonAction theory traceData beta
    (Weld.nativeForwardC3Bonds links)
  ≡ Gibbs.nativeSUNWilsonAction theory traceData beta links
nativeSUNWilsonActionC3 theory traceData inverseLaw beta links =
  Global.nativeSUNWilsonActionC3FromLocal theory traceData beta links
    (Local.nativeSUNSixAtC3FromInverseRealTrace
      theory traceData inverseLaw links)

-- The density is precisely Gibbs.nativeSUNWilsonGibbsDensity, not a
-- free C3-invariant field or a new arbitrary weight. In particular,
-- this does NOT establish the separately selected CMP119 E/R/B/V action.
nativeSUNWilsonGibbsDensityC3 :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (inverseLaw : Inverse.SUNRealTraceInverseOnNative theory traceData)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ) (links : Native.SUNSideFourLinks N theory) →
  Gibbs.nativeSUNWilsonGibbsDensity
    theory traceData exponential beta
    (Weld.nativeForwardC3Bonds links)
  ≡ Gibbs.nativeSUNWilsonGibbsDensity
    theory traceData exponential beta links
nativeSUNWilsonGibbsDensityC3
    theory traceData inverseLaw exponential beta links =
  cong (λ action → Exp.expReal exponential (-ℝ action))
    (nativeSUNWilsonActionC3
      theory traceData inverseLaw beta links)
