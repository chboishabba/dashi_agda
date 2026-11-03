{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNConstructedPeriodicGaugeCodecExact where

------------------------------------------------------------------------
-- R443/R445 P0: ACTUAL VARIABLE-PERIODIC SU(N) BOND-VECTOR GAUGE CODEC.
--
-- This constructs the previously UNINHABITED
-- OriginalPeriodicGaugeVectorNaturality from the original duplicate-free
-- positive-bond enumeration, not from another stipulated gauge equality.
-- Original (suc n)^4 four-torus bonds, original signed Wilson paths, and
-- source-site/target-site factors are used without a second lattice.
--
-- The group associativity step is essential: the Balaban native bond
-- transform is (gamma(x)*U)*gamma(y)^(-1), while the existing one-link
-- Haar theorem uses gamma(x)*(U*gamma(y)^(-1)).
--
-- No compact Haar producer, scalar model, cutoff-uniform decay, selected
-- R124 source, OS reconstruction or Clay gap is supplied by this codec.
-- Original Wilson, Balaban, Haar and in-repo owners retain authorship.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
import Agda.Builtin.List as List
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicBondPointwiseExact as Pointwise
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicProductHaarExact as VariableHaar
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGaugeHaarExact as GaugeHaar
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (n : Nat) (beta : ℝ)
    (oneLink : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Gamma : Set
  Gamma = Variable.SUNPeriodicGauge theory n

  positiveBondCount : Nat
  positiveBondCount = Codec.originalPositiveBondCount (suc n)

  nativeDecode :
    Vec.Vec Link positiveBondCount → Variable.SUNPeriodicLinks theory n
  nativeDecode = Codec.decodeOriginalBonds (suc n)

  nativeEncode :
    Variable.SUNPeriodicLinks theory n → Vec.Vec Link positiveBondCount
  nativeEncode = Codec.encodeOriginalBonds (suc n)

  -- These are the exact original gauge factors for each positive bond.
  leftField : Gamma → Torus.BondField (suc n) Link
  leftField gamma (Torus.pair site axis) = gamma site

  rightField : Gamma → Torus.BondField (suc n) Link
  rightField gamma (Torus.pair site axis) =
    SUN.sunInverse theory (gamma (Bond.positiveStep site axis))

  leftFactors : Gamma → Vec.Vec Link positiveBondCount
  leftFactors gamma = nativeEncode (leftField gamma)

  rightFactors : Gamma → Vec.Vec Link positiveBondCount
  rightFactors gamma = nativeEncode (rightField gamma)

  -- Reuse the prior product-Haar gauge action, vector by vector, at the
  -- canonical *unmodified* original bond enumeration.
  gaugeVectorOfList :
    ∀ {A : Set} (labels : List.List A)
      (left right field : A → Link) →
    Bilateral.gaugeBondVector theory oneLink bilateral
      (Codec.listValues labels left)
      (Codec.listValues labels right)
      (Codec.listValues labels field)
    ≡
    Codec.listValues labels
      (λ label →
        Bilateral.gaugeOneLink theory oneLink bilateral
          (left label) (right label) (field label))
  gaugeVectorOfList List.[] left right field = refl
  gaugeVectorOfList (List._∷_ label labels) left right field =
    cong
      (Vec._∷_
        (Bilateral.gaugeOneLink theory oneLink bilateral
          (left label) (right label) (field label)))
      (gaugeVectorOfList labels left right field)

  -- The decoder is a genuine two-sided finite codec. We need its
  -- vector roundtrip to replace an arbitrary vector by encode(decode v).
  actualGaugeVectorEncoded :
    (gamma : Gamma) (vector : Vec.Vec Link positiveBondCount) →
    Bilateral.gaugeBondVector theory oneLink bilateral
      (leftFactors gamma) (rightFactors gamma) vector
    ≡ nativeEncode
        (λ bond →
          Bilateral.gaugeOneLink theory oneLink bilateral
            (leftField gamma bond) (rightField gamma bond)
            (nativeDecode vector bond))
  actualGaugeVectorEncoded gamma vector =
    trans
      (cong
        (λ selected →
          Bilateral.gaugeBondVector theory oneLink bilateral
            (leftFactors gamma) (rightFactors gamma) selected)
        (sym (Codec.originalBondsEncodeDecodeExactly (suc n) vector)))
      (gaugeVectorOfList
        (Torus.elements (Codec.originalPositiveBondFinite (suc n)))
        (leftField gamma) (rightField gamma) (nativeDecode vector))

  actualGaugeVectorDecodedAt :
    (gamma : Gamma) (vector : Vec.Vec Link positiveBondCount) bond →
    nativeDecode
      (Bilateral.gaugeBondVector theory oneLink bilateral
        (leftFactors gamma) (rightFactors gamma) vector)
      bond
    ≡
    Bilateral.gaugeOneLink theory oneLink bilateral
      (leftField gamma bond) (rightField gamma bond)
      (nativeDecode vector bond)
  actualGaugeVectorDecodedAt gamma vector bond =
    trans
      (cong (λ selected → nativeDecode selected bond)
        (actualGaugeVectorEncoded gamma vector))
      (Codec.originalBondsDecodeEncodeAt (suc n)
        (λ label →
          Bilateral.gaugeOneLink theory oneLink bilateral
            (leftField gamma label) (rightField gamma label)
            (nativeDecode vector label))
        bond)

  -- PAY the original dependent physical naturality record, pointwise.
  -- No arbitrary lattice-level gauge/Haar transformation is assumed.
  constructedOriginalPeriodicGaugeNaturality :
    GaugeHaar.OriginalPeriodicGaugeVectorNaturality
      theory traceData exponential n beta oneLink bilateral
      nativeDecode divide
  constructedOriginalPeriodicGaugeNaturality = record
    { GaugeHaar.OriginalPeriodicGaugeVectorNaturality.leftFactors =
        leftFactors
    ; GaugeHaar.OriginalPeriodicGaugeVectorNaturality.rightFactors =
        rightFactors
    ; GaugeHaar.OriginalPeriodicGaugeVectorNaturality.gaugeDecodeAt =
        λ gamma vector → λ where
          (Torus.pair site axis) →
            trans
              (Core.multiplyAssociative (SUN.sunMatrixGroup theory)
                (gamma site)
                (nativeDecode vector (Torus.pair site axis))
                (SUN.sunInverse theory
                  (gamma (Bond.positiveStep site axis))))
              (sym (actualGaugeVectorDecodedAt
                gamma vector (Torus.pair site axis)))
    }

  actualPeriodicProductMeasure :
    Physical.PhysicalFiniteYMMeasure
      (Variable.SUNPeriodicLinks theory n) ℝ
  actualPeriodicProductMeasure =
    VariableHaar.periodicProductFiniteMeasure
      theory traceData exponential n beta oneLink nativeDecode divide

  -- The exact previous one-link -> all-link positivity compiler,
  -- now with the ORIGINAL decoder constructed rather than assumed.
  actualPeriodicPartitionPositive :
    Ordered.OneLinkStrictlyPositiveIntegration oneLink →
    0ℝ <ℝ Physical.partitionFunction actualPeriodicProductMeasure
  actualPeriodicPartitionPositive strict =
    VariableHaar.periodicProductPartitionStrictPositive
      theory traceData exponential n beta oneLink nativeDecode divide strict

  -- The one-link Haar left/right invariance now yields local gauge
  -- invariance on the same native physical source for every cutoff n.
  actualPeriodicGaugeHaar :
    (observable : Variable.SUNPeriodicLinks theory n → ℝ) →
    GaugeHaar.PeriodicPointwiseObservable
      theory traceData exponential n beta oneLink bilateral
      nativeDecode divide observable →
    (gamma : Gamma) →
    Physical.haarIntegral actualPeriodicProductMeasure
      (λ links →
        observable (Variable.periodicSUNGaugeTransform
          theory n links gamma))
    ≡ Physical.haarIntegral actualPeriodicProductMeasure observable
  actualPeriodicGaugeHaar observable pointwise gamma =
    GaugeHaar.periodicProductGaugeHaarInvariant
      theory traceData exponential n beta oneLink bilateral
      nativeDecode divide
      constructedOriginalPeriodicGaugeNaturality
      observable pointwise gamma

  actualPeriodicGaugeNormalized :
    (observable : Variable.SUNPeriodicLinks theory n → ℝ) →
    GaugeHaar.PeriodicPointwiseObservable
      theory traceData exponential n beta oneLink bilateral
      nativeDecode divide observable →
    (gamma : Gamma) →
    Physical.normalizedExpectation actualPeriodicProductMeasure
      (λ links →
        observable (Variable.periodicSUNGaugeTransform
          theory n links gamma))
    ≡ Physical.normalizedExpectation actualPeriodicProductMeasure observable
  actualPeriodicGaugeNormalized observable pointwise gamma =
    GaugeHaar.periodicGaugeNormalizedExpectationInvariant
      theory traceData exponential n beta oneLink bilateral
      nativeDecode divide
      constructedOriginalPeriodicGaugeNaturality
      observable pointwise gamma

  -- Literal source observable, not an independently supplied test: the
  -- original variable-size six-positive-plane Wilson deficit itself.
  actualSixDeficitPointwise :
    GaugeHaar.PeriodicPointwiseObservable
      theory traceData exponential n beta oneLink bilateral
      nativeDecode divide
      (Variable.periodicSUNSixDeficit theory traceData n)
  actualSixDeficitPointwise = record
    { GaugeHaar.PeriodicPointwiseObservable.congruentAt =
        Pointwise.variableSixWilsonDeficitPointwise theory traceData n
    }

  actualSixDeficitGaugeNormalized :
    (gamma : Gamma) →
    Physical.normalizedExpectation actualPeriodicProductMeasure
      (λ links →
        Variable.periodicSUNSixDeficit theory traceData n
          (Variable.periodicSUNGaugeTransform
            theory n links gamma))
    ≡ Physical.normalizedExpectation actualPeriodicProductMeasure
        (Variable.periodicSUNSixDeficit theory traceData n)
  actualSixDeficitGaugeNormalized =
    actualPeriodicGaugeNormalized
      (Variable.periodicSUNSixDeficit theory traceData n)
      actualSixDeficitPointwise
