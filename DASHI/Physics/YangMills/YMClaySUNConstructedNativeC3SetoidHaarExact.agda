module DASHI.Physics.YangMills.YMClaySUNConstructedNativeC3SetoidHaarExact where

------------------------------------------------------------------------
-- R443-C3: ORIGINAL side-four SUN native Haar codec, exact finite cut.
--
-- Old SUNNativeSetoidBondCodec required both a native encode/decode
-- correspondence and a c3DecodeAt theorem as externally supplied fields.
-- Both are now constructed from the canonical original 1024 bond list and
-- actual spatial C3 vector source. The ONLY remaining spatial C3
-- combinatorial input is a LinkPermutation syntax term that acts on vectors
-- exactly as the already-constructed selected native C3 reindexing.
--
-- This is a strict reduction of the original C3/Haar proof frontier:
-- no separate native C3 field equality and no global function extensionality.
-- It does NOT manufacture a normalized physical compact Haar integral.
-- Its one-link and Fubini laws remain the existing explicit source inputs.
--
-- The physically original Gibbs/C3 theorem is re-used directly, without
-- introducing another measure or Wilson action.
-- Wilson; Haar/Fubini; Bałaban; DASHI original code owners retain credit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayNativeSideFourC3VectorWeldExact as NativeC3
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClaySUNNativeSetoidBondProductHaarExact as Setoid
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (source : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Count : Nat
  Count = Codec.originalPositiveBondCount Torus.four

  Vector : Set
  Vector = Vec.Vec Link Count

  -- This is exactly the selected original coordinate C3, not a
  -- newly stipulated field map. A finite adjacent-swap program remains
  -- to be constructed/proved once, and has no analytic assumptions.
  record ExactC3AdjacentSwapWitness : Set where
    field
      program : Product.LinkPermutation Count
      matchesNativeVector :
        ∀ (vector : Vector) →
        Product.permuteLinks program vector
        ≡ NativeC3.forwardVector vector

  open ExactC3AdjacentSwapWitness public

  originalNativeC3SetoidCodec :
    ExactC3AdjacentSwapWitness →
    Setoid.SUNNativeSetoidBondCodec theory Count
  originalNativeC3SetoidCodec witness = record
    { Setoid.SUNNativeSetoidBondCodec.encode =
        Codec.encodeOriginalBonds Torus.four
    ; Setoid.SUNNativeSetoidBondCodec.decode =
        Codec.decodeOriginalBonds Torus.four
    ; Setoid.SUNNativeSetoidBondCodec.encodeDecode =
        Codec.originalBondsEncodeDecodeExactly Torus.four
    ; Setoid.SUNNativeSetoidBondCodec.decodeEncodeAt =
        Codec.originalBondsDecodeEncodeAt Torus.four
    ; Setoid.SUNNativeSetoidBondCodec.c3Permutation =
        program witness
    ; Setoid.SUNNativeSetoidBondCodec.c3DecodeAt =
        λ vector bond →
          trans
            (sym (NativeC3.nativeForwardIsVectorAt vector bond))
            (cong
              (λ selected →
                Codec.decodeOriginalBonds Torus.four selected bond)
              (sym (matchesNativeVector witness vector)))
    }

  -- Same original SU(N) six-plane Gibbs observable; use existing
  -- finite product-Haar permutation theorem via the constructed codec.
  originalNativeC3GibbsHaarInvariant :
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (witness : ExactC3AdjacentSwapWitness) →
    Setoid.nativeSetoidProductHaar source
      (originalNativeC3SetoidCodec witness)
      (λ links →
        let open import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact
        in nativeSUNWilsonGibbsDensity
          theory traceData exponential beta
          (DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact.nativeForwardC3Bonds links))
    ≡
    Setoid.nativeSetoidProductHaar source
      (originalNativeC3SetoidCodec witness)
      (DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact.nativeSUNWilsonGibbsDensity
        theory traceData exponential beta)
  originalNativeC3GibbsHaarInvariant traceData exponential beta witness =
    Setoid.nativeSUNPhysicalGibbsSetoidHaarC3
      theory traceData exponential beta
      source (originalNativeC3SetoidCodec witness)
