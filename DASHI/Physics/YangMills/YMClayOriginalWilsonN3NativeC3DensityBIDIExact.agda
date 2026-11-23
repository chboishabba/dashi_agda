module DASHI.Physics.YangMills.YMClayOriginalWilsonN3NativeC3DensityBIDIExact where

------------------------------------------------------------------------
-- YM P0: same original n=3 Wilson Gibbs density = native six-plane
-- source density, on the actual side-four SU(N) positive-bond carrier.
-- Flat fourfold source-site enumeration is transported to the ORIGINAL
-- native sumSitesReal, rather than assumed to be definitionally equal.
-- No arbitrary Wilson/Gibbs or extra CMP119 E/R/B/V weight is inserted.
-- The existing native real-inverse-trace C3 theorem supplies density
-- covariance. The native C3/vector codec supplies the field equality.
-- Original signed plaquette, flat sums, Wilson, C3, Haar, OS owners reused.
-- SOURCE WRITTEN; Agda kernel NOT RUN; no continuum, D1/D2, Clay claim.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; -ℝ_;
   +-assoc; +-identityˡ)

import Data.Vec.Base as Vec
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeInversePlaquetteRealTraceExact as Inverse
import DASHI.Physics.YangMills.YMClaySUNNativeSixPlaneFullC3FromInverseTraceExact as NativeC3
import DASHI.Physics.YangMills.YMClaySUNNativeWilsonBondPointwiseExact as Pointwise
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Single
import DASHI.Physics.YangMills.YMClayNativeSideFourC3VectorWeldExact as C3
import DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact as Sort
import DASHI.Physics.YangMills.YMClayOriginalWilsonC3WeightedHaarTransferExact as WilsonC3
import DASHI.Physics.YangMills.YMClayOriginalWilsonSpatialC3TimeMirrorBIDIExact as TimeMirror
import DASHI.Physics.YangMills.YMClayOriginalC3WeightedOSGramBidiExact as Gram
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN

------------------------------------------------------------------------
-- Actual flat original list to actual nested native 4^4 site-sum.
-- The extra additive identities from cartesian flattening are paid
-- using the source real additive laws, not a false 'refl'.
------------------------------------------------------------------------

realSumAppend :
  ∀ {A : Set} (xs ys : List A) (f : A → ℝ) →
  Sums.realSum (Torus._++_ xs ys) f
  ≡ Sums.realSum xs f +ℝ Sums.realSum ys f
realSumAppend [] ys f =
  sym (+-identityˡ (Sums.realSum ys f))
realSumAppend (x ∷ xs) ys f =
  trans
    (cong (f x +ℝ_) (realSumAppend xs ys f))
    (sym (+-assoc (f x) (Sums.realSum xs f) (Sums.realSum ys f)))

realSumMap :
  ∀ {A B : Set} (g : A → B) (xs : List A) (f : B → ℝ) →
  Sums.realSum (Torus.map g xs) f
  ≡ Sums.realSum xs (λ x → f (g x))
realSumMap g [] f = refl
realSumMap g (x ∷ xs) f =
  cong (f (g x) +ℝ_) (realSumMap g xs f)

realSumCartesian :
  ∀ {A B : Set} (xs : List A) (ys : List B)
    (f : Torus.Product A B → ℝ) →
  Sums.realSum (Torus.cartesian xs ys) f
  ≡ Sums.realSum xs
      (λ x → Sums.realSum ys (λ y → f (Torus.pair x y)))
realSumCartesian [] ys f = refl
realSumCartesian (x ∷ xs) ys f =
  trans
    (realSumAppend
      (Torus.map (λ y → Torus.pair x y) ys)
      (Torus.cartesian xs ys) f)
    (cong₂ _+ℝ_
      (realSumMap (λ y → Torus.pair x y) ys f)
      (realSumCartesian xs ys f))

Index4 : Set
Index4 = Torus.CyclicIndex Torus.four

Site4 : Set
Site4 = Torus.periodicTorus4Definition Torus.four

indices4 : List Index4
indices4 = Torus.allCyclicIndices Torus.four

pairs4 : List (Torus.Product Index4 Index4)
pairs4 = Torus.cartesian indices4 indices4

realSumFourIsNative :
  (f : Index4 → ℝ) →
  Sums.realSum indices4 f ≡ Gibbs.sumFourReal f
realSumFourIsNative f = refl

realSumFourfoldFlatToNested :
  (f : Site4 → ℝ) →
  Sums.realSum (Torus.elements (Torus.periodicTorus4Finite Torus.four)) f
  ≡ Sums.realSum indices4 (λ t →
      Sums.realSum indices4 (λ x →
        Sums.realSum indices4 (λ y →
          Sums.realSum indices4 (λ z →
            f (Torus.pair (Torus.pair t x) (Torus.pair y z))))))
realSumFourfoldFlatToNested f =
  trans
    (realSumCartesian pairs4 pairs4 f)
    (trans
      (Sums.realSumCong pairs4
        (λ (Torus.pair t x) →
          realSumCartesian indices4 indices4
            (λ (Torus.pair y z) →
              f (Torus.pair (Torus.pair t x) (Torus.pair y z)))))
      (realSumCartesian indices4 indices4
        (λ (Torus.pair t x) →
          Sums.realSum indices4 (λ y →
            Sums.realSum indices4 (λ z →
              f (Torus.pair (Torus.pair t x) (Torus.pair y z)))))))

realSumFourfoldNestedToNative :
  (f : Site4 → ℝ) →
  Sums.realSum indices4 (λ t →
    Sums.realSum indices4 (λ x →
      Sums.realSum indices4 (λ y →
        Sums.realSum indices4 (λ z →
          f (Torus.pair (Torus.pair t x) (Torus.pair y z))))))
  ≡ Gibbs.sumSitesReal f
realSumFourfoldNestedToNative f =
  trans
    (Sums.realSumCong indices4 (λ t →
      Sums.realSumCong indices4 (λ x →
        Sums.realSumCong indices4 (λ y →
          realSumFourIsNative
            (λ z → f (Torus.pair (Torus.pair t x) (Torus.pair y z)))))))
    (trans
      (Sums.realSumCong indices4 (λ t →
        Sums.realSumCong indices4 (λ x →
          realSumFourIsNative
            (λ y → Gibbs.sumFourReal
              (λ z → f (Torus.pair (Torus.pair t x) (Torus.pair y z)))))))
      (trans
        (Sums.realSumCong indices4 (λ t →
          realSumFourIsNative
            (λ x → Gibbs.sumFourReal (λ y →
              Gibbs.sumFourReal (λ z →
                f (Torus.pair (Torus.pair t x) (Torus.pair y z)))))))
        (realSumFourIsNative (λ t →
          Gibbs.sumFourReal (λ x →
            Gibbs.sumFourReal (λ y →
              Gibbs.sumFourReal (λ z →
                f (Torus.pair (Torus.pair t x) (Torus.pair y z)))))))))

realSumActualOriginalSiteIsNative :
  (f : Site4 → ℝ) →
  Sums.realSum (Torus.elements (Torus.periodicTorus4Finite Torus.four)) f
  ≡ Gibbs.sumSitesReal f
realSumActualOriginalSiteIsNative f =
  trans
    (realSumFourfoldFlatToNested f)
    (realSumFourfoldNestedToNative f)

------------------------------------------------------------------------
-- Same original SU(N) signed plaquette and entire original density.
------------------------------------------------------------------------

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (divide : ℝ → ℝ → ℝ)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  OriginalVec : Set
  OriginalVec = Vec.Vec Link Single.Count

  originalN3SixDeficitIsNative :
    (links : Variable.SUNPeriodicLinks theory 3) →
    Variable.periodicSUNSixDeficit theory traceData 3 links
    ≡ Gibbs.nativeSUNSixWilsonDeficit theory traceData links
  originalN3SixDeficitIsNative links =
    trans
      (Sums.realSumCong
        (Torus.elements (Torus.periodicTorus4Finite Torus.four))
        (λ site →
          Sums.realSumCong (Plaquette.ownedPeriodicPlaquettes site)
            (λ p →
              cong (1ℝ -ℝ_)
                (Variable.sideFourPlaquetteSameNativeWilsonTrace
                  theory traceData links p))))
      (realSumActualOriginalSiteIsNative
        (Gibbs.nativeSUNSixWilsonDeficitAt theory traceData links))

  originalN3DensityIsNative :
    (values : OriginalVec) →
    WilsonC3.actualOriginalFineWilsonDensity
      theory traceData exponential betaFine oneLink divide values
    ≡ Gibbs.nativeSUNWilsonGibbsDensity
        theory traceData exponential betaFine
        (Codec.decodeOriginalBonds Torus.four values)
  originalN3DensityIsNative values =
    cong
      (λ deficit → Exp.expReal exponential
        (-ℝ (betaFine *ℝ deficit)))
      (originalN3SixDeficitIsNative
        (Codec.decodeOriginalBonds Torus.four values))

  -- Exact original native vector/source-field compatibility is already
  -- in C3.nativeForwardIsVectorAt. Pointwise density transport avoids
  -- any function-extensionality principle for arbitrary link fields.
  originalActualGibbsC3FromNativeInverseTrace :
    Inverse.SUNRealTraceInverseOnNative theory traceData →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide
  originalActualGibbsC3FromNativeInverseTrace inverseLaw values =
    trans
      (originalN3DensityIsNative (C3.forwardVector values))
      (trans
        (Pointwise.nativeSUNGibbsDensityPointwise
          theory traceData exponential betaFine
          (Codec.decodeOriginalBonds Torus.four
            (C3.forwardVector values))
          (Weld.nativeForwardC3Bonds
            (Codec.decodeOriginalBonds Torus.four values))
          (C3.nativeForwardIsVectorAt values))
        (trans
          (NativeC3.nativeSUNWilsonGibbsDensityC3
            theory traceData inverseLaw exponential betaFine
            (Codec.decodeOriginalBonds Torus.four values))
          (sym (originalN3DensityIsNative values))))

  -- Original weighted-Haar theorem now needs the ORIGINAL inverse-trace
  -- donor + closed canonical permutation witness, rather than a separately
  -- assumed full pure-Wilson Gibbs density C3 covariance.
  originalWeightedC3FromNativeInverseTrace :
    Sort.constructedNativeC3CanonicalLabelGoal →
    Inverse.SUNRealTraceInverseOnNative theory traceData →
    ∀ observable →
      WilsonC3.actualOriginalFineNormalized
        theory traceData exponential betaFine oneLink divide
        (λ values → observable (C3.forwardVector values))
      ≡ WilsonC3.actualOriginalFineNormalized
          theory traceData exponential betaFine oneLink divide observable
  originalWeightedC3FromNativeInverseTrace canonical inverseLaw observable =
    WilsonC3.actualOriginalWeightedC3NormalizedInvariant
      theory traceData exponential betaFine oneLink divide
      canonical (originalActualGibbsC3FromNativeInverseTrace inverseLaw)
      observable

  -- No new reflection, Gram or measure: directly consume the previous
  -- ACTUAL R445 temporal mirror and its earlier original-gram C3 theorem.
  originalTimeMirrorRealGramC3FromNativeInverseTrace :
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink) →
    Sort.constructedNativeC3CanonicalLabelGoal →
    Inverse.SUNRealTraceInverseOnNative theory traceData →
    ∀ left right →
      Gram.originalReflectedGramEntry
        theory traceData exponential betaFine oneLink divide
        (TimeMirror.mirrorVector
          theory traceData exponential betaFine oneLink bilateral divide)
        (Gram.rotate
          theory traceData exponential betaFine oneLink divide left)
        (Gram.rotate
          theory traceData exponential betaFine oneLink divide right)
      ≡ Gram.originalReflectedGramEntry
          theory traceData exponential betaFine oneLink divide
          (TimeMirror.mirrorVector
            theory traceData exponential betaFine oneLink bilateral divide)
          left right
  originalTimeMirrorRealGramC3FromNativeInverseTrace
      bilateral canonical inverseLaw left right =
    TimeMirror.originalMirrorWeightedGramC3
      theory traceData exponential betaFine oneLink bilateral divide
      canonical (originalActualGibbsC3FromNativeInverseTrace inverseLaw)
      left right

------------------------------------------------------------------------
-- OPEN: original inverse-trace instantiation, canonical 1024-label
-- Agda proof, genuine SU(N) Borel Haar, complex OS RP/E1, T(t), D1/D2.
-- Extra CMP119 E/R/B/V terms, if selected, need separate C3 covariance.
------------------------------------------------------------------------
