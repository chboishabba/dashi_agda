module DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact where

------------------------------------------------------------------------
-- R443-H: ORIGINAL SU(N) POSITIVE BOND PRODUCT HAAR FROM ONE-LINK FUBINI.
--
-- Construction: integrate over a finite Vec of FULL SU(N) matrix elements
-- by the recursively defined productIntegral. A two-way vector/bond codec
-- and exact spatial C3 permutation give an integral directly over the
-- native side-four positive bonds. The full-lattice C3 change-of-variables
-- is DERIVED from one-link Fubini and concrete finite permutation induction.
--
-- SOURCE GAP: building a normalized Haar functional on real SU(N), proving
-- the selected 1024-positive-bond codec/C3 permutation and physical
-- source identification are still distinct proof obligations. This is not
-- a countable rational quaternion counting law or the 4D continuum limit.
--
-- Classical Haar/Fubini (Hall, "Lie Groups, Lie Algebras, and
-- Representations", Springer 2015, DOI 10.1007/978-3-319-13467-3);
-- Wilson 1974 DOI 10.1103/PhysRevD.10.2445; Bałaban 1985 CMP 99
-- DOI 10.1007/BF01466594. Finite-vector proof owned by DASHI.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 1ℝ)
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product

productIntegralCongruent :
  ∀ {Link : Set} {n : Nat}
    (source : Product.OneLinkProductHaar Link)
    (left right : Vec Link n → ℝ) →
  (∀ links → left links ≡ right links) →
  Product.productIntegral source left ≡ Product.productIntegral source right
productIntegralCongruent {n = zero} source left right pointwise =
  pointwise []
productIntegralCongruent {n = suc n} source left right pointwise =
  Product.integrateCongruent source _ _
    (λ link →
      productIntegralCongruent source
        (λ tail → left (link ∷ tail))
        (λ tail → right (link ∷ tail))
        (λ tail → pointwise (link ∷ tail)))

record SUNNativeBondProductCodec
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (linkCount : Nat) : Set₁ where
  field
    encode :
      Native.SUNSideFourLinks N theory →
      Vec (SUN.SUNMatrixElement theory) linkCount
    decode :
      Vec (SUN.SUNMatrixElement theory) linkCount →
      Native.SUNSideFourLinks N theory

    -- Two-sided identity. This is a real bond-coordinate enumeration,
    -- NOT an imported assumption of measure equality or compactness.
    decodeEncode : ∀ links → decode (encode links) ≡ links
    encodeDecode : ∀ vector → encode (decode vector) ≡ vector

    c3Permutation : Product.LinkPermutation linkCount
    c3Decode :
      ∀ vector →
      Weld.nativeForwardC3Bonds (decode vector)
      ≡ decode (Product.permuteLinks c3Permutation vector)

open SUNNativeBondProductCodec public

nativeSUNProductIntegral :
  ∀ {Matrix Complex : Set} {N linkCount : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    (source :
      Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (codec : SUNNativeBondProductCodec theory linkCount) →
  (Native.SUNSideFourLinks N theory → ℝ) → ℝ
nativeSUNProductIntegral source codec integrand =
  Product.productIntegral source (λ vector → integrand (decode codec vector))

-- No independent full-lattice Haar change-of-variables is supplied. The
-- proof consists only of an integral congruence and permutation induction.
nativeSUNProductIntegralSpatialC3Invariant :
  ∀ {Matrix Complex : Set} {N linkCount : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    (source :
      Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (codec : SUNNativeBondProductCodec theory linkCount)
    (integrand : Native.SUNSideFourLinks N theory → ℝ) →
  nativeSUNProductIntegral source codec
    (λ links → integrand (Weld.nativeForwardC3Bonds links))
  ≡ nativeSUNProductIntegral source codec integrand
nativeSUNProductIntegralSpatialC3Invariant source codec integrand =
  trans
    (productIntegralCongruent source _ _
      (λ vector → cong integrand (c3Decode codec vector)))
    (Product.productHaarPermutationInvariant source
      (c3Permutation codec) (λ vector → integrand (decode codec vector)))

-- If the supplied one-link integral is normalized, so is the N-link
-- full matrix product integral. No extra N-link normalization hypothesis.
nativeSUNProductIntegralUnit :
  ∀ {Matrix Complex : Set} {N linkCount : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    (source :
      Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (codec : SUNNativeBondProductCodec theory linkCount) →
  nativeSUNProductIntegral source codec (λ _ → 1ℝ)
  ≡ 1ℝ
nativeSUNProductIntegralUnit source codec =
  Product.productIntegralUnit source
