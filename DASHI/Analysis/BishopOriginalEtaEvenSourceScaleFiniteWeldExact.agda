module DASHI.Analysis.BishopOriginalEtaEvenSourceScaleFiniteWeldExact where

------------------------------------------------------------------------
-- P2: original Bishop source even-index scaling, finite same-object weld.
--
-- The previously paid original eta/zeta identity has an EVEN TERM
-- contribution.  This proof turns precisely one original source-term
-- identity
--
--   a(2*k+1) ≈ scale * a(k)
--
-- into the all-cutoff equality
--
--   eta_(2*N) + scale*zeta_N + scale*zeta_N ≈ zeta_(2*N).
--
-- Here every sum is on the existing Bishop Cartesian complex carrier,
-- with zeta_N interpreted by the ORIGINAL Sequence.SeriesOf owner.
-- The supplied dyadic source identity is an explicit premise; it must
-- eventually be proved from ORIGINAL Bishop log(2n)=log 2+log n
-- and original exponential multiplication.  No convergence, analytic
-- continuation, division, Gamma, Xi, or RH is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import RealProperties as RP

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Eta
import DASHI.Analysis.BishopOriginalEtaZetaEvenCutoffSeriesWeldExact as Weld
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Analysis.BishopOriginalXiPolynomialReflectionSameCarrierExact as Xi
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

-- Preserve both coordinates of the ORIGINAL Bishop setoid.
complexAddBothCongruent :
  ∀ {a b c d : BC.BishopComplex} →
  Eta._≈C_ a b →
  Eta._≈C_ c d →
  Eta._≈C_ (BC._+C_ a c) (BC._+C_ b d)
complexAddBothCongruent first second =
  RP.+-cong (proj₁ first) (proj₁ second)
  ,
  RP.+-cong (proj₂ first) (proj₂ second)

originalZeroIsScaleTimesZero :
  (scale : BC.BishopComplex) →
  Eta._≈C_ BC.zeroC (BC._*C_ scale BC.zeroC)
originalZeroIsScaleTimesZero (BC.bishop-complex sr si) =
  (let open RP.ℝ-Solver in
   solve 2
     (λ a b →
       Κ 0ℚᵘ ⊜
         ((a ⊗ Κ 0ℚᵘ) ⊖ (b ⊗ Κ 0ℚᵘ)))
     RP.≃-refl sr si)
  ,
  (let open RP.ℝ-Solver in
   solve 2
     (λ a b →
       Κ 0ℚᵘ ⊜
         ((a ⊗ Κ 0ℚᵘ) ⊕ (b ⊗ Κ 0ℚᵘ)))
     RP.≃-refl sr si)

-- Genuine complex distributivity, rather than transporting only
-- the real coordinate or presuming intensional equality of reals.
originalScaleDistributesOverPair :
  (scale left right : BC.BishopComplex) →
  Eta._≈C_
    (BC._+C_ (BC._*C_ scale left) (BC._*C_ scale right))
    (BC._*C_ scale (BC._+C_ left right))
originalScaleDistributesOverPair
    (BC.bishop-complex sr si)
    (BC.bishop-complex lr li)
    (BC.bishop-complex rr ri) =
  (let open RP.ℝ-Solver in
   solve 6
     (λ a b c d e f →
       (((a ⊗ c) ⊖ (b ⊗ d)) ⊕
        ((a ⊗ e) ⊖ (b ⊗ f))) ⊜
       ((a ⊗ (c ⊕ e)) ⊖ (b ⊗ (d ⊕ f))))
     RP.≃-refl sr si lr li rr ri)
  ,
  (let open RP.ℝ-Solver in
   solve 6
     (λ a b c d e f →
       (((a ⊗ d) ⊕ (b ⊗ c)) ⊕
        ((a ⊗ f) ⊕ (b ⊗ e))) ⊜
       ((a ⊗ (d ⊕ f)) ⊕ (b ⊗ (c ⊕ e))))
     RP.≃-refl sr si lr li rr ri)

-- This is the *only* mathematical input needed for the finite
-- even-term scaling.  Its construction from original native
-- negative-log and exponential terms remains an analytic obligation.
OriginalDyadicSourceScale :
  (term : Nat → BC.BishopComplex) →
  BC.BishopComplex → Set
OriginalDyadicSourceScale term scale =
  (k : Nat) →
  Eta._≈C_
    (term (suc (Eta.twice k)))
    (BC._*C_ scale (term k))

-- The all-cutoff proof is induction on the ORIGINAL even-term prefix,
-- not a new summation operator or a rational-complex proxy.
originalEvenSourceScaleFinite :
  (term : Nat → BC.BishopComplex) →
  (scale : BC.BishopComplex) →
  OriginalDyadicSourceScale term scale →
  (n : Nat) →
  Eta._≈C_
    (Eta.originalEvenPositivePrefix term n)
    (BC._*C_ scale (Eta.originalBishopPrefix term n))
originalEvenSourceScaleFinite term scale dyadic zero =
  originalZeroIsScaleTimesZero scale
originalEvenSourceScaleFinite term scale dyadic (suc n) =
  Eta.≈C-trans
    (complexAddBothCongruent
      (originalEvenSourceScaleFinite term scale dyadic n)
      (dyadic n))
    (originalScaleDistributesOverPair scale
      (Eta.originalBishopPrefix term n)
      (term n))

-- Instantiate the very same source native zeta finite prefix.
originalEvenSourceScaleNativePartial :
  (terms : Dirichlet.BishopDirichletTermFamily) →
  (s scale : BC.BishopComplex) →
  OriginalDyadicSourceScale (terms s) scale →
  (n : Nat) →
  Eta._≈C_
    (Eta.originalEvenPositivePrefix (terms s) n)
    (BC._*C_ scale (Dirichlet.dirichletPartial terms s n))
originalEvenSourceScaleNativePartial terms s scale dyadic n =
  Eta.≈C-trans
    (originalEvenSourceScaleFinite (terms s) scale dyadic n)
    (Xi.complexMultiplyCongruent
      (Xi.complexRefl scale)
      (Weld.originalBishopPrefixIsNativeSeries (terms s) n))

-- All terms, all n, ORIGINAL eta and ORIGINAL Bishop SeriesOf.
-- Once the dyadic identity is paid, no further finite algebra is needed.
originalEtaScaleToNativeZetaEvenCutoff :
  (terms : Dirichlet.BishopDirichletTermFamily) →
  (s scale : BC.BishopComplex) →
  OriginalDyadicSourceScale (terms s) scale →
  (n : Nat) →
  Eta._≈C_
    (BC._+C_
      (Eta.originalEtaPrefix (terms s) n)
      (BC._+C_
        (BC._*C_ scale (Dirichlet.dirichletPartial terms s n))
        (BC._*C_ scale (Dirichlet.dirichletPartial terms s n))))
    (Dirichlet.dirichletPartial terms s (Eta.twice n))
originalEtaScaleToNativeZetaEvenCutoff terms s scale dyadic n =
  Eta.≈C-trans
    (Xi.complexAddLeftCongruent
      (Eta.originalEtaPrefix (terms s) n)
      (complexAddBothCongruent
        (Eta.≈C-sym (originalEvenSourceScaleNativePartial
          terms s scale dyadic n))
        (Eta.≈C-sym (originalEvenSourceScaleNativePartial
          terms s scale dyadic n))))
    (Weld.originalEtaAndEvenTermsIsNativeZetaPartial terms s n)

-- The source-specialized consumer uses the existing Round11
-- negative-log/exponential term family.  The source dyadic input
-- remains independent and is NEVER inferred from a generic record.
module OriginalRound11
  (inputs : Round11.Round11BishopCutset)
  where

  module Selected = Eta.OriginalRound11DirichletEta inputs

  actualOriginalRound11EtaFiniteScaleBridge :
    (s scale : BC.BishopComplex) →
    OriginalDyadicSourceScale (Selected.sourceTerms s) scale →
    (n : Nat) →
    Eta._≈C_
      (BC._+C_
        (Eta.originalEtaPrefix (Selected.sourceTerms s) n)
        (BC._+C_
          (BC._*C_ scale (Dirichlet.dirichletPartial Selected.sourceTerms s n))
          (BC._*C_ scale (Dirichlet.dirichletPartial Selected.sourceTerms s n))))
      (Dirichlet.dirichletPartial Selected.sourceTerms s
        (Eta.twice n))
  actualOriginalRound11EtaFiniteScaleBridge s scale dyadic n =
    originalEtaScaleToNativeZetaEvenCutoff
      Selected.sourceTerms s scale dyadic n

-- Remaining source-native P2 gates:
-- 1. Prove dyadic source equality with scale = 2^(-s) from genuine
--    log multiplicativity and original exp product (cross-PR donor).
-- 2. Establish eta compact-uniform convergence for Re(s)>0 from a
--    *correct* complex-parameter majorant, not 2/(N+1)^sigma.
-- 3. Construct the infinite limit and factor identity, all divisor
--    zeros/removable singularities, and independently selected zeta.
-- 4. Typecheck this source with pinned Agda 2.9 and its imports.
