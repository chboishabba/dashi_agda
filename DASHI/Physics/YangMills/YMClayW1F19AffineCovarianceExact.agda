module DASHI.Physics.YangMills.YMClayW1F19AffineCovarianceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban, "Large Field Renormalization. I", Communications in
-- Mathematical Physics 122 (1989), 175--202. DOI: 10.1007/BF01257412.
--
-- DASHI CONTRIBUTION
--
-- Weld the real affine determinant/covariance ledger to the actual
-- original F19 four conditional Haar columns.  Inverse/normalization is
-- carried explicitly as a pointwise right-inverse law; no field inverse
-- axiom or connected-covariance claim is postulated.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _-ℝ_;
   +-identityʳ; mulZeroˡ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceCoreExact as Trace
import DASHI.Physics.YangMills.YMClayStrictPositiveRealExponentialCoreExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact as Original
import DASHI.Physics.YangMills.YMClayW0OriginalF19CandidateEquation171TExact as W0
import DASHI.Physics.YangMills.YMClayRealAffineFibreHessianLedgerExact as Ledger
open import DASHI.Physics.YangMills.CompactLieProofLevel

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (source : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
    (linear : Ordered.OneLinkOrderedHaarAlgebra source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Pair : Set
  Pair = Fibre.Pair theory source bilateral

  FinePairField : Set
  FinePairField = Vec Pair 64

  FineTest : Set
  FineTest = Vec Pair 64 → Vec Link 896 → ℝ

  SlowField : Set
  SlowField = Vec Link 64

  density : FineTest
  density =
    W0.sourceFixedWilsonDensity
      theory traceData exponential beta source bilateral linear

  fineF : FineTest → FineTest
  fineF =
    Original.originalWilsonFineF
      theory traceData exponential beta source bilateral linear

  fineFG : FineTest → FineTest → FineTest
  fineFG =
    Original.originalWilsonFineFG
      theory traceData exponential beta source bilateral linear

  mass : FineTest → SlowField → ℝ
  mass =
    W0.candidateF19Mass
      theory traceData exponential beta source bilateral linear

  k0 : SlowField → ℝ
  k0 = W0.sourceK0 theory traceData exponential beta source bilateral linear

  kf : FineTest → SlowField → ℝ
  kf = W0.sourceKF theory traceData exponential beta source bilateral linear

  kg : FineTest → SlowField → ℝ
  kg = W0.sourceKG theory traceData exponential beta source bilateral linear

  kfg : FineTest → FineTest → SlowField → ℝ
  kfg = W0.sourceKFG theory traceData exponential beta source bilateral linear

  testAdd :
    FineTest → FineTest → FineTest
  testAdd left right pairs spectators =
    left pairs spectators +ℝ right pairs spectators

  testScale : ℝ → FineTest → FineTest
  testScale scalar observable pairs spectators =
    scalar *ℝ observable pairs spectators

  funAdd :
    ∀ {n} → (Vec Pair n → ℝ) → (Vec Pair n → ℝ) → Vec Pair n → ℝ
  funAdd left right pairs = left pairs +ℝ right pairs

  funScale : ∀ {n} → ℝ → (Vec Pair n → ℝ) → Vec Pair n → ℝ
  funScale scalar observable pairs = scalar *ℝ observable pairs

  spec : FineTest → FinePairField → ℝ
  spec integrand pairs = Product.productIntegral source (integrand pairs)

  specAdd :
    ∀ (left right : FineTest) (pairs : FinePairField) →
      spec (testAdd left right) pairs
      ≡ funAdd (spec left) (spec right) pairs
  specAdd left right pairs =
    Ordered.productIntegralAdd source linear (left pairs) (right pairs)

  specScale :
    ∀ (scalar : ℝ) (observable : FineTest) (pairs : FinePairField) →
      spec (testScale scalar observable) pairs
      ≡ funScale scalar (spec observable) pairs
  specScale scalar observable pairs =
    Ordered.productIntegralScale source linear scalar (observable pairs)

  fibreIntegralAdd :
    ∀ {n} (left right : Vec Pair n → ℝ) (coarse : Vec Link n) →
      Fibre.actualAllPairsFibreIntegral theory source bilateral
        (funAdd left right) coarse
      ≡ Fibre.actualAllPairsFibreIntegral theory source bilateral left coarse
        +ℝ Fibre.actualAllPairsFibreIntegral theory source bilateral right coarse
  fibreIntegralAdd {n = zero} left right [] = refl
  fibreIntegralAdd {n = suc n} left right (block ∷ blocks) =
    trans
      (Product.integrateCongruent source _ _
        (λ fibre →
          fibreIntegralAdd {n = n}
            (λ tail → left
              (Fibre.pairFromCoarseAndFibre theory source bilateral block fibre
                ∷ tail))
            (λ tail → right
              (Fibre.pairFromCoarseAndFibre theory source bilateral block fibre
                ∷ tail))
            blocks))
      (Ordered.oneAdd linear _ _)

  fibreIntegralScale :
    ∀ {n} (scalar : ℝ) (observable : Vec Pair n → ℝ)
      (coarse : Vec Link n) →
      Fibre.actualAllPairsFibreIntegral theory source bilateral
        (funScale scalar observable) coarse
      ≡ scalar *ℝ Fibre.actualAllPairsFibreIntegral
          theory source bilateral observable coarse
  fibreIntegralScale {n = zero} scalar observable [] = refl
  fibreIntegralScale {n = suc n} scalar observable (block ∷ blocks) =
    trans
      (Product.integrateCongruent source _ _
        (λ fibre →
          fibreIntegralScale {n = n} scalar
            (λ tail → observable
              (Fibre.pairFromCoarseAndFibre theory source bilateral block fibre
                ∷ tail))
            blocks))
      (Ordered.oneScale linear scalar _)

  sourceAffineIntegrand :
    FineTest → FineTest → ℝ → ℝ → FineTest
  sourceAffineIntegrand left right s t =
    testAdd
      (testAdd
        (testAdd density (testScale s (fineF left)))
        (testScale t (fineF right)))
      (testScale (s *ℝ t) (fineFG left right))

  sourceAffineMass : FineTest → FineTest → ℝ → ℝ → SlowField → ℝ
  sourceAffineMass left right s t = mass (sourceAffineIntegrand left right s t)

  spectatorAffineIntegral :
    ∀ (left right : FineTest) (s t : ℝ) (pairs : FinePairField) →
      spec (sourceAffineIntegrand left right s t) pairs
      ≡ funAdd
          (funAdd
            (funAdd (spec density) (funScale s (spec (fineF left))))
            (funScale t (spec (fineF right))))
          (funScale (s *ℝ t) (spec (fineFG left right))) pairs
  spectatorAffineIntegral left right s t pairs =
    trans
      (specAdd
        (testAdd
          (testAdd density (testScale s (fineF left)))
          (testScale t (fineF right)))
        (testScale (s *ℝ t) (fineFG left right)) pairs)
      (trans
        (cong
          (λ z → z +ℝ spec (testScale (s *ℝ t) (fineFG left right)) pairs)
          (specAdd
            (testAdd density (testScale s (fineF left)))
            (testScale t (fineF right)) pairs))
        (trans
          (cong
            (λ z → (z +ℝ spec (testScale t (fineF right)) pairs)
                    +ℝ spec (testScale (s *ℝ t) (fineFG left right)) pairs)
            (specAdd density (testScale s (fineF left)) pairs))
          (trans
            (cong
              (λ z → ((spec density pairs +ℝ z)
                       +ℝ spec (testScale t (fineF right)) pairs)
                       +ℝ spec (testScale (s *ℝ t) (fineFG left right)) pairs)
              (specScale s (fineF left) pairs))
            (trans
              (cong
                (λ z → ((spec density pairs
                          +ℝ s *ℝ spec (fineF left) pairs)
                         +ℝ z)
                         +ℝ spec (testScale (s *ℝ t) (fineFG left right)) pairs)
                (specScale t (fineF right) pairs))
              (cong
                (λ z → ((spec density pairs
                          +ℝ s *ℝ spec (fineF left) pairs)
                         +ℝ t *ℝ spec (fineF right) pairs)
                         +ℝ z)
                (specScale (s *ℝ t) (fineFG left right) pairs))))))

  sourceAffineMassIsAffine :
    ∀ (left right : FineTest) (s t : ℝ) (coarse : SlowField) →
      sourceAffineMass left right s t coarse
      ≡ Ledger.affineMass
          (k0 coarse) (kf left coarse) (kg right coarse)
          (kfg left right coarse) s t
  sourceAffineMassIsAffine left right s t coarse =
    trans
      (Fibre.originalFibreIntegralCongruent theory source bilateral linear
        (W0.spectatorMarginalOfFineIntegrand
          theory traceData exponential beta source bilateral linear
          (sourceAffineIntegrand left right s t))
        (funAdd
          (funAdd
            (funAdd (spec density) (funScale s (spec (fineF left))))
            (funScale t (spec (fineF right))))
          (funScale (s *ℝ t) (spec (fineFG left right))))
        (λ pairs → spectatorAffineIntegral left right s t pairs)
        coarse)
      (trans
        (fibreIntegralAdd
          (funAdd
            (funAdd (spec density) (funScale s (spec (fineF left))))
            (funScale t (spec (fineF right))))
          (funScale (s *ℝ t) (spec (fineFG left right))) coarse)
        (trans
          (cong
            (λ z → z +ℝ Fibre.actualAllPairsFibreIntegral theory source bilateral
              (funScale (s *ℝ t) (spec (fineFG left right))) coarse)
            (fibreIntegralAdd
              (funAdd (spec density) (funScale s (spec (fineF left))))
              (funScale t (spec (fineF right))) coarse))
          (trans
            (cong
              (λ z → (z +ℝ Fibre.actualAllPairsFibreIntegral theory source bilateral
                  (funScale t (spec (fineF right))) coarse)
                +ℝ Fibre.actualAllPairsFibreIntegral theory source bilateral
                  (funScale (s *ℝ t) (spec (fineFG left right))) coarse)
              (fibreIntegralAdd
                (spec density)
                (funScale s (spec (fineF left))) coarse))
            (trans
              (cong
                (λ z → ((Fibre.actualAllPairsFibreIntegral theory source bilateral
                    (spec density) coarse +ℝ z)
                  +ℝ Fibre.actualAllPairsFibreIntegral theory source bilateral
                    (funScale t (spec (fineF right))) coarse)
                  +ℝ Fibre.actualAllPairsFibreIntegral theory source bilateral
                    (funScale (s *ℝ t) (spec (fineFG left right))) coarse)
                (fibreIntegralScale s (spec (fineF left)) coarse))
              (trans
                (cong
                  (λ z → ((Fibre.actualAllPairsFibreIntegral theory source bilateral
                      (spec density) coarse
                    +ℝ s *ℝ Fibre.actualAllPairsFibreIntegral
                      theory source bilateral (spec (fineF left)) coarse)
                    +ℝ z)
                    +ℝ Fibre.actualAllPairsFibreIntegral theory source bilateral
                      (funScale (s *ℝ t) (spec (fineFG left right))) coarse)
                  (fibreIntegralScale t (spec (fineF right)) coarse))
                (cong
                  (λ z → ((Fibre.actualAllPairsFibreIntegral theory source bilateral
                      (spec density) coarse
                    +ℝ s *ℝ Fibre.actualAllPairsFibreIntegral
                      theory source bilateral (spec (fineF left)) coarse)
                    +ℝ t *ℝ Fibre.actualAllPairsFibreIntegral
                      theory source bilateral (spec (fineF right)) coarse)
                    +ℝ z)
                  (fibreIntegralScale (s *ℝ t) (spec (fineFG left right)) coarse)))))))

  sourceAffineMassAtZero :
    ∀ (left right : FineTest) (coarse : SlowField) →
      sourceAffineMass left right 0ℝ 0ℝ coarse ≡ k0 coarse
  sourceAffineMassAtZero left right coarse =
    trans
      (sourceAffineMassIsAffine left right 0ℝ 0ℝ coarse)
      (trans
        (cong
          (λ z → ((k0 coarse +ℝ z)
                  +ℝ (0ℝ *ℝ kg right coarse))
                  +ℝ ((0ℝ *ℝ 0ℝ) *ℝ kfg left right coarse))
          (mulZeroˡ (kf left coarse)))
        (trans
          (cong
            (λ z → (z +ℝ (0ℝ *ℝ kg right coarse))
                    +ℝ ((0ℝ *ℝ 0ℝ) *ℝ kfg left right coarse))
            (+-identityʳ (k0 coarse)))
          (trans
            (cong
              (λ z → (k0 coarse +ℝ z)
                      +ℝ ((0ℝ *ℝ 0ℝ) *ℝ kfg left right coarse))
              (mulZeroˡ (kg right coarse)))
            (trans
              (cong
                (λ z → z +ℝ ((0ℝ *ℝ 0ℝ) *ℝ kfg left right coarse))
                (+-identityʳ (k0 coarse)))
              (trans
                 (cong
                   (λ z → k0 coarse +ℝ z)
                   (trans
                     (cong (λ z → z *ℝ kfg left right coarse)
                       (mulZeroˡ 0ℝ))
                     (mulZeroˡ (kfg left right coarse))))
                 (+-identityʳ (k0 coarse)))))))

  sourceAffineDeterminant :
    ∀ (left right : FineTest) (s t : ℝ) (coarse : SlowField) →
      sourceAffineMass left right s t coarse
          *ℝ kfg left right coarse
        -ℝ (kf left coarse +ℝ t *ℝ kfg left right coarse)
          *ℝ (kg right coarse +ℝ s *ℝ kfg left right coarse)
      ≡ k0 coarse *ℝ kfg left right coarse
          -ℝ kf left coarse *ℝ kg right coarse
  sourceAffineDeterminant left right s t coarse =
    trans
      (cong
        (λ value → value *ℝ kfg left right coarse
          -ℝ (kf left coarse +ℝ t *ℝ kfg left right coarse)
            *ℝ (kg right coarse +ℝ s *ℝ kfg left right coarse))
        (sourceAffineMassIsAffine left right s t coarse))
      (Ledger.affineMassDeterminant
        (k0 coarse) (kf left coarse) (kg right coarse)
        (kfg left right coarse) s t)

  sourceAffineConnectedCovarianceAtZero :
    ∀ (left right : FineTest) (inv : SlowField → ℝ) →
      (∀ coarse → k0 coarse *ℝ inv coarse ≡ 1ℝ) →
      ∀ coarse →
        kfg left right coarse *ℝ inv coarse
          -ℝ (kf left coarse *ℝ inv coarse)
            *ℝ (kg right coarse *ℝ inv coarse)
        ≡ (k0 coarse *ℝ kfg left right coarse
            -ℝ kf left coarse *ℝ kg right coarse)
            *ℝ inv coarse *ℝ inv coarse
  sourceAffineConnectedCovarianceAtZero left right inv invLaw coarse =
    Ledger.covarianceInverseLedger
      (k0 coarse) (kf left coarse) (kg right coarse)
      (kfg left right coarse) (inv coarse) (invLaw coarse)

  sourceAffineTiltedConnectedCovarianceAtZero :
    ∀ (left right : FineTest) (s t : ℝ) (inv : SlowField → ℝ) →
      (∀ coarse →
        sourceAffineMass left right s t coarse *ℝ inv coarse ≡ 1ℝ) →
      ∀ coarse →
        kfg left right coarse *ℝ inv coarse
          -ℝ ((kf left coarse +ℝ t *ℝ kfg left right coarse) *ℝ inv coarse)
            *ℝ ((kg right coarse +ℝ s *ℝ kfg left right coarse) *ℝ inv coarse)
        ≡ (k0 coarse *ℝ kfg left right coarse
            -ℝ kf left coarse *ℝ kg right coarse)
            *ℝ inv coarse *ℝ inv coarse
  sourceAffineTiltedConnectedCovarianceAtZero left right s t inv invLaw coarse =
    Ledger.affineTiltedCovarianceInverseLedger
      (k0 coarse) (kf left coarse) (kg right coarse)
      (kfg left right coarse) s t (inv coarse)
      (trans
        (cong
          (λ value → value *ℝ inv coarse)
          (sym (sourceAffineMassIsAffine left right s t coarse)))
        (invLaw coarse))

  w1F19AffineCovarianceLevel : ProofLevel
  w1F19AffineCovarianceLevel = machineChecked

  w1F19NormalizationApplicationLevel : ProofLevel
  w1F19NormalizationApplicationLevel = conditional
