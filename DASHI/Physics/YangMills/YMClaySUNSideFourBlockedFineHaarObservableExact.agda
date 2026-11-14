module DASHI.Physics.YangMills.YMClaySUNSideFourBlockedFineHaarObservableExact where

------------------------------------------------------------------------
-- R445 selected real SU(N) FINITE BLOCK-PULLBACK integration theorem.
--
-- A non-Abelian coarse link on the original periodic side-two torus is
-- the ordered two-link holonomy of the original side-four SUN links.
-- This module pulls coarse Wilson/Gibbs observables back onto the
-- ACTUAL fine original side-four SU(N) Gibbs measure built in R443/R445.
--
-- The same finite physical measure / betaFine / original density / Haar
-- constructor is used, not a newly invented probability distribution.
-- Only the existing one-link Haar bilateral + product-Fubini assumptions
-- and same-carrier pointwise observable congruence are consumed.
--
-- Important: the expectation E_fine[F(block U)] is the pushforward
-- observable functional BY DEFINITION. It is NOT proved equal to a
-- coarse `exp(-betaCoarse * WilsonAction)` product-Haar law. Such an
-- equality generally requires an RG effective action with extra terms.
-- This module does not claim Haar existence on continuous SU(N), tightness,
-- Wilson measure disintegration, reflection positivity, or mass gap.
--
-- Provenance: Wilson, Bałaban, finite Haar/Fubini, original DASHI owners.
-- Source-written, exact Agda kernel / real postulate audit still pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
import Data.Fin.Base as Fin
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Data.Vec.Base using (Vec)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry as Cube
import DASHI.Physics.YangMills.BalabanBlockedPeriodicLattice as Blocked
import DASHI.Physics.YangMills.YMClayNativeBlockedPeriodicBondWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeSideFourTwoBlockEndpointExact as Endpoint
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as Congruence
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicBondPointwiseExact as Pointwise
import DASHI.Physics.YangMills.YMClaySUNConstructedPeriodicGaugeCodecExact as Constructed
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGaugeHaarExact as GaugeHaar
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact as SUNBlock
import DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact as Block
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedWilsonGaugeExact as WilsonBlock
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  FineLinks : Set
  FineLinks = Variable.SUNPeriodicLinks theory 3

  CoarseLinks : Set
  CoarseLinks = Variable.SUNPeriodicLinks theory 1

  selectedFineMeasure : Physical.PhysicalFiniteYMMeasure FineLinks ℝ
  selectedFineMeasure =
    Constructed.actualPeriodicProductMeasure
      theory traceData exponential 3 betaFine
      oneLink bilateral divide

  selectedBlock : FineLinks → CoarseLinks
  selectedBlock = SUNBlock.nativeSUNBlockLinks
    {m = 1} {l = 1} theory

  record CoarsePointwiseObservable (observable : CoarseLinks → ℝ) : Set where
    field
      sameAtAllBonds : ∀ left right →
        Pointwise.VariableBondPointwise theory 1 left right →
        observable left ≡ observable right

  open CoarsePointwiseObservable public

  -- ACTUAL original two-link blocked holonomy respects every original
  -- fine bond; hence a coarse pointwise test is still a fine pointwise test.
  blockedPullbackPointwise :
    ∀ (observable : CoarseLinks → ℝ)
      (ext : CoarsePointwiseObservable observable) →
    GaugeHaar.PeriodicPointwiseObservable
      theory traceData exponential 3 betaFine
      oneLink bilateral (Codec.decodeOriginalBonds 4) divide
      (λ fine → observable (selectedBlock fine))
  blockedPullbackPointwise observable ext = record
    { GaugeHaar.PeriodicPointwiseObservable.congruentAt =
        λ left right same →
          sameAtAllBonds ext
            (selectedBlock left) (selectedBlock right)
            (Block.nativeBlockedPositiveLinksPointwise
              (Native.sunExactSignedLinkGroup theory)
              left right same)
    }

  -- The same ORIGINAL fine product-Haar Gibbs integration law is used.
  -- The coarse observable is a pullback, not a claimed coarse Wilson
  -- Gibbs distribution. This theorem has no field-function equality axiom.
  originalFineMeasureBlockedGaugeInvariant :
    ∀ (observable : CoarseLinks → ℝ)
      (ext : CoarsePointwiseObservable observable)
      (gamma : Variable.SUNPeriodicGauge theory 3) →
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        observable
          (selectedBlock
            (Variable.periodicSUNGaugeTransform
              theory 3 fine gamma)))
    ≡
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine → observable (selectedBlock fine))
  originalFineMeasureBlockedGaugeInvariant observable ext gamma =
    Constructed.actualPeriodicGaugeNormalized
      theory traceData exponential 3 betaFine
      oneLink bilateral divide
      (λ fine → observable (selectedBlock fine))
      (blockedPullbackPointwise observable ext)
      gamma

  -- The ORIGINAL side-two Wilson action is a selected coarse observable;
  -- its pointwise congruence is already proved for every periodic n.
  blockedCoarseWilsonPointwise :
    (betaCoarse : ℝ) →
    CoarsePointwiseObservable
      (Variable.periodicSUNWilsonAction
        theory traceData 1 betaCoarse)
  blockedCoarseWilsonPointwise betaCoarse = record
    { sameAtAllBonds =
        Pointwise.variableWilsonActionPointwise
          theory traceData 1 betaCoarse
    }

  originalFineGibbsBlockedWilsonGaugeInvariant :
    ∀ betaCoarse
      (gamma : Variable.SUNPeriodicGauge theory 3) →
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        Variable.periodicSUNWilsonAction theory traceData 1 betaCoarse
          (selectedBlock
            (Variable.periodicSUNGaugeTransform
              theory 3 fine gamma)))
    ≡
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        Variable.periodicSUNWilsonAction theory traceData 1 betaCoarse
          (selectedBlock fine))
  originalFineGibbsBlockedWilsonGaugeInvariant betaCoarse gamma =
    originalFineMeasureBlockedGaugeInvariant
      (Variable.periodicSUNWilsonAction
        theory traceData 1 betaCoarse)
      (blockedCoarseWilsonPointwise betaCoarse)
      gamma

  blockedCoarseGibbsPointwise :
    (betaCoarse : ℝ) →
    CoarsePointwiseObservable
      (Variable.periodicSUNGibbsDensity
        theory traceData exponential 1 betaCoarse)
  blockedCoarseGibbsPointwise betaCoarse = record
    { sameAtAllBonds =
        Pointwise.variableGibbsDensityPointwise
          theory traceData exponential 1 betaCoarse
    }

  originalFineGibbsBlockedGibbsGaugeInvariant :
    ∀ betaCoarse
      (gamma : Variable.SUNPeriodicGauge theory 3) →
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        Variable.periodicSUNGibbsDensity
          theory traceData exponential 1 betaCoarse
          (selectedBlock
            (Variable.periodicSUNGaugeTransform
              theory 3 fine gamma)))
    ≡
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        Variable.periodicSUNGibbsDensity
          theory traceData exponential 1 betaCoarse
          (selectedBlock fine))
  originalFineGibbsBlockedGibbsGaugeInvariant betaCoarse gamma =
    originalFineMeasureBlockedGaugeInvariant
      (Variable.periodicSUNGibbsDensity
        theory traceData exponential 1 betaCoarse)
      (blockedCoarseGibbsPointwise betaCoarse)
      gamma

  ------------------------------------------------------------------------
  -- R445.F08: ALL original side-two site-gauge changes are induced by a
  -- fine side-four gauge, not merely the gauges already selected from a
  -- fine history. This strengthens F07 for the actual blocked SU(N) law.
  --
  -- The lift is pullback along the ORIGINAL Balaban M=L=2 coarse-site
  -- projection. Its restriction to block origins is proved to be the
  -- identity, using the existing cube/site + block/unblock roundtrips.
  -- No arbitrary gauge-extension or function-extensionality axiom.
  ------------------------------------------------------------------------

  FineSite : Set
  FineSite = Torus.periodicTorus4Definition 4

  CoarseSite : Set
  CoarseSite = Torus.periodicTorus4Definition 2

  zeroBlockOffset : Cube.Cube4 2
  zeroBlockOffset =
    Cube.cube4 Fin.zero Fin.zero Fin.zero Fin.zero

  selectedFineBlockOrigin : CoarseSite → FineSite
  selectedFineBlockOrigin =
    Block.fineBlockOrigin {m = 1} {l = 1}
      (Native.sunExactSignedLinkGroup theory)

  selectedCoarseSiteOfFine : FineSite → CoarseSite
  selectedCoarseSiteOfFine fine =
    Weld.cubeToSite
      (Blocked.coarseCube (Weld.blockNativeSite 2 2 fine))

  selectedCoarseSiteAtBlockOrigin :
    ∀ site →
    selectedCoarseSiteOfFine (selectedFineBlockOrigin site) ≡ site
  selectedCoarseSiteAtBlockOrigin site =
    trans
      (cong
        (λ blocked → Weld.cubeToSite (Blocked.coarseCube blocked))
        (Weld.blockNativeSiteAfterUnblock 2 2
          (Blocked.blockedCube4
            (Weld.siteToCube site) zeroBlockOffset)))
      (Weld.siteCubeRoundtrip site)

  liftOriginalCoarseGauge :
    Variable.SUNPeriodicGauge theory 1 →
    Variable.SUNPeriodicGauge theory 3
  liftOriginalCoarseGauge coarseGamma fineSite =
    coarseGamma (selectedCoarseSiteOfFine fineSite)

  blockLiftedCoarseGaugeAt :
    ∀ (coarseGamma : Variable.SUNPeriodicGauge theory 1) site →
    SUNBlock.nativeSUNBlockGauge {m = 1} {l = 1} theory
      (liftOriginalCoarseGauge coarseGamma) site
    ≡ coarseGamma site
  blockLiftedCoarseGaugeAt coarseGamma site =
    cong coarseGamma (selectedCoarseSiteAtBlockOrigin site)

  -- The ORIGINAL bond transformation depends on the gauge only at its
  -- source and target sites; pointwise equal site gauges give the same
  -- transformed link without equating whole gauge functions.
  coarseGaugeTransformRespectsPointwise :
    ∀ (links : CoarseLinks)
      (left right : Variable.SUNPeriodicGauge theory 1) →
    (∀ site → left site ≡ right site) →
    Pointwise.VariableBondPointwise theory 1
      (Variable.periodicSUNGaugeTransform theory 1 links left)
      (Variable.periodicSUNGaugeTransform theory 1 links right)
  coarseGaugeTransformRespectsPointwise links left right same
      (Torus.pair site axis) =
    cong₂
      (λ start finish →
        Bond.multiply (Native.sunExactSignedLinkGroup theory)
          (Bond.multiply (Native.sunExactSignedLinkGroup theory)
            start (links (Torus.pair site axis)))
          (Bond.inverse (Native.sunExactSignedLinkGroup theory) finish))
      (same site)
      (same (Bond.positiveStep site axis))

  selectedBlockedCoarseGaugeEquivariant :
    ∀ (fine : FineLinks)
      (coarseGamma : Variable.SUNPeriodicGauge theory 1) →
    Pointwise.VariableBondPointwise theory 1
      (selectedBlock
        (Variable.periodicSUNGaugeTransform theory 3 fine
          (liftOriginalCoarseGauge coarseGamma)))
      (Variable.periodicSUNGaugeTransform theory 1
        (selectedBlock fine) coarseGamma)
  selectedBlockedCoarseGaugeEquivariant fine coarseGamma bond =
    trans
      (Endpoint.sideFourSUNBlockGaugeCovariant theory fine
        (liftOriginalCoarseGauge coarseGamma) bond)
      (coarseGaugeTransformRespectsPointwise
        (selectedBlock fine)
        (SUNBlock.nativeSUNBlockGauge {m = 1} {l = 1} theory
          (liftOriginalCoarseGauge coarseGamma))
        coarseGamma
        (blockLiftedCoarseGaugeAt coarseGamma)
        bond)

  -- Congruence for the SAME selected fine Wilson/Gibbs product integral;
  -- it follows from the given one-link integrable-test congruence. No
  -- extra full-field measure equality or arbitrary integration law.
  selectedFineNormalizedExpectationCongruent :
    ∀ (left right : FineLinks → ℝ) →
    (∀ fine → left fine ≡ right fine) →
    Physical.normalizedExpectation selectedFineMeasure left
    ≡ Physical.normalizedExpectation selectedFineMeasure right
  selectedFineNormalizedExpectationCongruent left right same =
    cong
      (λ numerator →
        divide numerator (Physical.partitionFunction selectedFineMeasure))
      (Congruence.productIntegralCongruent oneLink
        (λ vector →
          Physical.density selectedFineMeasure
            (Codec.decodeOriginalBonds 4 vector)
          *ℝ left (Codec.decodeOriginalBonds 4 vector))
        (λ vector →
          Physical.density selectedFineMeasure
            (Codec.decodeOriginalBonds 4 vector)
          *ℝ right (Codec.decodeOriginalBonds 4 vector))
        (λ vector →
          cong
            (λ value →
              Physical.density selectedFineMeasure
                (Codec.decodeOriginalBonds 4 vector) *ℝ value)
            (same (Codec.decodeOriginalBonds 4 vector))))

  -- The pushed-forward finite functional is invariant under EVERY coarse
  -- site gauge, not just a preselected fine gauge. Crucially this does
  -- NOT identify the coarse distribution with bare Wilson/Gibbs Haar.
  selectedPushforwardAllCoarseGaugeInvariant :
    ∀ (observable : CoarseLinks → ℝ)
      (ext : CoarsePointwiseObservable observable)
      (coarseGamma : Variable.SUNPeriodicGauge theory 1) →
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        observable
          (Variable.periodicSUNGaugeTransform theory 1
            (selectedBlock fine) coarseGamma))
    ≡ Physical.normalizedExpectation selectedFineMeasure
        (λ fine → observable (selectedBlock fine))
  selectedPushforwardAllCoarseGaugeInvariant
      observable ext coarseGamma =
    trans
      (selectedFineNormalizedExpectationCongruent _ _
        (λ fine →
          sameAtAllBonds ext _ _
            (λ bond →
              sym
                (selectedBlockedCoarseGaugeEquivariant
                  fine coarseGamma bond))))
      (originalFineMeasureBlockedGaugeInvariant
        observable ext (liftOriginalCoarseGauge coarseGamma))

  selectedBlockedWilsonAllCoarseGaugeInvariant :
    ∀ (betaCoarse : ℝ)
      (coarseGamma : Variable.SUNPeriodicGauge theory 1) →
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        Variable.periodicSUNWilsonAction theory traceData 1 betaCoarse
          (Variable.periodicSUNGaugeTransform theory 1
            (selectedBlock fine) coarseGamma))
    ≡ Physical.normalizedExpectation selectedFineMeasure
        (λ fine →
          Variable.periodicSUNWilsonAction theory traceData 1 betaCoarse
            (selectedBlock fine))
  selectedBlockedWilsonAllCoarseGaugeInvariant betaCoarse coarseGamma =
    selectedPushforwardAllCoarseGaugeInvariant _
      (blockedCoarseWilsonPointwise betaCoarse) coarseGamma

  selectedBlockedGibbsAllCoarseGaugeInvariant :
    ∀ (betaCoarse : ℝ)
      (coarseGamma : Variable.SUNPeriodicGauge theory 1) →
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        Variable.periodicSUNGibbsDensity
          theory traceData exponential 1 betaCoarse
          (Variable.periodicSUNGaugeTransform theory 1
            (selectedBlock fine) coarseGamma))
    ≡ Physical.normalizedExpectation selectedFineMeasure
        (λ fine →
          Variable.periodicSUNGibbsDensity
            theory traceData exponential 1 betaCoarse
            (selectedBlock fine))
  selectedBlockedGibbsAllCoarseGaugeInvariant betaCoarse coarseGamma =
    selectedPushforwardAllCoarseGaugeInvariant _
      (blockedCoarseGibbsPointwise betaCoarse) coarseGamma

