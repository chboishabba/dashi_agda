module DASHI.Physics.YangMills.YMClayY369OriginalSingerWilsonFourMarkSourceWeldExact where

------------------------------------------------------------------------
-- CLAY YM P0: same-ORIGINAL Wilson source, indexed signed geometric
-- chart, original 1024 fine links / all 1536 physical plaquettes,
-- and ONE same Wilson Haar functional for all 1/F/G/FG marks.
--
-- Reuse original 369 typed signed-zero gauge-fibre + original R445/F19
-- full-bond bijection, original finite Wilson-weighted Haar, and the
-- existing original marked sorted source. No second hyperfabric
-- gauge theory, no NEW physical transfer operator, no new Haar law.
--
-- RH #1533 stage-k Singer word is reproduced as a *small expression*
-- over the EXISTING master Sah/Griess grade and antipode operations.
-- RH's module itself is unmerged; no invented 27-point carrier.
-- t (history/physical clock label), k (chart index) and x (original
-- Euclidean 4-torus site including its time direction) are DISTINCT.
--
-- Source-written Agda only, kernel/trust receipt not yet obtained.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)
import Data.Vec.Base as Vec

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as H9
import DASHI.Moonshine.Griess1990MoufangCoherentSL3SectionSourceExact as Sah
import DASHI.Unified.Hyperfabric27MinusOneAntipodalSameCarrierCutExact as Antipode
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as T
import DASHI.Physics.YangMills.YMClayR445OriginalAxialBondParityInjectiveExact as R445
import DASHI.Physics.YangMills.YMClayR445Base2ThreeAxis369FibreBIDIExact as Fib
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as OriginalWilson
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact as Original
import DASHI.Physics.YangMills.YMClayOriginalWilsonCanonicalMarkedReindexExact as Mark

------------------------------------------------------------------------
-- Y369.1. Use EXACT native Griess/Sah source geometry, not a fabricated
-- Singer permutation. Carry the source zero branch separately.
------------------------------------------------------------------------

toExistingSSP : Fib.OriginalSignedQuadZeroBranch → SSP.SSPTrit
toExistingSSP Fib.sourceNegative = SSP.sspNegOne
toExistingSSP (Fib.sourceZeroWith _) = SSP.sspZero
toExistingSSP Fib.sourcePositive = SSP.sspPosOne

sourceNinePoint : Fib.OriginalFourSignedZeroBranches → H9.TernaryHyperformalPoint
sourceNinePoint (Fib.sourceFourSigned a b c d) =
  H9.ternaryHyperformalPoint
    (H9.ternary27Point (toExistingSSP a) (toExistingSSP b) (toExistingSSP c))
    (H9.ternary27Point (toExistingSSP d) SSP.sspZero SSP.sspZero)
    H9.origin

-- EXACT same order-26 RH word: antipode ∘ e20 ∘ e12 ∘ e01.
originalGrade26 : H9.Ternary27Point → H9.Ternary27Point
originalGrade26 p =
  Antipode.antipode
    (Sah.gradeShear Sah.e20
      (Sah.gradeShear Sah.e12
        (Sah.gradeShear Sah.e01 p)))

originalGradeMove9 : H9.TernaryHyperformalPoint → H9.TernaryHyperformalPoint
originalGradeMove9 (H9.ternaryHyperformalPoint interaction a b) =
  H9.ternaryHyperformalPoint
    (originalGrade26 interaction)
    (originalGrade26 a)
    (originalGrade26 b)

originalGradeIterate9 : Nat → H9.TernaryHyperformalPoint → H9.TernaryHyperformalPoint
originalGradeIterate9 zero p = p
originalGradeIterate9 (suc k) p =
  originalGradeMove9 (originalGradeIterate9 k p)

sourceIndexedSite : Nat → R445.Site4 → H9.TernaryHyperformalPoint
sourceIndexedSite k site =
  originalGradeIterate9 k
    (sourceNinePoint (Fib.originalSourceSiteToFourSignedBranches site))

-- The *original bond* determines incidence; not a fixed P3^9 edge.
sourceIndexedOriginalBondEndpoints :
  Nat → R445.FineBond →
  H9.TernaryHyperformalPoint × H9.TernaryHyperformalPoint
sourceIndexedOriginalBondEndpoints k (T.pair site axis) =
  (sourceIndexedSite k site ,
   sourceIndexedSite k (Fib.originalTargetOfFullBinaryAddress
                         (Fib.decodeOriginalFine (T.pair site axis))))

sourceIndexedOriginalAddressEndpoints :
  Nat → Fib.OriginalBinaryAddress →
  H9.TernaryHyperformalPoint × H9.TernaryHyperformalPoint
sourceIndexedOriginalAddressEndpoints k address =
  (sourceIndexedSite k (Fib.originalSourceOfFullBinaryAddress address) ,
   sourceIndexedSite k (Fib.originalTargetOfFullBinaryAddress address))

-- Source native k-square is NONTRIVIAL on the 9D grade; it is
-- definitionally natural because the ORIGINAL edge is carried too.
sourceIndexedAddressRefinementSquare :
  ∀ k address →
  sourceIndexedOriginalAddressEndpoints (suc k) address
  ≡
  (originalGradeMove9
    (proj₁ (sourceIndexedOriginalAddressEndpoints k address)) ,
   originalGradeMove9
    (proj₂ (sourceIndexedOriginalAddressEndpoints k address)))
sourceIndexedAddressRefinementSquare k address = refl

------------------------------------------------------------------------
-- Y369.2: actual original Wilson product-Haar integration on the
-- ORIGINAL full 1024 field: no measure is introduced on a new graph.
-- Stage k and physical history time t are retained as separate labels.
------------------------------------------------------------------------

module _
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
  (exponential : Exp.StrictPositiveRealExponential)
  (beta : ℝ)
  (source : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  OriginalVector : Set
  OriginalVector = Vec.Vec Link (Codec.originalPositiveBondCount 4)

  sourceCanonicalField : OriginalVector → R445.FineBond → Link
  sourceCanonicalField = Codec.decodeOriginalBonds 4

  indexedSourceLink :
    ∀ {Time : Set} → Time → Nat → OriginalVector →
    Fib.OriginalBinaryAddress →
    (Time × Nat) ×
      ((H9.TernaryHyperformalPoint × H9.TernaryHyperformalPoint) × Link)
  indexedSourceLink t k original address =
    (t , k) ,
    (sourceIndexedOriginalAddressEndpoints k address ,
     sourceCanonicalField original (Fib.encodeOriginalFine address))

  -- The sole recovery path for EVERY original positive fine link:
  -- the source k/time/indexed point is never mistaken for a new bond,
  -- and 896 spectator source labels are never quotiented away.
  recoverCanonicalFromIndexed :
    ∀ {Time : Set} → Time → Nat → OriginalVector → OriginalVector
  recoverCanonicalFromIndexed t k original =
    Codec.encodeOriginalBonds 4
      (λ bond →
        proj₂ (proj₂
          (indexedSourceLink t k original (Fib.decodeOriginalFine bond))))

  sourceIndexedLinkRecoversOriginal :
    ∀ {Time : Set} (t : Time) k original →
    recoverCanonicalFromIndexed t k original ≡ original
  sourceIndexedLinkRecoversOriginal t k original =
    trans
      (Codec.listValuesCong
        (T.elements (Codec.originalPositiveBondFinite 4))
        (λ bond →
          proj₂ (proj₂
            (indexedSourceLink t k original (Fib.decodeOriginalFine bond))))
        (sourceCanonicalField original)
        (λ bond →
          cong (sourceCanonicalField original)
            (Fib.originalFineRoundTrip bond)))
      (Codec.originalBondsEncodeDecodeExactly 4 original)

  -- ACTUAL ORIGINAL 4D plaquette and six-plane action, not only the
  -- scalar Gibbs-density equality. In particular this holds at EACH
  -- original of the 1536 positive oriented Wilson plaquette labels;
  -- original path orientation and spectator interactions are unchanged.
  originalIndexedPlaquetteIsOriginal :
    ∀ {Time : Set} (t : Time) k original
      (plaquette : Plaquette.PeriodicPlaquette 3) →
    OriginalWilson.periodicSUNPositivePlaquette
      theory 3
      (Codec.decodeOriginalBonds 4
        (recoverCanonicalFromIndexed t k original)) plaquette
    ≡
    OriginalWilson.periodicSUNPositivePlaquette
      theory 3 (Codec.decodeOriginalBonds 4 original) plaquette
  originalIndexedPlaquetteIsOriginal t k original plaquette =
    cong
      (λ vector →
        OriginalWilson.periodicSUNPositivePlaquette
          theory 3 (Codec.decodeOriginalBonds 4 vector) plaquette)
      (sourceIndexedLinkRecoversOriginal t k original)

  originalIndexedSixPlaneWilsonDeficitIsOriginal :
    ∀ {Time : Set} (t : Time) k original →
    OriginalWilson.periodicSUNSixDeficit
      theory traceData 3
      (Codec.decodeOriginalBonds 4
        (recoverCanonicalFromIndexed t k original))
    ≡
    OriginalWilson.periodicSUNSixDeficit
      theory traceData 3
      (Codec.decodeOriginalBonds 4 original)
  originalIndexedSixPlaneWilsonDeficitIsOriginal t k original =
    cong
      (λ vector →
        OriginalWilson.periodicSUNSixDeficit
          theory traceData 3 (Codec.decodeOriginalBonds 4 vector))
      (sourceIndexedLinkRecoversOriginal t k original)

  actualOriginalWilsonWeight : OriginalVector → ℝ
  actualOriginalWilsonWeight =
    Original.originalWilsonVectorWeight theory traceData exponential beta

  originalIndexedWilsonWeight :
    ∀ {Time : Set} → Time → Nat → OriginalVector → ℝ
  originalIndexedWilsonWeight t k original =
    actualOriginalWilsonWeight (recoverCanonicalFromIndexed t k original)

  originalWilsonActionDensityIndexedEqualsOriginal :
    ∀ {Time : Set} (t : Time) k original →
    originalIndexedWilsonWeight t k original
      ≡ actualOriginalWilsonWeight original
  originalWilsonActionDensityIndexedEqualsOriginal t k original =
    cong actualOriginalWilsonWeight
      (sourceIndexedLinkRecoversOriginal t k original)

  -- Partition Z is transported as its own physical source
  -- coefficient, not tacitly declared equal to a second measure.
  originalIndexedWilsonPartition :
    ∀ {Time : Set} → Time → Nat → ℝ
  originalIndexedWilsonPartition t k =
    Haar.productIntegral source (originalIndexedWilsonWeight t k)

  originalIndexedWilsonPartitionIsOriginal :
    ∀ {Time : Set} (t : Time) k →
    originalIndexedWilsonPartition t k
    ≡ Haar.productIntegral source actualOriginalWilsonWeight
  originalIndexedWilsonPartitionIsOriginal t k =
    Original.productIntegralCongruent source
      (originalIndexedWilsonWeight t k)
      actualOriginalWilsonWeight
      (originalWilsonActionDensityIndexedEqualsOriginal t k)

  -- A single actual Wilson Haar density and a single original source
  -- partition for all fine-field 1,F,G,F*G. Nothing is integrated
  -- independently or recast as a new hyperfabric probability space.
  originalIndexedWilsonMarkedNumerator :
    ∀ {Time : Set} → Time → Nat →
    (OriginalVector → ℝ) → ℝ
  originalIndexedWilsonMarkedNumerator t k mark =
    Haar.productIntegral source
      (λ original →
        originalIndexedWilsonWeight t k original *ℝ
        mark (recoverCanonicalFromIndexed t k original))

  -- The already-existing ORIGINAL F19 theorem takes a mark on the
  -- SORTED source vector. Restore the original canonical mark using
  -- the SOURCE-PROVED INVERSE permutation; do not mis-apply a mark to
  -- a field in the other coordinate order.
  originalSortedPullbackMark :
    (OriginalVector → ℝ) → OriginalVector → ℝ
  originalSortedPullbackMark mark sorted =
    mark
      (Haar.permuteLinks
        (Original.inverseProgram (Original.actualPairProgram theory))
        sorted)

  originalCanonicalWilsonMarkedNumerator :
    (OriginalVector → ℝ) → ℝ
  originalCanonicalWilsonMarkedNumerator mark =
    Mark.canonicalOriginalMarkedNumerator
      theory traceData exponential beta source
      (originalSortedPullbackMark mark)

  originalIndexedWilsonNumeratorIsOriginal :
    ∀ {Time : Set} (t : Time) k mark →
    originalIndexedWilsonMarkedNumerator t k mark
    ≡ originalCanonicalWilsonMarkedNumerator mark
  originalIndexedWilsonNumeratorIsOriginal t k mark =
    Original.productIntegralCongruent source
      (λ original →
        originalIndexedWilsonWeight t k original *ℝ
        mark (recoverCanonicalFromIndexed t k original))
      (λ original →
        actualOriginalWilsonWeight original *ℝ mark original)
      (λ original →
        cong₂ _*ℝ_
          (originalWilsonActionDensityIndexedEqualsOriginal t k original)
          (trans
            (cong mark (sourceIndexedLinkRecoversOriginal t k original))
            (sym
              (cong mark
                (Original.inverseAfterForward
                  (Original.actualPairProgram theory) original)))))

  originalIndexedWilsonFourMoments :
    ∀ {Time : Set} (t : Time) k
      (f g : OriginalVector → ℝ) →
    originalIndexedWilsonMarkedNumerator t k f
      ≡ originalCanonicalWilsonMarkedNumerator f
    ×
    (originalIndexedWilsonMarkedNumerator t k g
      ≡ originalCanonicalWilsonMarkedNumerator g)
    ×
    (originalIndexedWilsonMarkedNumerator t k
      (λ v → f v *ℝ g v)
      ≡ originalCanonicalWilsonMarkedNumerator
         (λ v → f v *ℝ g v))
  originalIndexedWilsonFourMoments t k f g =
    originalIndexedWilsonNumeratorIsOriginal t k f ,
    originalIndexedWilsonNumeratorIsOriginal t k g ,
    originalIndexedWilsonNumeratorIsOriginal t k
      (λ v → f v *ℝ g v)

  -- Already-constructed original F19 adjacent-swap physical density:
  -- the SAME original partition and marked observables go to the
  -- sorted F19 source; no CMP119 localized T is inferred.
  originalIndexedWilsonNormalizedEqualsOriginalF19 :
    ∀ {Time : Set} (t : Time) k
      (divide : ℝ → ℝ → ℝ)
      (mark : OriginalVector → ℝ) →
    divide
      (originalIndexedWilsonMarkedNumerator t k mark)
      (originalIndexedWilsonPartition t k)
    ≡
    Mark.sortedOriginalMarkedNormalized
      theory traceData exponential beta source divide
      (originalSortedPullbackMark mark)
  originalIndexedWilsonNormalizedEqualsOriginalF19
    t k divide mark =
    trans
      (cong₂ divide
        (originalIndexedWilsonNumeratorIsOriginal t k mark)
        (originalIndexedWilsonPartitionIsOriginal t k))
      (Mark.originalCanonicalMarkedNormalizedIsSorted
        theory traceData exponential beta source divide
        (originalSortedPullbackMark mark))

  -- This is a real ORIGINAL-SOURCE functional, NOT a new time/grade
  -- dependent Wilson Boltzmann weight. Our chart k is not a Balaban
  -- RG step, and none of this constructs CMP119 source domains,
  -- absolute UV-uniform CMP116 W3, or a continuum OS mass gap.
