module DASHI.Physics.YangMills.YMClayOriginalWilsonSpatialC3TimeMirrorBIDIExact where

------------------------------------------------------------------------
-- YM P0: original R445 Wilson time mirror commutes with native spatial C3.
-- The temporal-link inverse is the ORIGINAL SU(N) group inverse,
-- not an invented unoriented reindexing.
-- Source owners: original R445 reflection, native 1024-bond C3,
-- original finite bond codec, original weighted Gram and Gram-row BIDI.
-- Exact pointwise/vector source written; Agda kernel NOT RUN.
-- No claim of weighted density invariance, complex OS RP or mass gap.
-- Credit: Wilson, Balaban, Osterwalder--Schrader, DASHI source owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Signed
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayFiniteNativeBondReindexingSafeExact as Reindex
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Single
import DASHI.Physics.YangMills.YMClayNativeSideFourC3VectorWeldExact as C3
import DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact as Sort
import DASHI.Physics.YangMills.YMClayOriginalWilsonC3WeightedHaarTransferExact as WilsonC3
import DASHI.Physics.YangMills.YMClayOriginalC3WeightedOSGramBidiExact as Gram
import DASHI.Physics.YangMills.YMClayOriginalC3GramRowEquivalenceBidiExact as Row
import DASHI.Physics.YangMills.YMClayOriginalR445ReflectedPointwiseWordWeldExact as Mirror
import DASHI.Physics.YangMills.YMClayR445SelectedTimeReflectionForwardExact as Geometry

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  FineLinks : Set
  FineLinks = Variable.SUNPeriodicLinks theory 3

  OriginalVec : Set
  OriginalVec = Vec.Vec Link Single.Count

  mirror : FineLinks → FineLinks
  mirror = Mirror.reflectOriginalFineLinks
    theory traceData exponential betaFine oneLink bilateral divide

  rotateField : FineLinks → FineLinks
  rotateField links bond = links (C3.forwardBond bond)

  -- Exact 4D geometry, split on all FOUR original positive axes.
  -- On axis 0 the original negativeStep and group inverse are retained.
  actualOriginalMirrorC3At :
    (links : FineLinks) (bond : Torus.PositiveBond Torus.four) →
    mirror (rotateField links) bond ≡
    rotateField (mirror links) bond
  actualOriginalMirrorC3At links
    (Torus.pair (Torus.pair (Torus.pair t x) (Torus.pair y z))
      Torus.zeroᵢ) = refl
  actualOriginalMirrorC3At links
    (Torus.pair (Torus.pair (Torus.pair t x) (Torus.pair y z))
      (Torus.sucᵢ Torus.zeroᵢ)) = refl
  actualOriginalMirrorC3At links
    (Torus.pair (Torus.pair (Torus.pair t x) (Torus.pair y z))
      (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl
  actualOriginalMirrorC3At links
    (Torus.pair (Torus.pair (Torus.pair t x) (Torus.pair y z))
      (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)))) = refl

  -- Pointwise replacement suffices, avoiding function extensionality.
  mirrorRespectsPointwise :
    (left right : FineLinks) →
    ((bond : Torus.PositiveBond Torus.four) → left bond ≡ right bond) →
    (bond : Torus.PositiveBond Torus.four) →
    mirror left bond ≡ mirror right bond
  mirrorRespectsPointwise left right same
      (Torus.pair site Torus.zeroᵢ) =
    cong (Bond.inverse (Signed.sunExactSignedLinkGroup theory))
      (same (Torus.pair
        (Bond.negativeStep (Geometry.reflectFineSite site)
          Torus.zeroᵢ)
        Torus.zeroᵢ))
  mirrorRespectsPointwise left right same
      (Torus.pair site (Torus.sucᵢ axis)) =
    same (Torus.pair
      (Geometry.reflectFineSite site) (Torus.sucᵢ axis))

  -- Original canonical 1024-bond source vector, not a second measure.
  mirrorVector : OriginalVec → OriginalVec
  mirrorVector values =
    Codec.encodeOriginalBonds Torus.four
      (mirror (Codec.decodeOriginalBonds Torus.four values))

  actualOriginalMirrorC3Vector :
    (values : OriginalVec) →
    mirrorVector (C3.forwardVector values) ≡
    C3.forwardVector (mirrorVector values)
  actualOriginalMirrorC3Vector values =
    Codec.originalBondsEncodePointwise Torus.four
      (mirror (Codec.decodeOriginalBonds Torus.four
        (C3.forwardVector values)))
      (λ bond → Codec.decodeOriginalBonds Torus.four
        (mirrorVector values) (C3.forwardBond bond))
      (λ bond →
        trans
          (mirrorRespectsPointwise
            (Codec.decodeOriginalBonds Torus.four (C3.forwardVector values))
            (rotateField (Codec.decodeOriginalBonds Torus.four values))
            (Reindex.reindexAt Torus.four C3.forwardBond values)
            bond)
          (trans
            (actualOriginalMirrorC3At
              (Codec.decodeOriginalBonds Torus.four values) bond)
            (sym (Codec.originalBondsDecodeEncodeAt Torus.four
              (mirror (Codec.decodeOriginalBonds Torus.four values))
              (C3.forwardBond bond)))))

  -- The old reflected-Gram theorem's C3/reflection premise is now
  -- derived for the original physical reflection, not assumed anew.
  originalMirrorDischargesGramCommutation :
    Gram.ReflectionCommutesWithOriginalSpatialC3
      theory traceData exponential betaFine oneLink divide mirrorVector
  originalMirrorDischargesGramCommutation = actualOriginalMirrorC3Vector

  -- Actual full-density invariance and canonical-label proof remain OPEN.
  originalMirrorWeightedGramC3 :
    Sort.constructedNativeC3CanonicalLabelGoal →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide →
    ∀ left right →
    Gram.originalReflectedGramEntry
      theory traceData exponential betaFine oneLink divide mirrorVector
      (Gram.rotate theory traceData exponential betaFine oneLink divide left)
      (Gram.rotate theory traceData exponential betaFine oneLink divide right)
    ≡ Gram.originalReflectedGramEntry
      theory traceData exponential betaFine oneLink divide mirrorVector
      left right
  originalMirrorWeightedGramC3 canonical density left right =
    Gram.originalReflectedGramC3Invariant
      theory traceData exponential betaFine oneLink divide
      mirrorVector actualOriginalMirrorC3Vector canonical density left right

  originalMirrorPreservesFullGramRows :
    Sort.constructedNativeC3CanonicalLabelGoal →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide →
    ∀ left right →
    Row.OriginalGramRowEquivalent
      theory traceData exponential betaFine oneLink divide
      mirrorVector left right →
    Row.OriginalGramRowEquivalent
      theory traceData exponential betaFine oneLink divide
      mirrorVector
      (Gram.rotate theory traceData exponential betaFine oneLink divide left)
      (Gram.rotate theory traceData exponential betaFine oneLink divide right)
  originalMirrorPreservesFullGramRows canonical density left right same =
    Row.originalC3PreservesAllGramRows
      theory traceData exponential betaFine oneLink divide
      mirrorVector actualOriginalMirrorC3Vector canonical density
      left right same

------------------------------------------------------------------------
-- Remaining: source density C3; canonical labels; full complex RP;
-- cutoff Gram convergence; same-E1 OS/Hilbert U_C3/T(t); D1-D2 gap.
------------------------------------------------------------------------
