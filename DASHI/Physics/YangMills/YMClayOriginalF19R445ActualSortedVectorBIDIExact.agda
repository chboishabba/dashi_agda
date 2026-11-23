module DASHI.Physics.YangMills.YMClayOriginalF19R445ActualSortedVectorBIDIExact where

------------------------------------------------------------------------
-- YM P0 F19 → R445: ORIGINAL 1024-site link-VALUE commuting square.
--
-- TOP: original F19 physical constructed adjacent-swap permutation.
-- LEFT: actual canonical original 1024 positive-bond decoder.
-- BOTTOM: original R445 selected-128 + residual-896 encoded vector.
--
-- Master original F19 reindex source:
-- YMClayNative1024ClosedReindexHaarConsequencesExact
--   .actualPairSpectatorReindexEveryOriginalVector.
-- Master original R445 field codec:
-- YMClayR445CanonicalBondPermutationCodecExact
--   .originalR445CanonicalToPairResidual.
-- All-1024 ordered label equality: #1536 existing
-- YMClayOriginalF19R445Full1024LabelsP0Exact
--   .originalF19Complete1024LabelOrderMatchesR445.
--
-- This does not replace the original Yang-Mills measure, drop the
-- 896 interacting spectators, commute SU(N) links, or assume a
-- source-free permutation. Genuine kernel acceptance NOT run.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Vec.Base as Vec

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClayNativeSideFourPairSpectatorSortProgramExact as F19
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Single
import DASHI.Physics.YangMills.YMClayNativeClosedThreeEqualitiesCandidateExact as Closed
import DASHI.Physics.YangMills.YMClayNative1024ClosedReindexHaarConsequencesExact as Sorted
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayOriginalF19R445Full1024LabelsP0Exact as OriginalLabels
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as R445
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec

module _
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  -- F19's original certified target Vec is the same source-owned
  -- complete ordered R445 target under the ORIGINAL canonical
  -- 1024-link label decoder. No independent Vec order postulate.
  originalF19TargetVectorValuesAreR445 :
    ∀ {Value : Set} (original : Vec.Vec Value Single.Count) →
    Vec.map (Codec.decodeOriginalBonds 4 original)
      (F19.originalPairSpectatorTargetVector
        theory (Closed.originalPairSpectatorLengthClosed theory))
    ≡ R445.originalR445CanonicalToPairResidual original
  originalF19TargetVectorValuesAreR445 original
    rewrite OriginalLabels.originalF19Complete1024LabelOrderMatchesR445
      theory = refl

  -- The physical F19 permutation program, not a fresh arrangement,
  -- commutes with the R445 canonical-to-selected+residual codec on
  -- ANY original 1024-link value vector. This includes actual SU(N)
  -- link matrices, and every interacting spectator coordinate.
  originalPhysicalF19ActualSortIsOriginalR445Codec :
    ∀ {Value : Set} (original : Vec.Vec Value Single.Count) →
    Haar.permuteLinks (Sorted.actualPairProgram theory) original
    ≡ R445.originalR445CanonicalToPairResidual original
  originalPhysicalF19ActualSortIsOriginalR445Codec original =
    trans
      (Sorted.actualPairSpectatorReindexEveryOriginalVector
        theory original)
      (originalF19TargetVectorValuesAreR445 original)

  -- A *single* actual original sorted link value vector is the same
  -- input to every subsequent selected Wilson consumer. This does NOT
  -- assume the value of any particular Wilson observable, or supply
  -- a physical W1/W3 or cutoff-uniform correlation decay rate.
  originalEveryActualSortedWilsonConsumerAgrees :
    ∀ {Value Scalar : Set}
      (original : Vec.Vec Value Single.Count)
      (consumer :
        Vec.Vec Value
          (Codec.listLength R445.originalR445PairResidualBondEnumeration)
        → Scalar) →
    consumer
      (Haar.permuteLinks (Sorted.actualPairProgram theory) original)
    ≡ consumer (R445.originalR445CanonicalToPairResidual original)
  originalEveryActualSortedWilsonConsumerAgrees original consumer =
    cong consumer
      (originalPhysicalF19ActualSortIsOriginalR445Codec original)

-- This adds NO new Wilson measure or OS Hamiltonian. Physical
-- cutoff-uniform W1/W3, original E1 continuum and same H_OS remain OPEN.
