module DASHI.Reasoning.TernarySynthesisTransportWeldExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Ingrid Daubechies,
-- "Ten Lectures on Wavelets", SIAM, 1992.
-- DOI: 10.1137/1.9781611970104.
--
-- DASHI CONTRIBUTION
--
-- Reuse the repository's existing j-coarse/j-fine branching cobordism,
-- finite wave superposition, PNF 0/1/2-cell topology and signed spectral layer
-- as the transport side of ternary synthesis.
--
-- A branch synthesis is measured by the already-defined split/recombine
-- residual. The canonical 1->3 refinement has zero residual; the existing
-- phase-changed refinement has a nonzero exact residual. This is the concrete
-- finite transport defect needed by the synthesis-commutation discussion:
-- coherent refinement and path-dependent refinement are distinguished without
-- inventing a new wave or Hodge authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (_*_)
open import Data.Integer using (+_; -[1+_])

import DASHI.Biology.JFineCoarseRelativeScaleExact as JScale
import DASHI.Interop.PNFHodgeResidualTopology as Hodge
import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Branch
import DASHI.Reasoning.RelationalBranchInterference as Interference

record BranchSynthesisTransport : Set where
  constructor branchSynthesisTransport
  field
    junction : Branch.OneToNBranching
    coarse : Branch.BranchChannel
    coarseIsJCoarse : coarse ≡ Branch.jCoarse junction
    fine : List Branch.BranchChannel
    fineIsJFine : fine ≡ Branch.jFine junction
    synthesisWave : Interference.BranchWave
    synthesisWaveIsRecombined :
      synthesisWave ≡ Branch.recombineJ junction
    transportDefect : Interference.BranchWave
    transportDefectIsSplitRecombineResidual :
      transportDefect ≡ Branch.splitRecombineResidual junction

open BranchSynthesisTransport public

canonicalOneToThreeSynthesis :
  BranchSynthesisTransport
canonicalOneToThreeSynthesis =
  branchSynthesisTransport
    Branch.composedOneToThree
    (Branch.jCoarse Branch.composedOneToThree)
    refl
    (Branch.jFine Branch.composedOneToThree)
    refl
    (Branch.recombineJ Branch.composedOneToThree)
    refl
    (Branch.splitRecombineResidual Branch.composedOneToThree)
    refl

phaseChangedSynthesis :
  BranchSynthesisTransport
phaseChangedSynthesis =
  branchSynthesisTransport
    Branch.phaseChangedJunction
    (Branch.jCoarse Branch.phaseChangedJunction)
    refl
    (Branch.jFine Branch.phaseChangedJunction)
    refl
    (Branch.recombineJ Branch.phaseChangedJunction)
    refl
    (Branch.splitRecombineResidual Branch.phaseChangedJunction)
    refl

canonicalSynthesisDefectIsZero :
  transportDefect canonicalOneToThreeSynthesis
  ≡ Wave.mkDiscreteWave (+ 0) (+ 0)
canonicalSynthesisDefectIsZero =
  Branch.composedResidualIsZero

phaseChangedSynthesisDefectExact :
  transportDefect phaseChangedSynthesis
  ≡ Wave.mkDiscreteWave (-[1+ 0 ]) (+ 1)
phaseChangedSynthesisDefectExact =
  Branch.phaseChangedResidualExact

------------------------------------------------------------------------
-- j-coarse/j-fine scale identity already present in the harmonic lane.
------------------------------------------------------------------------

jCoarseIsNine : JScale.jCoarseFrequency ≡ 9
jCoarseIsNine = refl

jFineIsThreePowerNine : JScale.jFineFrequency ≡ 19683
jFineIsThreePowerNine = JScale.jFineIsThreePowerNine

jAbsoluteFineFactors :
  JScale.jAbsoluteFineFrequency
  ≡ JScale.jCoarseFrequency * JScale.jFineFrequency
jAbsoluteFineFactors =
  JScale.jAbsoluteFineIsCoarseTimesJFine

------------------------------------------------------------------------
-- Existing Hodge/spectral topology is the receipt surface for higher-cell
-- synthesis. Contradiction remains on the boundary; Delta0 is the implementable
-- signed graph layer and Delta1/Delta2 remain diagnostic-only.
------------------------------------------------------------------------

canonicalContradictionSynthesisCell : Hodge.PNFTwoCell
canonicalContradictionSynthesisCell =
  Hodge.canonicalContradictionTwoCell

canonicalContradictionSynthesisKind :
  Hodge.PNFTwoCell.twoCellKind canonicalContradictionSynthesisCell
  ≡ Hodge.contradictionTriangle2Cell
canonicalContradictionSynthesisKind = refl

implementableSynthesisSpectralShape :
  Hodge.PNFHodgeLaplacianShape
implementableSynthesisSpectralShape =
  Hodge.canonicalΔ0Shape

synthesisSpectralLayerIsDeltaZero :
  Hodge.PNFHodgeLaplacianShape.laplacianTag
    implementableSynthesisSpectralShape
  ≡ Hodge.Δ0
synthesisSpectralLayerIsDeltaZero = refl

record TernarySynthesisTransportBoundary : Set where
  field
    existingJCoarseFineReused : Bool
    existingJCoarseFineReusedIsTrue :
      existingJCoarseFineReused ≡ true

    existingWaveResidualReused : Bool
    existingWaveResidualReusedIsTrue :
      existingWaveResidualReused ≡ true

    existingPNFTwoCellReused : Bool
    existingPNFTwoCellReusedIsTrue :
      existingPNFTwoCellReused ≡ true

    deltaOneOrTwoPromotedToCompletedHodgeAuthority : Bool
    deltaOneOrTwoPromotedToCompletedHodgeAuthorityIsFalse :
      deltaOneOrTwoPromotedToCompletedHodgeAuthority ≡ false

    zeroTransportDefectInterpretedAsUniversalEmpiricalHealth : Bool
    zeroTransportDefectInterpretedAsUniversalEmpiricalHealthIsFalse :
      zeroTransportDefectInterpretedAsUniversalEmpiricalHealth ≡ false

canonicalTernarySynthesisTransportBoundary :
  TernarySynthesisTransportBoundary
canonicalTernarySynthesisTransportBoundary =
  record
    { existingJCoarseFineReused = true
    ; existingJCoarseFineReusedIsTrue = refl
    ; existingWaveResidualReused = true
    ; existingWaveResidualReusedIsTrue = refl
    ; existingPNFTwoCellReused = true
    ; existingPNFTwoCellReusedIsTrue = refl
    ; deltaOneOrTwoPromotedToCompletedHodgeAuthority = false
    ; deltaOneOrTwoPromotedToCompletedHodgeAuthorityIsFalse = refl
    ; zeroTransportDefectInterpretedAsUniversalEmpiricalHealth = false
    ; zeroTransportDefectInterpretedAsUniversalEmpiricalHealthIsFalse = refl
    }
