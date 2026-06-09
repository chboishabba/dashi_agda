module DASHI.Physics.Closure.Gate2ActualSelectedCarrierBundle where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ColimitGapLiftOnHamiltonian as Colimit
import DASHI.Physics.Closure.FiniteCoercivityOnSelectedCarrier as FiniteCarrier
import DASHI.Physics.Closure.GapRefinementOnActualTower as Tower
import DASHI.Physics.Closure.Gate2SpectralGapMath as Gate2
import DASHI.Physics.Closure.SelfAdjointYangMillsHamiltonianOnCarrierQuotient as SelfAdjoint
import DASHI.Physics.Closure.UniformLowerBoundOnTower as Uniform
import DASHI.Physics.Boundaries.GribovResolutionAuthorityReceipt as Gribov
import DASHI.Physics.Boundaries.TopologicalMassGapInterpretation as Topological
import DASHI.Physics.Boundaries.YMConstructive5DProofReceipt as YM5D

------------------------------------------------------------------------
-- Actual selected-carrier Gate 2 bundle.

canonicalGate2Receipt :
  Gate2.Gate2SpectralGapMathReceipt
canonicalGate2Receipt =
  Gate2.canonicalGate2SpectralGapMathReceipt

record Gate2ActualSelectedCarrierBundleReceipt : Setω where
  field
    finiteCoercivityOnSelectedCarrier :
      FiniteCarrier.FiniteCoercivityOnSelectedCarrierReceipt

    gapRefinementOnActualTower :
      Tower.GapRefinementOnActualTowerReceipt

    uniformLowerBoundOnTower :
      Uniform.UniformLowerBoundOnTowerReceipt

    selfAdjointColimitWrapper :
      SelfAdjoint.Gate2ColimitGapLiftReceipt

    colimitGapLiftOnHamiltonian :
      Colimit.ColimitGapLiftOnHamiltonianReceipt

    ymConstructive5DExternalCandidate :
      YM5D.YMConstructive5DProofReceipt

    gribovResolutionExternalCandidate :
      Gribov.GribovResolutionAuthorityReceipt

    topologicalMassGapExternalCandidate :
      Topological.TopologicalMassGapInterpretationReceipt

    externalCandidateEvidencePromoted :
      Bool

    externalCandidateEvidencePromotedIsFalse :
      externalCandidateEvidencePromoted ≡ false

    selectedCarrierGate2Promoted :
      Bool

    selectedCarrierGate2PromotedIsFalse :
      selectedCarrierGate2Promoted ≡ false

    actualGate2Boundary :
      List String

open Gate2ActualSelectedCarrierBundleReceipt public

canonicalGate2ActualSelectedCarrierBundleReceipt :
  Gate2ActualSelectedCarrierBundleReceipt
canonicalGate2ActualSelectedCarrierBundleReceipt =
  record
    { finiteCoercivityOnSelectedCarrier =
        FiniteCarrier.canonicalFiniteCoercivityOnSelectedCarrierReceipt
    ; gapRefinementOnActualTower =
        Tower.canonicalGapRefinementOnActualTowerReceipt
    ; uniformLowerBoundOnTower =
        Uniform.canonicalUniformLowerBoundOnTowerReceipt
    ; selfAdjointColimitWrapper =
        SelfAdjoint.canonicalGate2ColimitGapLiftReceipt
    ; colimitGapLiftOnHamiltonian =
        Colimit.canonicalColimitGapLiftOnHamiltonianReceipt
    ; ymConstructive5DExternalCandidate =
        YM5D.canonicalYMConstructive5DProofReceipt
    ; gribovResolutionExternalCandidate =
        Gribov.canonicalGribovResolutionAuthorityReceipt
    ; topologicalMassGapExternalCandidate =
        Topological.canonicalTopologicalMassGapInterpretationReceipt
    ; externalCandidateEvidencePromoted =
        false
    ; externalCandidateEvidencePromotedIsFalse =
        refl
    ; selectedCarrierGate2Promoted =
        false
    ; selectedCarrierGate2PromotedIsFalse =
        refl
    ; actualGate2Boundary =
        "Gate 2 now consumes the concrete selected-carrier receipt chain"
        ∷ "The canonical Bool-model Gate 2 package is retained as the core reference receipt"
        ∷ "Finite coercivity, tower refinement, uniform lower bound, self-adjoint wrapper, and Hamiltonian colimit lift are threaded explicitly"
        ∷ "External YM candidate receipts are recorded as authority evidence only and all carry false promotion flags"
        ∷ "No real-carrier analytic theorem is promoted here"
        ∷ []
    }
