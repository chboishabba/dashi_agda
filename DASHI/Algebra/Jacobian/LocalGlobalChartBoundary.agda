module DASHI.Algebra.Jacobian.LocalGlobalChartBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.Jacobian.InvertibilityStrata as Strata
import DASHI.Algebra.Jacobian.FibreBranching as Fibre

------------------------------------------------------------------------
-- A nonsingular local differential type can coexist with multiple global
-- sheets.  Global analysis must therefore track fibres and behaviour at
-- infinity in addition to neighbourhood data.

record GlobalFibreTopologyBoundary : Set where
  constructor globalFibreTopologyBoundary
  field
    localDifferentialTypeNonsingular : Bool
    localChartsValid : Bool
    globalInjectivityFollows : Bool
    fibreCardinalityMustBeTracked : Bool
    branchPermutationMustBeTracked : Bool
    behaviourAtInfinityMustBeTracked : Bool
    propernessMustBeTracked : Bool

open GlobalFibreTopologyBoundary public

canonicalGlobalFibreTopologyBoundary : GlobalFibreTopologyBoundary
canonicalGlobalFibreTopologyBoundary =
  globalFibreTopologyBoundary
    true
    true
    false
    true
    true
    true
    true

canonicalLocalValidityDoesNotGiveGlobalInjectivity :
  globalInjectivityFollows canonicalGlobalFibreTopologyBoundary ≡ false
canonicalLocalValidityDoesNotGiveGlobalInjectivity = refl

record InverseAuditBoundary : Set where
  constructor inverseAuditBoundary
  field
    everyInverseUseClassified : Bool
    globalInverseRequiresGlobalProof : Bool
    localRoundTripSufficesForGlobalInverse : Bool
    branchSelectedInverseRequiresReceipt : Bool
    fibreEnumerationIsReconstructionResult : Bool

open InverseAuditBoundary public

canonicalInverseAuditBoundary : InverseAuditBoundary
canonicalInverseAuditBoundary =
  inverseAuditBoundary true true false true true

canonicalLocalRoundTripNotEnough :
  localRoundTripSufficesForGlobalInverse canonicalInverseAuditBoundary ≡ false
canonicalLocalRoundTripNotEnough = refl
