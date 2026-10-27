{-# OPTIONS --safe #-}
module DASHI.Unified.SingularBasinCoarseRGTOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.SingularBasinCoarseRGTOEExact as Owner
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier

toeFiniteReductionMatchesOwner :
  TOE.toeSingularBasinFiniteReduction
  ≡ Owner.finiteReduction
toeFiniteReductionMatchesOwner = refl

unifierFiniteReductionMatchesOwner :
  Unifier.unifierSingularBasinFiniteReduction
  ≡ Owner.finiteReduction
unifierFiniteReductionMatchesOwner = refl

toeFiniteReductionStillNotBasinPreserving :
  ¬ Owner.Reduction.BasinPreserving Owner.finiteReduction
toeFiniteReductionStillNotBasinPreserving =
  TOE.toeSingularBasinFiniteReductionNotBasinPreserving

unifierFiniteReductionStillNotBasinPreserving :
  ¬ Owner.Reduction.BasinPreserving Owner.finiteReduction
unifierFiniteReductionStillNotBasinPreserving =
  Unifier.unifierSingularBasinFiniteReductionNotBasinPreserving

toeFiniteBasinStillDoesNotFactor :
  ¬ Owner.Reduction.PredicateFactorisation
      Owner.Finite.project
      Owner.Finite.FullInBasin
toeFiniteBasinStillDoesNotFactor =
  TOE.toeSingularBasinFiniteFullBasinDoesNotFactor

unifierFiniteBasinStillDoesNotFactor :
  ¬ Owner.Reduction.PredicateFactorisation
      Owner.Finite.project
      Owner.Finite.FullInBasin
unifierFiniteBasinStillDoesNotFactor =
  Unifier.unifierSingularBasinFiniteFullBasinDoesNotFactor

toeSelectedResolutionStillNotRobust :
  ¬ Owner.Resolution.RobustAt
      Owner.ResolutionWitness.finiteResolutionGeometry
      Owner.Finite.FullInBasin
      Owner.ResolutionWitness.selectedResolution
      Owner.Finite.funnelState
toeSelectedResolutionStillNotRobust =
  TOE.toeSingularBasinSelectedResolutionNotRobust

unifierSelectedResolutionStillNotRobust :
  ¬ Owner.Resolution.RobustAt
      Owner.ResolutionWitness.finiteResolutionGeometry
      Owner.Finite.FullInBasin
      Owner.ResolutionWitness.selectedResolution
      Owner.Finite.funnelState
unifierSelectedResolutionStillNotRobust =
  Unifier.unifierSingularBasinSelectedResolutionNotRobust

toeStableManifoldTubeStillOpen :
  Owner.Yanchuk.intervalStableManifoldTubeCertified
    Owner.yanchukStableManifoldValidationBoundary
  ≡ false
toeStableManifoldTubeStillOpen =
  TOE.toeYanchukIntervalStableManifoldTubeStillMissing

unifierStableManifoldTubeStillOpen :
  Owner.Yanchuk.intervalStableManifoldTubeCertified
    Owner.yanchukStableManifoldValidationBoundary
  ≡ false
unifierStableManifoldTubeStillOpen =
  Unifier.unifierYanchukIntervalStableManifoldTubeStillMissing

toeBasinSeparationStillOpen :
  Owner.Yanchuk.basinSeparationTheoremCertified
    Owner.yanchukStableManifoldValidationBoundary
  ≡ false
toeBasinSeparationStillOpen =
  TOE.toeYanchukBasinSeparationTheoremStillMissing

unifierBasinSeparationStillOpen :
  Owner.Yanchuk.basinSeparationTheoremCertified
    Owner.yanchukStableManifoldValidationBoundary
  ≡ false
unifierBasinSeparationStillOpen =
  Unifier.unifierYanchukBasinSeparationTheoremStillMissing

toeZKPFrameMatchesOwner :
  TOE.toeSingularBasinZKPFrame
  ≡ Owner.canonicalSingularBasinTOEZKPFrame
toeZKPFrameMatchesOwner = refl

unifierZKPFrameMatchesOwner :
  Unifier.unifierSingularBasinZKPFrame
  ≡ Owner.canonicalSingularBasinTOEZKPFrame
unifierZKPFrameMatchesOwner = refl
