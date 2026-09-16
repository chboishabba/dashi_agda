module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFreeEnergyTextAcquisitionValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFreeEnergyTextAcquisitionExact as Owner

boundary = Owner.canonicalAdKFreeEnergyTextAcquisitionBoundary
bound = Owner.ligandBoundOpenClosedDeltaG
unbound = Owner.ligandFreeOpenClosedRange

_ : Owner.tenthsKcalMol bound ≡ 80
_ = refl

_ : Owner.lowerKT unbound ≡ 1
_ = refl

_ : Owner.upperKT unbound ≡ 2
_ = refl

_ : Owner.gammaIsReferenceMinimum Owner.ligandFreeQualitativeOrdering ≡ true
_ = refl

_ : Owner.alphaBetaGammaNearlySame Owner.ligandFreeQualitativeOrdering ≡ true
_ = refl

_ : Owner.deltaLLowerThanZetaL Owner.ligandBoundQualitativeOrdering ≡ true
_ = refl
