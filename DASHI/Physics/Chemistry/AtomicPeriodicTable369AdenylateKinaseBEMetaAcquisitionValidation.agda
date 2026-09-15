module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseBEMetaAcquisitionValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseBEMetaAcquisitionExact as Owner

boundary = Owner.canonicalAdKBEMetaAcquisitionBoundary
protocol = Owner.canonicalBEMetaProtocol

_ : Owner.thetaOneLowerDegrees protocol ≡ 58
_ = refl

_ : Owner.thetaOneUpperDegrees protocol ≡ 100
_ = refl

_ : Owner.thetaTwoLowerDegrees protocol ≡ 20
_ = refl

_ : Owner.thetaTwoUpperDegrees protocol ≡ 70
_ = refl

_ : Owner.dLnLowerAngstrom protocol ≡ 15
_ = refl

_ : Owner.dLnUpperAngstrom protocol ≡ 45
_ = refl

_ : Owner.gaussianHeightHundredthsKcalMol protocol ≡ 5
_ = refl

_ : Owner.angularGaussianWidthHundredthsRadian protocol ≡ 1
_ = refl

_ : Owner.dLnGaussianWidthTenthsAngstrom protocol ≡ 1
_ = refl

_ : Owner.gaussianDepositionPicoseconds protocol ≡ 1
_ = refl

_ : Owner.swapAttemptPicoseconds protocol ≡ 2
_ = refl

_ : Owner.nanosecondsPerReplica protocol ≡ 200
_ = refl

_ : Owner.totalNanosecondsPerBEMeta protocol ≡ 800
_ = refl
