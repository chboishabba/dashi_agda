module DASHI.Crypto.TopTenSearchGeometryControlsExact where

------------------------------------------------------------------------
-- CROSS-PRIMITIVE VERIFICATION -> SEARCH CONTROLS
--
-- Every candidate gets a typed candidate-test/observation geometry.  This is a
-- comparative blue-team control surface, not an assertion that a standardized
-- implementation leaks or that any named primitive is broken.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)

import DASHI.Crypto.TopTenCryptoBlueTeamProfilesExact as Profile

-- The key comparison is what a supplied candidate can be checked against and
-- what extra observation/factorisation would be required to construct it.
data CandidateTestGeometry : Set where
  affineReuseRelation
  authenticatedPartition
  modularForwardEquation
  finiteGroupForwardEquation
  ellipticScalarForwardEquation
  randomizedReencryptionWitness
  componentLocalComposition
  noisyResidualAndReconciliation
  physicalStatisticalPartition : CandidateTestGeometry

data ExtraSearchStructure : Set where
  reuseCorrelation
  hiddenDependentOutcome
  publicInverseFactorisation
  discreteLogFactorisation
  randomnessRecoveryOrElimination
  componentBreakOrCrossBoundaryLeak
  localResidualEnumerationAndCheapReconciliation
  physicalObservationModel : ExtraSearchStructure

record SearchControl : Set where
  constructor searchControl
  field
    candidate : Profile.CryptoCandidate
    verifierGeometry : CandidateTestGeometry
    extraStructureTarget : ExtraSearchStructure

open SearchControl public

otpControl : SearchControl
otpControl = searchControl Profile.oneTimePad
  affineReuseRelation reuseCorrelation

aesControl : SearchControl
aesControl = searchControl Profile.aesGcm
  authenticatedPartition hiddenDependentOutcome

chachaControl : SearchControl
chachaControl = searchControl Profile.chacha20Poly1305
  authenticatedPartition hiddenDependentOutcome

rsaControl : SearchControl
rsaControl = searchControl Profile.rsaOaep
  modularForwardEquation publicInverseFactorisation

dhControl : SearchControl
dhControl = searchControl Profile.diffieHellman
  finiteGroupForwardEquation discreteLogFactorisation

x25519Control : SearchControl
x25519Control = searchControl Profile.x25519
  ellipticScalarForwardEquation discreteLogFactorisation

elGamalControl : SearchControl
elGamalControl = searchControl Profile.elGamal
  randomizedReencryptionWitness randomnessRecoveryOrElimination

hpkeControl : SearchControl
hpkeControl = searchControl Profile.hpke
  componentLocalComposition componentBreakOrCrossBoundaryLeak

mlKemControl : SearchControl
mlKemControl = searchControl Profile.mlKem
  noisyResidualAndReconciliation localResidualEnumerationAndCheapReconciliation

qkdControl : SearchControl
qkdControl = searchControl Profile.qkdWithSymmetric
  physicalStatisticalPartition physicalObservationModel

allSearchControls : List SearchControl
allSearchControls =
  otpControl ∷ aesControl ∷ chachaControl ∷ rsaControl ∷ dhControl ∷
  x25519Control ∷ elGamalControl ∷ hpkeControl ∷ mlKemControl ∷
  qkdControl ∷ []

allSearchControlsCount : length allSearchControls ≡ 10
allSearchControlsCount = refl

-- Timing is intentionally orthogonal to primitive mathematics: it is an
-- implementation/protocol observation coordinate that may be attached to any
-- computational candidate, but requires an actual same-public-fibre split
-- witness before being promoted to leakage.
data RuntimeObservationStatus : Set where
  runtimeNotModelled
  runtimeModelledNoSplitProved
  runtimeSplitWitnessed : RuntimeObservationStatus

record RuntimeAugmentedControl : Set where
  constructor runtimeAugmentedControl
  field
    base : SearchControl
    runtimeStatus : RuntimeObservationStatus

open RuntimeAugmentedControl public
