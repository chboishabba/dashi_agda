module DASHI.Crypto.TopTenSearchGeometryControlsExact where

------------------------------------------------------------------------
-- CROSS-PRIMITIVE VERIFICATION -> SEARCH CONTROLS
--
-- Every candidate gets a typed candidate-test/observation geometry. This is a
-- comparative blue-team control surface, not an assertion that a standardized
-- implementation leaks or that any named primitive is broken.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)

import DASHI.Crypto.TopTenCryptoBlueTeamProfilesExact as Profile

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
otpControl = searchControl Profile.oneTimePad affineReuseRelation reuseCorrelation

aesControl : SearchControl
aesControl = searchControl Profile.aesGcm authenticatedPartition hiddenDependentOutcome

chachaControl : SearchControl
chachaControl = searchControl Profile.chacha20Poly1305 authenticatedPartition hiddenDependentOutcome

rsaControl : SearchControl
rsaControl = searchControl Profile.rsaOaep modularForwardEquation publicInverseFactorisation

dhControl : SearchControl
dhControl = searchControl Profile.diffieHellman finiteGroupForwardEquation discreteLogFactorisation

x25519Control : SearchControl
x25519Control = searchControl Profile.x25519 ellipticScalarForwardEquation discreteLogFactorisation

elGamalControl : SearchControl
elGamalControl = searchControl Profile.elGamal randomizedReencryptionWitness randomnessRecoveryOrElimination

hpkeControl : SearchControl
hpkeControl = searchControl Profile.hpke componentLocalComposition componentBreakOrCrossBoundaryLeak

mlKemControl : SearchControl
mlKemControl = searchControl Profile.mlKem noisyResidualAndReconciliation localResidualEnumerationAndCheapReconciliation

qkdControl : SearchControl
qkdControl = searchControl Profile.qkdWithSymmetric physicalStatisticalPartition physicalObservationModel

allSearchControls : List SearchControl
allSearchControls =
  otpControl ∷ aesControl ∷ chachaControl ∷ rsaControl ∷ dhControl ∷
  x25519Control ∷ elGamalControl ∷ hpkeControl ∷ mlKemControl ∷ qkdControl ∷ []

allSearchControlsCount : length allSearchControls ≡ 10
allSearchControlsCount = refl

------------------------------------------------------------------------
-- Timing is orthogonal to primitive mathematics. It can be attached to any of
-- the ten candidates, but no candidate is promoted to a timing leak without a
-- same-public-fibre TimingSplit or a protected-outcome timing factorisation.
------------------------------------------------------------------------

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

runtimeControl : SearchControl → RuntimeAugmentedControl
runtimeControl control = runtimeAugmentedControl control runtimeModelledNoSplitProved

allRuntimeAugmentedControls : List RuntimeAugmentedControl
allRuntimeAugmentedControls =
  runtimeControl otpControl ∷
  runtimeControl aesControl ∷
  runtimeControl chachaControl ∷
  runtimeControl rsaControl ∷
  runtimeControl dhControl ∷
  runtimeControl x25519Control ∷
  runtimeControl elGamalControl ∷
  runtimeControl hpkeControl ∷
  runtimeControl mlKemControl ∷
  runtimeControl qkdControl ∷ []

allRuntimeAugmentedControlsCount : length allRuntimeAugmentedControls ≡ 10
allRuntimeAugmentedControlsCount = refl
