module DASHI.Crypto.TopTenCryptoObservationSurfacesExact where

------------------------------------------------------------------------
-- OBSERVATION SURFACES FOR THE TEN-CANDIDATE BLUE-TEAM MATRIX
--
-- The same primitive can be secure under a smaller observation surface and
-- insecure once a secret-dependent protocol outcome is exposed.  This file
-- makes that modelling boundary explicit for all ten educational candidates.
-- It names places to look for split witnesses; it does not assert that a
-- standardized implementation exposes them.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)

import DASHI.Crypto.TopTenCryptoBlueTeamProfilesExact as Profile

-- publicOnly: mathematically factors through already-public state;
-- hiddenDependent: would refine a secret fibre if a split witness exists;
-- physicalChannel: observation belongs to a physical channel model rather than
-- a classical ciphertext/key state alone.
data ObservationDependency : Set where
  publicOnly hiddenDependent physicalChannel : ObservationDependency

data ObservationKind : Set where
  ciphertextTranscript
  authenticationAcceptReject
  paddingValidityOutcome
  sessionKeyConfirmation
  publicElementAcceptance
  hpkeOpenOutcome
  implicitRejectionDownstreamOutcome
  qkdParameterStatistics
  qkdClassicalAuthenticationOutcome : ObservationKind

record ObservationSurface : Set where
  constructor observationSurface
  field
    candidate : Profile.CryptoCandidate
    kind : ObservationKind
    dependency : ObservationDependency
    splitMustBeProvedNotAssumed : Bool
    splitMustBeProvedNotAssumedIsTrue : splitMustBeProvedNotAssumed ≡ true

open ObservationSurface public

otpPassive : ObservationSurface
otpPassive = observationSurface Profile.oneTimePad ciphertextTranscript publicOnly true refl

aesPassive : ObservationSurface
aesPassive = observationSurface Profile.aesGcm ciphertextTranscript publicOnly true refl

aesAuthOutcome : ObservationSurface
aesAuthOutcome = observationSurface Profile.aesGcm authenticationAcceptReject hiddenDependent true refl

chachaPassive : ObservationSurface
chachaPassive = observationSurface Profile.chacha20Poly1305 ciphertextTranscript publicOnly true refl

chachaAuthOutcome : ObservationSurface
chachaAuthOutcome = observationSurface Profile.chacha20Poly1305 authenticationAcceptReject hiddenDependent true refl

rsaPassive : ObservationSurface
rsaPassive = observationSurface Profile.rsaOaep ciphertextTranscript publicOnly true refl

rsaValidityOutcome : ObservationSurface
rsaValidityOutcome = observationSurface Profile.rsaOaep paddingValidityOutcome hiddenDependent true refl

dhPublic : ObservationSurface
dhPublic = observationSurface Profile.diffieHellman ciphertextTranscript publicOnly true refl

dhElementAcceptance : ObservationSurface
dhElementAcceptance = observationSurface Profile.diffieHellman publicElementAcceptance hiddenDependent true refl

x25519Public : ObservationSurface
x25519Public = observationSurface Profile.x25519 ciphertextTranscript publicOnly true refl

x25519Confirmation : ObservationSurface
x25519Confirmation = observationSurface Profile.x25519 sessionKeyConfirmation hiddenDependent true refl

elGamalPassive : ObservationSurface
elGamalPassive = observationSurface Profile.elGamal ciphertextTranscript publicOnly true refl

hpkePassive : ObservationSurface
hpkePassive = observationSurface Profile.hpke ciphertextTranscript publicOnly true refl

hpkeOpen : ObservationSurface
hpkeOpen = observationSurface Profile.hpke hpkeOpenOutcome hiddenDependent true refl

mlKemPassive : ObservationSurface
mlKemPassive = observationSurface Profile.mlKem ciphertextTranscript publicOnly true refl

mlKemDownstream : ObservationSurface
mlKemDownstream = observationSurface Profile.mlKem implicitRejectionDownstreamOutcome hiddenDependent true refl

qkdStatistics : ObservationSurface
qkdStatistics = observationSurface Profile.qkdWithSymmetric qkdParameterStatistics physicalChannel true refl

qkdAuthOutcome : ObservationSurface
qkdAuthOutcome = observationSurface Profile.qkdWithSymmetric qkdClassicalAuthenticationOutcome hiddenDependent true refl

-- At least one explicit blue-team observation surface is assigned to every
-- candidate.  The ten-element coverage list is separate from extra active
-- surfaces above.
coverage : List ObservationSurface
coverage =
  otpPassive ∷ aesPassive ∷ chachaPassive ∷ rsaPassive ∷ dhPublic ∷
  x25519Public ∷ elGamalPassive ∷ hpkePassive ∷ mlKemPassive ∷
  qkdStatistics ∷ []

coverageCount : length coverage ≡ 10
coverageCount = refl
