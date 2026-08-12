module DASHI.Crypto.TopTenCryptoStateContractMatrixExact where

------------------------------------------------------------------------
-- PRECONDITION / POSTCONDITION / INVARIANT MATRIX FOR THE TEN CANDIDATES
--
-- This is a typed blue-team checklist surface, not a proof that the named
-- standardized primitives satisfy every security assumption.  Structural
-- obligations are separated so a failed precondition is not confused with a
-- cryptanalytic break and primitive correctness is not confused with protocol
-- security.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)

import DASHI.Crypto.TopTenCryptoBlueTeamProfilesExact as Profile

------------------------------------------------------------------------
-- State-contract vocabulary.
------------------------------------------------------------------------

data Precondition : Set where
  padUniformSecretAndOneUse
  nonceUniqueForKey
  keyGeneratedWithAdequateEntropy
  rsaKeyWellFormed
  oaepRandomnessFresh
  groupParametersAccepted
  peerElementAccepted
  ephemeralExponentFresh
  x25519InputHandledPerRFC7748
  elGamalRandomnessFresh
  hpkeSuiteAndModeBound
  mlKemEncodedKeyAccepted
  mlKemEncapsulationCoinsFresh
  qkdClassicalChannelAuthenticated
  qkdDevicesAndParametersWithinModel : Precondition

data Postcondition : Set where
  plaintextRecovered
  plaintextAuthenticatedOrRejected
  sharedSecretAgrees
  kemSharedSecretProduced
  qkdKeyAcceptedOrProtocolAborts : Postcondition

data Invariant : Set where
  padNeverReused
  nonceNeverRepeatedUnderSameKey
  authenticationFailureNotPlaintext
  publicOperationDoesNotExposeProtectedInverse
  secretAgreementNotPubliclyDerived
  publicElementValidationPreserved
  x25519AllZeroSharedSecretHandled
  ephemeralStateNotReused
  hpkeComponentBoundariesPreserved
  contextBindingPreserved
  mlKemImplicitRejectionNotSplitExternally
  mlKemProtectedLabelNotPubliclyFactored
  qkdAuthenticationBindingPreserved
  qkdAcceptedKeyFeedsApprovedSymmetricProtection : Invariant

record CandidateStateContract : Set where
  constructor candidateStateContract
  field
    candidate : Profile.CryptoCandidate
    preconditions : List Precondition
    postconditions : List Postcondition
    invariants : List Invariant

open CandidateStateContract public

otpContract : CandidateStateContract
otpContract = candidateStateContract Profile.oneTimePad
  (padUniformSecretAndOneUse ∷ [])
  (plaintextRecovered ∷ [])
  (padNeverReused ∷ [])

aesGcmContract : CandidateStateContract
aesGcmContract = candidateStateContract Profile.aesGcm
  (nonceUniqueForKey ∷ keyGeneratedWithAdequateEntropy ∷ [])
  (plaintextAuthenticatedOrRejected ∷ [])
  (nonceNeverRepeatedUnderSameKey ∷ authenticationFailureNotPlaintext ∷
   contextBindingPreserved ∷ [])

chachaContract : CandidateStateContract
chachaContract = candidateStateContract Profile.chacha20Poly1305
  (nonceUniqueForKey ∷ keyGeneratedWithAdequateEntropy ∷ [])
  (plaintextAuthenticatedOrRejected ∷ [])
  (nonceNeverRepeatedUnderSameKey ∷ authenticationFailureNotPlaintext ∷
   contextBindingPreserved ∷ [])

rsaContract : CandidateStateContract
rsaContract = candidateStateContract Profile.rsaOaep
  (rsaKeyWellFormed ∷ oaepRandomnessFresh ∷ [])
  (plaintextRecovered ∷ [])
  (publicOperationDoesNotExposeProtectedInverse ∷
   authenticationFailureNotPlaintext ∷ [])

dhContract : CandidateStateContract
dhContract = candidateStateContract Profile.diffieHellman
  (groupParametersAccepted ∷ peerElementAccepted ∷ ephemeralExponentFresh ∷ [])
  (sharedSecretAgrees ∷ [])
  (secretAgreementNotPubliclyDerived ∷ publicElementValidationPreserved ∷
   ephemeralStateNotReused ∷ [])

x25519Contract : CandidateStateContract
x25519Contract = candidateStateContract Profile.x25519
  (x25519InputHandledPerRFC7748 ∷ ephemeralExponentFresh ∷ [])
  (sharedSecretAgrees ∷ [])
  (secretAgreementNotPubliclyDerived ∷ x25519AllZeroSharedSecretHandled ∷
   contextBindingPreserved ∷ ephemeralStateNotReused ∷ [])

elGamalContract : CandidateStateContract
elGamalContract = candidateStateContract Profile.elGamal
  (groupParametersAccepted ∷ peerElementAccepted ∷ elGamalRandomnessFresh ∷ [])
  (plaintextRecovered ∷ [])
  (publicOperationDoesNotExposeProtectedInverse ∷
   ephemeralStateNotReused ∷ publicElementValidationPreserved ∷ [])

hpkeContract : CandidateStateContract
hpkeContract = candidateStateContract Profile.hpke
  (hpkeSuiteAndModeBound ∷ keyGeneratedWithAdequateEntropy ∷ [])
  (plaintextAuthenticatedOrRejected ∷ [])
  (hpkeComponentBoundariesPreserved ∷ contextBindingPreserved ∷
   authenticationFailureNotPlaintext ∷ [])

mlKemContract : CandidateStateContract
mlKemContract = candidateStateContract Profile.mlKem
  (mlKemEncodedKeyAccepted ∷ mlKemEncapsulationCoinsFresh ∷ [])
  (kemSharedSecretProduced ∷ [])
  (mlKemImplicitRejectionNotSplitExternally ∷
   mlKemProtectedLabelNotPubliclyFactored ∷ [])

qkdContract : CandidateStateContract
qkdContract = candidateStateContract Profile.qkdWithSymmetric
  (qkdClassicalChannelAuthenticated ∷ qkdDevicesAndParametersWithinModel ∷ [])
  (qkdKeyAcceptedOrProtocolAborts ∷ [])
  (qkdAuthenticationBindingPreserved ∷
   qkdAcceptedKeyFeedsApprovedSymmetricProtection ∷ [])

allContracts : List CandidateStateContract
allContracts =
  otpContract ∷ aesGcmContract ∷ chachaContract ∷ rsaContract ∷
  dhContract ∷ x25519Contract ∷ elGamalContract ∷ hpkeContract ∷
  mlKemContract ∷ qkdContract ∷ []

allContractsCount : length allContracts ≡ 10
allContractsCount = refl
