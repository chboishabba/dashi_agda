module DASHI.Crypto.TopTenCryptoDependencyGraphExact where

------------------------------------------------------------------------
-- TOP-TEN CRYPTO DEPENDENCY / BREAK GRAPH
--
-- The central blue-team rule is compositional: primitive correctness is not
-- security, and a composite protocol is only as strong as every obligation it
-- actually exposes.  Each candidate below gets typed security obligations and
-- exact contradiction lemmas for supplied break witnesses.
--
-- References are carried by TopTenCryptoBlueTeamProfilesExact and the specific
-- primitive modules imported below.  No standardized primitive is asserted
-- broken here.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

import DASHI.Crypto.TopTenCryptoBlueTeamProfilesExact as Profile
import DASHI.Crypto.CryptoUsageInvariantExact as Usage
import DASHI.Crypto.PublicSecretFactorisationAttackExact as Factor

------------------------------------------------------------------------
-- Shared obligations.
------------------------------------------------------------------------

data SecurityObligation : Set where
  padFreshAndSecret
  nonceUniquePerKey
  keyEntropyAdequate
  authenticationSound
  trapdoorInverseHard
  paddingValidityNotObservable
  discreteLogHard
  publicElementAcceptedOnlyIfValid
  x25519AllZeroSharedSecretHandled
  ephemeralFresh
  kemComponentSecure
  kdfComponentSecure
  aeadComponentSecure
  contextBound
  moduleLWEHard
  noPublicSecretFactorisation
  implicitRejectionNotExternallySplit
  classicalChannelAuthenticated
  quantumParameterTestSound
  followOnSymmetricSecure
  attackerModelWithinAssumedBoundary : SecurityObligation

data DependsOn : Profile.CryptoCandidate → SecurityObligation → Set where
  otpPad : DependsOn Profile.oneTimePad padFreshAndSecret

  aesNonce : DependsOn Profile.aesGcm nonceUniquePerKey
  aesEntropy : DependsOn Profile.aesGcm keyEntropyAdequate
  aesAuth : DependsOn Profile.aesGcm authenticationSound
  aesContext : DependsOn Profile.aesGcm contextBound

  chachaNonce : DependsOn Profile.chacha20Poly1305 nonceUniquePerKey
  chachaEntropy : DependsOn Profile.chacha20Poly1305 keyEntropyAdequate
  chachaAuth : DependsOn Profile.chacha20Poly1305 authenticationSound
  chachaContext : DependsOn Profile.chacha20Poly1305 contextBound

  rsaInverse : DependsOn Profile.rsaOaep trapdoorInverseHard
  rsaOracle : DependsOn Profile.rsaOaep paddingValidityNotObservable
  rsaModel : DependsOn Profile.rsaOaep attackerModelWithinAssumedBoundary

  dhDlog : DependsOn Profile.diffieHellman discreteLogHard
  dhValidate : DependsOn Profile.diffieHellman publicElementAcceptedOnlyIfValid
  dhFresh : DependsOn Profile.diffieHellman ephemeralFresh
  dhModel : DependsOn Profile.diffieHellman attackerModelWithinAssumedBoundary

  xDlog : DependsOn Profile.x25519 discreteLogHard
  xAllZero : DependsOn Profile.x25519 x25519AllZeroSharedSecretHandled
  xFresh : DependsOn Profile.x25519 ephemeralFresh
  xContext : DependsOn Profile.x25519 contextBound
  xModel : DependsOn Profile.x25519 attackerModelWithinAssumedBoundary

  elgDlog : DependsOn Profile.elGamal discreteLogHard
  elgFresh : DependsOn Profile.elGamal ephemeralFresh
  elgValidate : DependsOn Profile.elGamal publicElementAcceptedOnlyIfValid
  elgModel : DependsOn Profile.elGamal attackerModelWithinAssumedBoundary

  hpkeKem : DependsOn Profile.hpke kemComponentSecure
  hpkeKdf : DependsOn Profile.hpke kdfComponentSecure
  hpkeAead : DependsOn Profile.hpke aeadComponentSecure
  hpkeContext : DependsOn Profile.hpke contextBound

  mlkemLwe : DependsOn Profile.mlKem moduleLWEHard
  mlkemNoFactor : DependsOn Profile.mlKem noPublicSecretFactorisation
  mlkemReject : DependsOn Profile.mlKem implicitRejectionNotExternallySplit
  mlkemModel : DependsOn Profile.mlKem attackerModelWithinAssumedBoundary

  qkdAuth : DependsOn Profile.qkdWithSymmetric classicalChannelAuthenticated
  qkdTest : DependsOn Profile.qkdWithSymmetric quantumParameterTestSound
  qkdSymmetric : DependsOn Profile.qkdWithSymmetric followOnSymmetricSecure
  qkdContext : DependsOn Profile.qkdWithSymmetric contextBound

------------------------------------------------------------------------
-- A complete obligation is proof-bearing.  A supplied refutation of the same
-- obligation contradicts completion immediately.
------------------------------------------------------------------------

record ObligationHolds (obligation : SecurityObligation) : Set₁ where
  constructor obligationHolds
  field
    Evidence : Set
    evidence : Evidence

open ObligationHolds public

ObligationBreak : SecurityObligation → Set₁
ObligationBreak obligation = ObligationHolds obligation → ⊥

breakContradictsHeld :
  ∀ {obligation} →
  ObligationBreak obligation →
  ObligationHolds obligation → ⊥
breakContradictsHeld break held = break held

------------------------------------------------------------------------
-- HPKE: KEM + KDF + AEAD + context binding.  This mirrors RFC 9180's typed
-- composition rather than treating HPKE as one opaque encryption primitive.
------------------------------------------------------------------------

record HPKESecurityContract : Set₁ where
  constructor hpkeSecurityContract
  field
    hpkeKemEvidence : ObligationHolds kemComponentSecure
    hpkeKdfEvidence : ObligationHolds kdfComponentSecure
    hpkeAeadEvidence : ObligationHolds aeadComponentSecure
    hpkeContextEvidence : ObligationHolds contextBound

open HPKESecurityContract public

kemBreakRefutesHPKE :
  ObligationBreak kemComponentSecure →
  HPKESecurityContract → ⊥
kemBreakRefutesHPKE break contract = break (hpkeKemEvidence contract)

kdfBreakRefutesHPKE :
  ObligationBreak kdfComponentSecure →
  HPKESecurityContract → ⊥
kdfBreakRefutesHPKE break contract = break (hpkeKdfEvidence contract)

aeadBreakRefutesHPKE :
  ObligationBreak aeadComponentSecure →
  HPKESecurityContract → ⊥
aeadBreakRefutesHPKE break contract = break (hpkeAeadEvidence contract)

contextBreakRefutesHPKE :
  ObligationBreak contextBound →
  HPKESecurityContract → ⊥
contextBreakRefutesHPKE break contract = break (hpkeContextEvidence contract)

------------------------------------------------------------------------
-- QKD + symmetric follow-on: authenticated classical channel, parameter test,
-- and later symmetric protection are independent obligations.
------------------------------------------------------------------------

record QKDCompositeSecurityContract : Set₁ where
  constructor qkdCompositeSecurityContract
  field
    qkdAuthenticatedChannel : ObligationHolds classicalChannelAuthenticated
    qkdParameterTest : ObligationHolds quantumParameterTestSound
    qkdFollowOnCipher : ObligationHolds followOnSymmetricSecure
    qkdContextEvidence : ObligationHolds contextBound

open QKDCompositeSecurityContract public

unauthenticatedBreakRefutesQKDComposite :
  ObligationBreak classicalChannelAuthenticated →
  QKDCompositeSecurityContract → ⊥
unauthenticatedBreakRefutesQKDComposite break contract =
  break (qkdAuthenticatedChannel contract)

parameterTestBreakRefutesQKDComposite :
  ObligationBreak quantumParameterTestSound →
  QKDCompositeSecurityContract → ⊥
parameterTestBreakRefutesQKDComposite break contract =
  break (qkdParameterTest contract)

followOnBreakRefutesQKDComposite :
  ObligationBreak followOnSymmetricSecure →
  QKDCompositeSecurityContract → ⊥
followOnBreakRefutesQKDComposite break contract =
  break (qkdFollowOnCipher contract)

------------------------------------------------------------------------
-- Algebraic/public-key family boundary.  A public-secret factorisation is
-- stronger than merely naming a hardness assumption: it is an exact break
-- witness for the protected secret-label map.
------------------------------------------------------------------------

publicSecretFactorisationCutsAsymmetry :
  ∀ {system : Factor.SecretLabelledProjection} →
  Factor.PublicSecretFactorisation system →
  (Factor.ExactPublicSecretRecovery system → ⊥) →
  ⊥
publicSecretFactorisationCutsAsymmetry factorisation noRecovery =
  noRecovery (Factor.factorisationImpliesExactRecovery factorisation)

------------------------------------------------------------------------
-- Usage-token uniqueness is reusable across OTP/AEAD/ephemeral families.
------------------------------------------------------------------------

uniqueUseViolationIsContradiction :
  ∀ {unique : Usage.TwoUseUniqueToken} →
  Usage.TwoUseReuseWitness unique → ⊥
uniqueUseViolationIsContradiction = Usage.reuseContradictsUniqueness
