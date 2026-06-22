module DASHI.Crypto.RSAPlusOneIdentitySection where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _-_)
open import Agda.Builtin.String using (String)

open import Data.Nat.Base using (NonZero; nonZero)
open import Data.Nat.DivMod using (_%_)

import DASHI.Crypto.RSAArithmeticCore as RSAA
import DASHI.Crypto.RSACRTChamberCore as RSACRT
import DASHI.Crypto.RSAVulnerabilityBoundary as RSAB
import DASHI.Algebra.MoonshineBridge as MB
import CRTPeriod as CRT
import JFixedPoint as J

------------------------------------------------------------------------
-- Thin RSA +1 identity-section adapter.
--
-- The arithmetic payload stays local only for the actual N + 1 witness.
-- Everything else is indexed through the existing RSA arithmetic / CRT /
-- vulnerability modules, and the Moonshine lane is attached by reference
-- to the existing 196883 -> 196884 bridge.

rsaWitnessEcologyHidden : String
rsaWitnessEcologyHidden = "p-1, q-1, phi(N), lambda(N)"

rsaWitnessEcologyHiddenLabel : String
rsaWitnessEcologyHiddenLabel = "hidden witness ecology"

rsaPlusOneNoFactorOracle : Bool
rsaPlusOneNoFactorOracle = false

instance
  rsaNonZero47 : NonZero 47
  rsaNonZero47 = nonZero

  rsaNonZero59 : NonZero 59
  rsaNonZero59 = nonZero

------------------------------------------------------------------------
-- Local RSA witness arithmetic.

rsaPrimeP : Nat
rsaPrimeP = 47

rsaPrimeQ : Nat
rsaPrimeQ = 59

rsaPublicModulus : Nat
rsaPublicModulus = rsaPrimeP * rsaPrimeQ

rsaPublicModulusPlusOne : Nat
rsaPublicModulusPlusOne = rsaPublicModulus + 1

rsaPrimePMinusOne : Nat
rsaPrimePMinusOne = rsaPrimeP - 1

rsaPrimeQMinusOne : Nat
rsaPrimeQMinusOne = rsaPrimeQ - 1

rsaPhi : Nat
rsaPhi = rsaPrimePMinusOne * rsaPrimeQMinusOne

rsaLambda : Nat
rsaLambda = 1334

rsaPublicModulusIsProduct : rsaPublicModulus ≡ 2773
rsaPublicModulusIsProduct = refl

rsaPublicModulusPlusOneIsProductPlusOne :
  rsaPublicModulusPlusOne ≡ 2774
rsaPublicModulusPlusOneIsProductPlusOne = refl

rsaZeroSectionP : rsaPublicModulus % rsaPrimeP ≡ 0
rsaZeroSectionP = refl

rsaZeroSectionQ : rsaPublicModulus % rsaPrimeQ ≡ 0
rsaZeroSectionQ = refl

rsaIdentitySectionP : rsaPublicModulusPlusOne % rsaPrimeP ≡ 1
rsaIdentitySectionP = refl

rsaIdentitySectionQ : rsaPublicModulusPlusOne % rsaPrimeQ ≡ 1
rsaIdentitySectionQ = refl

rsaPrimeWitnessRuleP : rsaPrimePMinusOne + 1 ≡ rsaPrimeP
rsaPrimeWitnessRuleP = refl

rsaPrimeWitnessRuleQ : rsaPrimeQMinusOne + 1 ≡ rsaPrimeQ
rsaPrimeWitnessRuleQ = refl

rsaPhiFormula : rsaPhi ≡ 2668
rsaPhiFormula = refl

rsaPrimeSumBridge : rsaPrimeP + rsaPrimeQ ≡ rsaPublicModulus - rsaPhi + 1
rsaPrimeSumBridge = refl

------------------------------------------------------------------------
-- RSA +1 identity-section adapter.

record RSAPlusOneIdentitySectionRow
  (pAxis qAxis : Nat)
  .{{_ : NonZero pAxis}}
  .{{_ : NonZero qAxis}}
  : Set₁ where
  constructor mkRSAPlusOneIdentitySectionRow
  field
    rsaArithmeticCoreReference :
      RSAA.RSAArithmeticCoreSurface

    rsaCRTChamberReference :
      RSACRT.RSACRTChamberCore

    rsaVulnerabilityBoundaryReference :
      RSAB.RSAVulnerabilityBoundary

    publicBodyLabel :
      String

    hiddenPrimeAxisLabel :
      String

    hiddenWitnessEcologyLabel :
      String

    zeroSectionLabel :
      String

    identitySectionLabel :
      String

    publicLimitationLabel :
      String

    noBreakWitnessLabel :
      String

    publicModulusField :
      Nat

    publicModulusPlusOneField :
      Nat

    primePField :
      Nat

    primeQField :
      Nat

    primePMinusOneField :
      Nat

    primeQMinusOneField :
      Nat

    phiField :
      Nat

    lambdaField :
      Nat

    publicModulusFieldIsProduct :
      publicModulusField ≡ pAxis * qAxis

    publicModulusPlusOneFieldIsPlusOne :
      publicModulusPlusOneField ≡ publicModulusField + 1

    zeroSectionPField :
      publicModulusField % pAxis ≡ 0

    zeroSectionQField :
      publicModulusField % qAxis ≡ 0

    identitySectionPField :
      publicModulusPlusOneField % pAxis ≡ 1

    identitySectionQField :
      publicModulusPlusOneField % qAxis ≡ 1

    primeWitnessRulePField :
      primePMinusOneField + 1 ≡ pAxis

    primeWitnessRuleQField :
      primeQMinusOneField + 1 ≡ qAxis

    phiFieldFormula :
      phiField ≡ primePMinusOneField * primeQMinusOneField

    primeSumBridgeField :
      pAxis + qAxis ≡ publicModulusField - phiField + 1

    noFactorOracle :
      Bool

    noFactorOracleIsFalse :
      noFactorOracle ≡ false

open RSAPlusOneIdentitySectionRow public

rsaNPlusOneIdentitySection :
  RSAPlusOneIdentitySectionRow rsaPrimeP rsaPrimeQ
rsaNPlusOneIdentitySection =
  mkRSAPlusOneIdentitySectionRow
    RSAA.rsaArithmeticCoreSurface
    RSACRT.canonicalRSACRTChamberCore
    RSAB.canonicalRSAVulnerabilityBoundary
    "public closed composite body"
    "hidden prime axes"
    rsaWitnessEcologyHiddenLabel
    "zero section"
    "identity section"
    "the identity section is not a factor oracle"
    "no-break witness"
    rsaPublicModulus
    rsaPublicModulusPlusOne
    rsaPrimeP
    rsaPrimeQ
    rsaPrimePMinusOne
    rsaPrimeQMinusOne
    rsaPhi
    rsaLambda
    refl
    refl
    rsaZeroSectionP
    rsaZeroSectionQ
    rsaIdentitySectionP
    rsaIdentitySectionQ
    rsaPrimeWitnessRuleP
    rsaPrimeWitnessRuleQ
    refl
    rsaPrimeSumBridge
    rsaPlusOneNoFactorOracle
    refl

------------------------------------------------------------------------
-- Moonshine analogue row.
--
-- This attaches the existing 196883 -> 196884 witness rather than
-- re-proving it locally.

record MoonshinePlusOneAnalogueRow : Set₁ where
  constructor mkMoonshinePlusOneAnalogueRow
  field
    analogueLabel :
      String

    periodReference :
      Nat

    moonshineCoefficientReference :
      Nat

    existingBridgeReference :
      CRT.period + 1 ≡ J.contract J.unit-obs

    scalarBridgeSurface :
      MB.MoonshineScalarBridge

    analogueCandidateOnly :
      Bool

    analogueCandidateOnlyIsTrue :
      analogueCandidateOnly ≡ true

open MoonshinePlusOneAnalogueRow public

moonshinePlusOneAnalogueRow :
  MoonshinePlusOneAnalogueRow
moonshinePlusOneAnalogueRow =
  mkMoonshinePlusOneAnalogueRow
    "196883 + 1 identity-section analogy"
    CRT.period
    MB.moonshineCoefficient
    MB.MoonshineBridge
    MB.moonshineScalarBridgeSurface
    true
    refl

------------------------------------------------------------------------
-- Indexing receipt.

record RSAPlusOneIdentitySectionReceipt : Set₁ where
  constructor mkRSAPlusOneIdentitySectionReceipt
  field
    rsaRow :
      RSAPlusOneIdentitySectionRow rsaPrimeP rsaPrimeQ

    moonshineRow :
      MoonshinePlusOneAnalogueRow

    rsaWitnessEcologyHiddenRow :
      String

    rsaWitnessEcologyHiddenRowIsCanonical :
      rsaWitnessEcologyHiddenRow ≡ rsaWitnessEcologyHidden

open RSAPlusOneIdentitySectionReceipt public

rsaPlusOneIdentitySectionReceipt :
  RSAPlusOneIdentitySectionReceipt
rsaPlusOneIdentitySectionReceipt =
  mkRSAPlusOneIdentitySectionReceipt
    rsaNPlusOneIdentitySection
    moonshinePlusOneAnalogueRow
    rsaWitnessEcologyHidden
    refl
