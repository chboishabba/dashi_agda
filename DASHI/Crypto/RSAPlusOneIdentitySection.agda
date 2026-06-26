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
import DASHI.Algebra.MoonshinePlusOneAnalogue as MPA

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

open RSAPlusOneIdentitySectionRow public

rsaNPlusOneIdentitySection :
  RSAPlusOneIdentitySectionRow rsaPrimeP rsaPrimeQ
rsaNPlusOneIdentitySection =
  mkRSAPlusOneIdentitySectionRow
    RSAA.rsaArithmeticCoreSurface
    RSACRT.canonicalRSACRTChamberCore
    "public closed composite body"
    "hidden prime axes"
    rsaWitnessEcologyHiddenLabel
    "zero section"
    "identity section"
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

------------------------------------------------------------------------
-- Boundary receipt wrapper.

record RSAPlusOneBoundaryReceipt : Set₁ where
  constructor mkRSAPlusOneBoundaryReceipt
  field
    rsaArithmeticRow :
      RSAPlusOneIdentitySectionRow rsaPrimeP rsaPrimeQ

    rsaVulnerabilityBoundaryReference :
      RSAB.RSAVulnerabilityBoundary

    publicLimitationLabel :
      String

    noBreakWitnessLabel :
      String

    noFactorOracle :
      Bool

    noFactorOracleIsFalse :
      noFactorOracle ≡ false

open RSAPlusOneBoundaryReceipt public

rsaPlusOneBoundaryReceipt :
  RSAPlusOneBoundaryReceipt
rsaPlusOneBoundaryReceipt =
  mkRSAPlusOneBoundaryReceipt
    rsaNPlusOneIdentitySection
    RSAB.canonicalRSAVulnerabilityBoundary
    "the identity section is not a factor oracle"
    "no-break witness"
    rsaPlusOneNoFactorOracle
    refl

------------------------------------------------------------------------
-- Indexing receipt.

record RSAPlusOneIdentitySectionReceipt : Set₁ where
  constructor mkRSAPlusOneIdentitySectionReceipt
  field
    rsaArithmeticRow :
      RSAPlusOneIdentitySectionRow rsaPrimeP rsaPrimeQ

    rsaBoundaryReceipt :
      RSAPlusOneBoundaryReceipt

    moonshineRow :
      MPA.MoonshinePlusOneAnalogueRow

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
    rsaPlusOneBoundaryReceipt
    MPA.canonicalMoonshinePlusOneAnalogueRow
    rsaWitnessEcologyHidden
    refl
