module DASHI.Crypto.RSA260ExternalFactorizationSourceReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence
import DASHI.Core.GenericReceipt as Receipt
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SearchBridge
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- RSA-260 EXTERNAL FACTORIZATION RECEIPT
--
-- On 2026-09-03 Eric Lu (@penlume) posted one 130-digit divisor of RSA-260.
-- The complementary 130-digit factor and exact reconstructed 260-digit modulus
-- are retained below as decimal source data.
--
-- This owner is deliberately source/provenance level.  It does NOT force the
-- 260-digit multiplication through the ordinary Agda Nat normalizer inside the
-- small CS validation cone.  Kernel certification of the giant arithmetic is a
-- separate proof-debt coordinate.
------------------------------------------------------------------------

rsa260ModulusDecimal : String
rsa260ModulusDecimal =
  "22112825529529666435281085255026230927612089502470015394413748319128822941402001986512729726569746599085900330031400051170742204560859276357953757185954298838958709229238491006703034124620545784566413664540684214361293017694020846391065875914794251435144458199"

rsa260PublishedFactorDecimal : String
rsa260PublishedFactorDecimal =
  "4397328654844826923795068102505872571721883526553349659561256924505973939597593482272505698004801207988043088656411102133523080581"

rsa260ComplementaryFactorDecimal : String
rsa260ComplementaryFactorDecimal =
  "5028695206842569864686141618253083416610081090075366674776775706538324961364412200138116378509733307971876652984898985905923678379"

rsa260DecimalDigits : Nat
rsa260DecimalDigits = 260

rsa260BitLength : Nat
rsa260BitLength = 862

publishedFactorDecimalDigits : Nat
publishedFactorDecimalDigits = 130

complementaryFactorDecimalDigits : Nat
complementaryFactorDecimalDigits = 130

------------------------------------------------------------------------
-- Canonical attributed sources.
------------------------------------------------------------------------

ericLuXSource : Source.AttributedSource
ericLuXSource =
  Source.mkNoDOISource
    "Eric Lu (@penlume)"
    "divides RSA-260"
    "X post"
    "2026"
    "https://x.com/penlume/status/2095372672356212876"
    (Source.namedSourceKind "social-media primary announcement")
    "primary announcement of one published RSA-260 divisor"
    Source.publicAttribution

johnCookCorroboratingSource : Source.AttributedSource
johnCookCorroboratingSource =
  Source.mkNoDOISource
    "John D. Cook"
    "New RSA number factored"
    "John D. Cook blog"
    "2026"
    "https://www.johndcook.com/blog/2026/09/03/new-rsa-number-factored/"
    Source.practitionerSource
    "corroborating report identifying RSA-260, date, size and Eric Lu announcement"
    Source.publicAttribution

rsa260SourceAtlas : Source.AttributedSourceAtlas
rsa260SourceAtlas =
  Source.mkSourceAtlas
    "RSA-260 September 2026 factorization sources"
    "DASHI.Crypto.RSA260ExternalFactorizationSourceReceiptExact"
    (ericLuXSource ∷ johnCookCorroboratingSource ∷ [])
    "primary announcement plus corroborating report; source identity does not itself kernel-prove the multiplication or disclose the factorization method"

------------------------------------------------------------------------
-- Source diligence for the bounded proposition actually supported.
------------------------------------------------------------------------

rsa260FactorizationDiligence : Diligence.SourceDiligence
rsa260FactorizationDiligence =
  Diligence.source-diligence
    "Eric Lu published a divisor of RSA-260 on 2026-09-03"
    ericLuXSource
    Diligence.primaryProposition
    true
    refl
    "direct primary X status located; corroborating independent reports checked"
    Diligence.primaryLocated
    "X status 2095372672356212876; literal 130-digit divisor string retained above"
    "2026-09-03"
    "same RSA-260 challenge modulus as the 260-decimal-digit RSA Factoring Challenge number"
    "announcement date and public state through 2026-09-09"
    "covers publication of divisor; does not cover undisclosed computational method"
    "checked for reports contradicting the divisibility/factorization; none retained by this atlas"
    "factor publication is separated from claims about algorithm, hardware, AI, quantum execution or shared-prime weakness"
    "applicable to RSA-260 challenge-number factorization only; not a claim that deployed RSA-2048 is broken"

rsa260FactorizationAdmission : Diligence.EmpiricalFactAdmission
rsa260FactorizationAdmission =
  Diligence.empirical-fact-admission
    rsa260FactorizationDiligence
    "bounded proposition: the published 130-digit integer divides RSA-260 and yields the retained complementary factor"
    "primary post supplies the divisor; corroborating reports reproduce/verify the resulting factorization"
    "modulus, published factor, complementary factor, date and source identity remain explicit after projection"
    "method of factorization remains undisclosed in the sources admitted here; giant arithmetic is not Agda-kernel-certified here"
    "downstream cryptographic interpretation remains separately typed"
    false refl false refl false refl

------------------------------------------------------------------------
-- Separate mathematical / method / certification coordinates.
------------------------------------------------------------------------

data FactorizationStatementStatus : Set where
  externallyVerifiedFactorizationIdentity : FactorizationStatementStatus

data FactorizationMethodStatus : Set where
  methodPubliclyUnresolved : FactorizationMethodStatus

data GiantArithmeticCertificationStatus : Set where
  externalBigIntegerVerificationOnly : GiantArithmeticCertificationStatus
  dedicatedKernelCertificationAvailable : GiantArithmeticCertificationStatus

record RSA260ExternalFactorizationReceipt : Set where
  constructor rsa260-external-factorization-receipt
  field
    modulusDecimal : String
    publishedFactorDecimal : String
    complementaryFactorDecimal : String
    decimalDigits : Nat
    bitLength : Nat
    statementStatus : FactorizationStatementStatus
    methodStatus : FactorizationMethodStatus
    certificationStatus : GiantArithmeticCertificationStatus
    primarySource : Source.AttributedSource
    sourceAdmission : Diligence.EmpiricalFactAdmission
    sharedPrimeBatchGCDClaimed : Bool
    quantumFactorizationClaimed : Bool
    modernRSA2048BrokenClaimed : Bool
    agdaNatMultiplicationKernelCertifiedHere : Bool

open RSA260ExternalFactorizationReceipt public

canonicalRSA260ExternalFactorizationReceipt : RSA260ExternalFactorizationReceipt
canonicalRSA260ExternalFactorizationReceipt =
  rsa260-external-factorization-receipt
    rsa260ModulusDecimal
    rsa260PublishedFactorDecimal
    rsa260ComplementaryFactorDecimal
    rsa260DecimalDigits
    rsa260BitLength
    externallyVerifiedFactorizationIdentity
    methodPubliclyUnresolved
    externalBigIntegerVerificationOnly
    ericLuXSource
    rsa260FactorizationAdmission
    false
    false
    false
    false

------------------------------------------------------------------------
-- Live acquisition obligation: method provenance is still open.
------------------------------------------------------------------------

rsa260MethodSearchDemand : SearchBridge.SourceDiligenceSearchDemand
rsa260MethodSearchDemand =
  SearchBridge.source-diligence-search-demand
    "what algorithm/resources produced the RSA-260 factorization?"
    SearchBridge.coverageUnresolved
    Search.empiricalEvidenceProducer
    refl
    "RSA-260 method provenance / factoring-complexity consumer"
    "seek Eric Lu primary technical disclosure, write-up, code, runtime/resource receipt or subsequent paper; do not infer method from employer or social-media speculation"

------------------------------------------------------------------------
-- Fail-closed generic receipt.
------------------------------------------------------------------------

rsa260ExternalFactorizationGenericReceipt : Receipt.GenericReceipt
rsa260ExternalFactorizationGenericReceipt =
  Receipt.mkNonPromotingReceipt
    "RSA-260 external factorization source receipt"
    "DASHI.Crypto.RSA260ExternalFactorizationSourceReceiptExact"
    "source-diligent decimal modulus/factors + statement/method/certification split"
    "records the 2026-09-03 RSA-260 factor publication with exact decimal strings and source provenance"
    "factorization method remains unresolved; giant multiplication is externally checked but not certified through Agda Nat normalization in this module"
    "agda -i . DASHI/Crypto/RSA260ExternalFactorizationSourceReceiptExact.agda"

record RSA260Boundary : Set where
  constructor rsa260-boundary
  field
    publishedDivisorRecorded : Bool
    complementaryFactorRecorded : Bool
    exactDecimalModulusRecorded : Bool
    methodKnownFromAdmittedPrimarySource : Bool
    sharedPrimeAttackClaimed : Bool
    quantumMethodClaimed : Bool
    deployedRSA2048BreakClaimed : Bool
    externalVerificationEqualsAgdaKernelCertification : Bool

canonicalRSA260Boundary : RSA260Boundary
canonicalRSA260Boundary =
  rsa260-boundary true true true false false false false false
