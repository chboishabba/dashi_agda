module DASHI.Physics.Moonshine.ModularJInvariantAlphaReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.AuthorityBoundary as Authority

------------------------------------------------------------------------
-- Modular j/Eisenstein alpha geometry receipt.
--
-- This module records authority-backed modular anchors that may be useful for
-- later alpha-geometry investigations.  It deliberately does not derive the
-- alpha1/alpha2 diagnostics used by the carrier-Yukawa and Cabibbo receipts:
-- no formal bridge from j/Eisenstein geometry to those alpha readbacks is
-- constructed here.

data ModularJInvariantAlphaStatus : Set where
  modularAnchorsRecordedNoAlphaDerivation :
    ModularJInvariantAlphaStatus

data ModularJInvariantAlphaCitation : Set where
  classicalModularJInvariantCitation :
    ModularJInvariantAlphaCitation

  eisensteinSeriesEllipticPointCitation :
    ModularJInvariantAlphaCitation

data ModularJInvariantAlphaAnchor : Set where
  jAtIEquals1728Anchor :
    ModularJInvariantAlphaAnchor

  jAtRhoEqualsZeroAnchor :
    ModularJInvariantAlphaAnchor

  jAtHeegnerSevenEqualsNegative3375Anchor :
    ModularJInvariantAlphaAnchor

  pdg2024MSbarUpCharmMassRatioAnchor :
    ModularJInvariantAlphaAnchor

data ModularJInvariantAlphaBlocker : Set where
  missingFormalModularJToAlphaMap :
    ModularJInvariantAlphaBlocker

  alphaTwoNumericalMatchNotFoundInTestedNormalizations :
    ModularJInvariantAlphaBlocker

  alphaOneNearHitIsOnlyHeuristicNormalization :
    ModularJInvariantAlphaBlocker

  alphaOneCorrectionFactorNotIdentified :
    ModularJInvariantAlphaBlocker

  missingEisensteinNormalizationToCarrierAlphaProof :
    ModularJInvariantAlphaBlocker

  missingDiscriminantPeterssonCarrierNormalizationProof :
    ModularJInvariantAlphaBlocker

  missingAlphaOneAlphaTwoEqualityOrErrorBound :
    ModularJInvariantAlphaBlocker

  missingCarrierYukawaCabibboPromotionBridge :
    ModularJInvariantAlphaBlocker

canonicalModularJInvariantAlphaCitations :
  List ModularJInvariantAlphaCitation
canonicalModularJInvariantAlphaCitations =
  classicalModularJInvariantCitation
  ∷ eisensteinSeriesEllipticPointCitation
  ∷ []

canonicalModularJInvariantAlphaAnchors :
  List ModularJInvariantAlphaAnchor
canonicalModularJInvariantAlphaAnchors =
  jAtIEquals1728Anchor
  ∷ jAtRhoEqualsZeroAnchor
  ∷ jAtHeegnerSevenEqualsNegative3375Anchor
  ∷ pdg2024MSbarUpCharmMassRatioAnchor
  ∷ []

canonicalModularJInvariantAlphaBlockers :
  List ModularJInvariantAlphaBlocker
canonicalModularJInvariantAlphaBlockers =
  missingFormalModularJToAlphaMap
  ∷ alphaTwoNumericalMatchNotFoundInTestedNormalizations
  ∷ alphaOneNearHitIsOnlyHeuristicNormalization
  ∷ alphaOneCorrectionFactorNotIdentified
  ∷ missingEisensteinNormalizationToCarrierAlphaProof
  ∷ missingDiscriminantPeterssonCarrierNormalizationProof
  ∷ missingAlphaOneAlphaTwoEqualityOrErrorBound
  ∷ missingCarrierYukawaCabibboPromotionBridge
  ∷ []

jAtILabel : String
jAtILabel =
  "j(i) = 1728"

jAtRhoLabel : String
jAtRhoLabel =
  "j(rho) = 0"

jAtHeegnerSevenLabel : String
jAtHeegnerSevenLabel =
  "j((1+i*sqrt(7))/2) = -3375"

jDifferenceIRhoLabel : String
jDifferenceIRhoLabel =
  "|j(i)-j(rho)| = 1728"

jDifferenceIHeegnerSevenLabel : String
jDifferenceIHeegnerSevenLabel =
  "|j(i)-j((1+i*sqrt(7))/2)| = 5103"

jDifferenceRhoHeegnerSevenLabel : String
jDifferenceRhoHeegnerSevenLabel =
  "|j(rho)-j((1+i*sqrt(7))/2)| = 3375"

alphaFromJNumericalReportPathLabel : String
alphaFromJNumericalReportPathLabel =
  "Docs/AlphaFromJNumericalCheck.md"

alphaOneNumericalNearHitLabel : String
alphaOneNumericalNearHitLabel =
  "72 / |j(i)-j(rho)| = 72/1728 = 1/24 = 0.041666666667; alpha1 = sqrt(mu/mc) = 0.0412406 from PDG 2024 MSbar masses mu=2.16 MeV and mc=1.27 GeV at 2 GeV; discrepancy is about 1.03%; match=true at tolerance 0.001"

alphaOneModularMeaningLabel : String
alphaOneModularMeaningLabel =
  "72 = 3 * 24 is modularly meaningful: 3 is the elliptic stabilizer order at rho in PSL2Z, and 24 is the weight of Delta = eta^24"

alphaOneCorrectionLabel : String
alphaOneCorrectionLabel =
  "alpha1 / (1/24) = 0.98977 using alpha1=sqrt(mu/mc); correction factor not identified as Gamma/pi/algebraic constant"

alphaTwoNumericalNoHitLabel : String
alphaTwoNumericalNoHitLabel =
  "No tested normalization matched target alpha2 = 0.085720 at tolerance 0.001; alpha2 match=false"

alphaTwoModularNearHitLabel : String
alphaTwoModularNearHitLabel =
  "No modular near-hit for alpha2 is recorded by the tested j/Eisenstein normalizations"

alphaFromJNumericalConclusionLabel : String
alphaFromJNumericalConclusionLabel =
  "PDG mass-ratio alpha1 is numerically near the modular natural value 1/24, but this is not a modular derivation and gives no alpha2 formula"

eisensteinEllipticPointLabel : String
eisensteinEllipticPointLabel =
  "E4 vanishes at rho and E6 vanishes at i under the classical normalization"

alphaOneDiagnosticLabel : String
alphaOneDiagnosticLabel =
  "alpha1 equals sqrt(mu/mc) to five significant figures, using PDG 2024 MSbar masses at 2 GeV, and is not derived here from modular geometry"

alphaTwoDiagnosticLabel : String
alphaTwoDiagnosticLabel =
  "alpha2 approximately 0.086 is a carrier-Yukawa diagnostic, not derived here"

alphaOnePDGMassRatioLabel : String
alphaOnePDGMassRatioLabel =
  "alpha1 = sqrt(mu/mc) = 0.0412406 to five significant figures from PDG 2024 MSbar masses mu=2.16 MeV and mc=1.27 GeV at 2 GeV"

alphaOnePDGRatioCheckLabel : String
alphaOnePDGRatioCheckLabel =
  "alpha1 / sqrt(mu/mc) = 0.99999 at the recorded precision"

alphaOneModularNaturalComparisonLabel : String
alphaOneModularNaturalComparisonLabel =
  "1/24 = 0.041666666667 remains a modular natural value within about 1-2% of alpha1=sqrt(mu/mc)"

alphaOneSquaredModularComparisonLabel : String
alphaOneSquaredModularComparisonLabel =
  "(1/24)^2 = 0.001736111111 is within about 2% of mu/mc = 0.001700787402"

modularJClassicalCitationAuthority :
  Authority.CitationAuthorityBoundary
modularJClassicalCitationAuthority =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "classical modular j-invariant and Eisenstein elliptic-point anchors"
    "Classical modular-form authority for j(i)=1728, j(rho)=0, and the normalized Eisenstein/discriminant construction"
    true
    false
    false
    ( "CitationAuthority only: no machine-readable alpha artifact is claimed"
      ∷ "The receipt records modular anchors j(i)=1728, j(rho)=0, j((1+i*sqrt(7))/2)=-3375, and the PDG 2024 MSbar up/charm mass-ratio alpha1 interpretation, but does not derive alpha1 or alpha2"
      ∷ []
    )

modularJClassicalCitationNoArtifact :
  Authority.CitationAuthorityNoArtifact
modularJClassicalCitationNoArtifact =
  Authority.mkCitationAuthorityNoArtifact
    modularJClassicalCitationAuthority
    refl
    refl
    refl

record ModularJInvariantAlphaReceipt : Setω where
  field
    status :
      ModularJInvariantAlphaStatus

    citations :
      List ModularJInvariantAlphaCitation

    citationsAreCanonical :
      citations ≡ canonicalModularJInvariantAlphaCitations

    citationAuthority :
      Authority.CitationAuthorityBoundary

    citationAuthorityIsCanonical :
      citationAuthority ≡ modularJClassicalCitationAuthority

    citationAuthorityHasNoArtifact :
      Authority.CitationAuthorityNoArtifact

    anchors :
      List ModularJInvariantAlphaAnchor

    anchorsAreCanonical :
      anchors ≡ canonicalModularJInvariantAlphaAnchors

    jAtIParts :
      Nat

    jAtIPartsIs1728 :
      jAtIParts ≡ 1728

    jAtIStatement :
      String

    jAtIStatementIsCanonical :
      jAtIStatement ≡ jAtILabel

    jAtRhoParts :
      Nat

    jAtRhoPartsIsZero :
      jAtRhoParts ≡ 0

    jAtRhoStatement :
      String

    jAtRhoStatementIsCanonical :
      jAtRhoStatement ≡ jAtRhoLabel

    jAtHeegnerSevenStatement :
      String

    jAtHeegnerSevenStatementIsCanonical :
      jAtHeegnerSevenStatement ≡ jAtHeegnerSevenLabel

    jDifferenceIRhoParts :
      Nat

    jDifferenceIRhoPartsIs1728 :
      jDifferenceIRhoParts ≡ 1728

    jDifferenceIRhoStatement :
      String

    jDifferenceIRhoStatementIsCanonical :
      jDifferenceIRhoStatement ≡ jDifferenceIRhoLabel

    jDifferenceIHeegnerSevenParts :
      Nat

    jDifferenceIHeegnerSevenPartsIs5103 :
      jDifferenceIHeegnerSevenParts ≡ 5103

    jDifferenceIHeegnerSevenStatement :
      String

    jDifferenceIHeegnerSevenStatementIsCanonical :
      jDifferenceIHeegnerSevenStatement ≡ jDifferenceIHeegnerSevenLabel

    jDifferenceRhoHeegnerSevenParts :
      Nat

    jDifferenceRhoHeegnerSevenPartsIs3375 :
      jDifferenceRhoHeegnerSevenParts ≡ 3375

    jDifferenceRhoHeegnerSevenStatement :
      String

    jDifferenceRhoHeegnerSevenStatementIsCanonical :
      jDifferenceRhoHeegnerSevenStatement ≡ jDifferenceRhoHeegnerSevenLabel

    eisensteinEllipticPointStatement :
      String

    eisensteinEllipticPointStatementIsCanonical :
      eisensteinEllipticPointStatement ≡ eisensteinEllipticPointLabel

    alphaOneProbeLabel :
      String

    alphaOneProbeLabelIsCanonical :
      alphaOneProbeLabel ≡ alphaOneDiagnosticLabel

    alphaTwoProbeLabel :
      String

    alphaTwoProbeLabelIsCanonical :
      alphaTwoProbeLabel ≡ alphaTwoDiagnosticLabel

    alphaOnePDGMassRatioStatement :
      String

    alphaOnePDGMassRatioStatementIsCanonical :
      alphaOnePDGMassRatioStatement ≡ alphaOnePDGMassRatioLabel

    alphaOnePDGRatioCheckStatement :
      String

    alphaOnePDGRatioCheckStatementIsCanonical :
      alphaOnePDGRatioCheckStatement ≡ alphaOnePDGRatioCheckLabel

    alphaOneModularNaturalComparison :
      String

    alphaOneModularNaturalComparisonIsCanonical :
      alphaOneModularNaturalComparison ≡ alphaOneModularNaturalComparisonLabel

    alphaOneSquaredModularComparison :
      String

    alphaOneSquaredModularComparisonIsCanonical :
      alphaOneSquaredModularComparison ≡ alphaOneSquaredModularComparisonLabel

    alphaFromJNumericalReportPath :
      String

    alphaFromJNumericalReportPathIsCanonical :
      alphaFromJNumericalReportPath ≡ alphaFromJNumericalReportPathLabel

    alphaOneNumericalNearHit :
      Bool

    alphaOneNumericalNearHitIsTrue :
      alphaOneNumericalNearHit ≡ true

    alphaOneNumericalNearHitStatement :
      String

    alphaOneNumericalNearHitStatementIsCanonical :
      alphaOneNumericalNearHitStatement ≡ alphaOneNumericalNearHitLabel

    alphaOneNearHitModularMeaning :
      String

    alphaOneNearHitModularMeaningIsCanonical :
      alphaOneNearHitModularMeaning ≡ alphaOneModularMeaningLabel

    alphaOneCorrectionIdentified :
      Bool

    alphaOneCorrectionIdentifiedIsFalse :
      alphaOneCorrectionIdentified ≡ false

    alphaOneCorrectionStatement :
      String

    alphaOneCorrectionStatementIsCanonical :
      alphaOneCorrectionStatement ≡ alphaOneCorrectionLabel

    alphaTwoNumericalMatch :
      Bool

    alphaTwoNumericalMatchIsFalse :
      alphaTwoNumericalMatch ≡ false

    alphaTwoNumericalMatchStatement :
      String

    alphaTwoNumericalMatchStatementIsCanonical :
      alphaTwoNumericalMatchStatement ≡ alphaTwoNumericalNoHitLabel

    alphaTwoModularNearHit :
      Bool

    alphaTwoModularNearHitIsFalse :
      alphaTwoModularNearHit ≡ false

    alphaTwoModularNearHitStatement :
      String

    alphaTwoModularNearHitStatementIsCanonical :
      alphaTwoModularNearHitStatement ≡ alphaTwoModularNearHitLabel

    simultaneousAlphaOneAlphaTwoNumericalDerivation :
      Bool

    simultaneousAlphaOneAlphaTwoNumericalDerivationIsFalse :
      simultaneousAlphaOneAlphaTwoNumericalDerivation ≡ false

    alphaFromJNumericalConclusion :
      String

    alphaFromJNumericalConclusionIsCanonical :
      alphaFromJNumericalConclusion ≡ alphaFromJNumericalConclusionLabel

    alphaDerivedFromModularGeometry :
      Bool

    alphaDerivedFromModularGeometryIsFalse :
      alphaDerivedFromModularGeometry ≡ false

    alphaOneDerivedFromModularGeometry :
      Bool

    alphaOneDerivedFromModularGeometryIsFalse :
      alphaOneDerivedFromModularGeometry ≡ false

    alphaTwoDerivedFromModularGeometry :
      Bool

    alphaTwoDerivedFromModularGeometryIsFalse :
      alphaTwoDerivedFromModularGeometry ≡ false

    alphaValuesPromoted :
      Bool

    alphaValuesPromotedIsFalse :
      alphaValuesPromoted ≡ false

    blockers :
      List ModularJInvariantAlphaBlocker

    blockersAreCanonical :
      blockers ≡ canonicalModularJInvariantAlphaBlockers

    receiptBoundary :
      List String

open ModularJInvariantAlphaReceipt public

canonicalModularJInvariantAlphaReceipt :
  ModularJInvariantAlphaReceipt
canonicalModularJInvariantAlphaReceipt =
  record
    { status =
        modularAnchorsRecordedNoAlphaDerivation
    ; citations =
        canonicalModularJInvariantAlphaCitations
    ; citationsAreCanonical =
        refl
    ; citationAuthority =
        modularJClassicalCitationAuthority
    ; citationAuthorityIsCanonical =
        refl
    ; citationAuthorityHasNoArtifact =
        modularJClassicalCitationNoArtifact
    ; anchors =
        canonicalModularJInvariantAlphaAnchors
    ; anchorsAreCanonical =
        refl
    ; jAtIParts =
        1728
    ; jAtIPartsIs1728 =
        refl
    ; jAtIStatement =
        jAtILabel
    ; jAtIStatementIsCanonical =
        refl
    ; jAtRhoParts =
        0
    ; jAtRhoPartsIsZero =
        refl
    ; jAtRhoStatement =
        jAtRhoLabel
    ; jAtRhoStatementIsCanonical =
        refl
    ; jAtHeegnerSevenStatement =
        jAtHeegnerSevenLabel
    ; jAtHeegnerSevenStatementIsCanonical =
        refl
    ; jDifferenceIRhoParts =
        1728
    ; jDifferenceIRhoPartsIs1728 =
        refl
    ; jDifferenceIRhoStatement =
        jDifferenceIRhoLabel
    ; jDifferenceIRhoStatementIsCanonical =
        refl
    ; jDifferenceIHeegnerSevenParts =
        5103
    ; jDifferenceIHeegnerSevenPartsIs5103 =
        refl
    ; jDifferenceIHeegnerSevenStatement =
        jDifferenceIHeegnerSevenLabel
    ; jDifferenceIHeegnerSevenStatementIsCanonical =
        refl
    ; jDifferenceRhoHeegnerSevenParts =
        3375
    ; jDifferenceRhoHeegnerSevenPartsIs3375 =
        refl
    ; jDifferenceRhoHeegnerSevenStatement =
        jDifferenceRhoHeegnerSevenLabel
    ; jDifferenceRhoHeegnerSevenStatementIsCanonical =
        refl
    ; eisensteinEllipticPointStatement =
        eisensteinEllipticPointLabel
    ; eisensteinEllipticPointStatementIsCanonical =
        refl
    ; alphaOneProbeLabel =
        alphaOneDiagnosticLabel
    ; alphaOneProbeLabelIsCanonical =
        refl
    ; alphaTwoProbeLabel =
        alphaTwoDiagnosticLabel
    ; alphaTwoProbeLabelIsCanonical =
        refl
    ; alphaOnePDGMassRatioStatement =
        alphaOnePDGMassRatioLabel
    ; alphaOnePDGMassRatioStatementIsCanonical =
        refl
    ; alphaOnePDGRatioCheckStatement =
        alphaOnePDGRatioCheckLabel
    ; alphaOnePDGRatioCheckStatementIsCanonical =
        refl
    ; alphaOneModularNaturalComparison =
        alphaOneModularNaturalComparisonLabel
    ; alphaOneModularNaturalComparisonIsCanonical =
        refl
    ; alphaOneSquaredModularComparison =
        alphaOneSquaredModularComparisonLabel
    ; alphaOneSquaredModularComparisonIsCanonical =
        refl
    ; alphaFromJNumericalReportPath =
        alphaFromJNumericalReportPathLabel
    ; alphaFromJNumericalReportPathIsCanonical =
        refl
    ; alphaOneNumericalNearHit =
        true
    ; alphaOneNumericalNearHitIsTrue =
        refl
    ; alphaOneNumericalNearHitStatement =
        alphaOneNumericalNearHitLabel
    ; alphaOneNumericalNearHitStatementIsCanonical =
        refl
    ; alphaOneNearHitModularMeaning =
        alphaOneModularMeaningLabel
    ; alphaOneNearHitModularMeaningIsCanonical =
        refl
    ; alphaOneCorrectionIdentified =
        false
    ; alphaOneCorrectionIdentifiedIsFalse =
        refl
    ; alphaOneCorrectionStatement =
        alphaOneCorrectionLabel
    ; alphaOneCorrectionStatementIsCanonical =
        refl
    ; alphaTwoNumericalMatch =
        false
    ; alphaTwoNumericalMatchIsFalse =
        refl
    ; alphaTwoNumericalMatchStatement =
        alphaTwoNumericalNoHitLabel
    ; alphaTwoNumericalMatchStatementIsCanonical =
        refl
    ; alphaTwoModularNearHit =
        false
    ; alphaTwoModularNearHitIsFalse =
        refl
    ; alphaTwoModularNearHitStatement =
        alphaTwoModularNearHitLabel
    ; alphaTwoModularNearHitStatementIsCanonical =
        refl
    ; simultaneousAlphaOneAlphaTwoNumericalDerivation =
        false
    ; simultaneousAlphaOneAlphaTwoNumericalDerivationIsFalse =
        refl
    ; alphaFromJNumericalConclusion =
        alphaFromJNumericalConclusionLabel
    ; alphaFromJNumericalConclusionIsCanonical =
        refl
    ; alphaDerivedFromModularGeometry =
        false
    ; alphaDerivedFromModularGeometryIsFalse =
        refl
    ; alphaOneDerivedFromModularGeometry =
        false
    ; alphaOneDerivedFromModularGeometryIsFalse =
        refl
    ; alphaTwoDerivedFromModularGeometry =
        false
    ; alphaTwoDerivedFromModularGeometryIsFalse =
        refl
    ; alphaValuesPromoted =
        false
    ; alphaValuesPromotedIsFalse =
        refl
    ; blockers =
        canonicalModularJInvariantAlphaBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "The receipt records classical modular anchors j(i)=1728, j(rho)=0, j((1+i*sqrt(7))/2)=-3375, and the PDG 2024 MSbar up/charm mass-ratio alpha1 interpretation"
        ∷ "The computed absolute CM j-value differences are 1728, 5103, and 3375"
        ∷ "alpha1 is interpreted as sqrt(mu/mc) = 0.0412406 to five significant figures, with alpha1/sqrt(mu/mc) = 0.99999 against PDG 2024 MSbar masses at 2 GeV"
        ∷ "scripts/check_alpha_from_j_values.py finds alpha1 match=true only for 72/|j(i)-j(rho)| = 72/1728 = 1/24 within tolerance 0.001, where 1/24 remains a modular natural value about 1.03% above alpha1"
        ∷ "(1/24)^2 remains within about 2% of mu/mc, but this squared comparison is also numerical bookkeeping rather than a derivation"
        ∷ "The same numerical check finds alpha2 match=false and alphaTwoModularNearHit=false for every tested normalization"
        ∷ "The numerical conclusion is partial heuristic evidence only, not a simultaneous alpha1/alpha2 derivation"
        ∷ "The factor 72 = 3 * 24 is modularly meaningful: 3 is the elliptic stabilizer order at rho in PSL2Z, and 24 is the weight of Delta = eta^24"
        ∷ "The alpha1 correction factor alpha1/(1/24) = 0.98977 is not identified, so the near-hit remains a signal rather than a derivation"
        ∷ "The next admissible probe is a discriminant/Petersson normalization with an independently defined carrier metric constant c0"
        ∷ "The Eisenstein elliptic-point statement is authority-backed bookkeeping only"
        ∷ "alpha1 and alpha2 remain diagnostics from the carrier-Yukawa/Cabibbo lane, not modular-geometry derivations"
        ∷ "alphaDerivedFromModularGeometry is false because no formal j/Eisenstein-to-alpha bridge is constructed"
        ∷ "No accepted alpha value, common-alpha proof, Cabibbo derivation, or physical promotion is claimed"
        ∷ []
    }

modularJInvariantAlphaReceiptKeepsDerivationClosed :
  alphaDerivedFromModularGeometry canonicalModularJInvariantAlphaReceipt
  ≡
  false
modularJInvariantAlphaReceiptKeepsDerivationClosed =
  refl

modularJInvariantAlphaReceiptKeepsAlphaOneDerivationClosed :
  alphaOneDerivedFromModularGeometry canonicalModularJInvariantAlphaReceipt
  ≡
  false
modularJInvariantAlphaReceiptKeepsAlphaOneDerivationClosed =
  refl

modularJInvariantAlphaReceiptKeepsAlphaTwoDerivationClosed :
  alphaTwoDerivedFromModularGeometry canonicalModularJInvariantAlphaReceipt
  ≡
  false
modularJInvariantAlphaReceiptKeepsAlphaTwoDerivationClosed =
  refl

modularJInvariantAlphaReceiptKeepsAlphaValuesUnpromoted :
  alphaValuesPromoted canonicalModularJInvariantAlphaReceipt
  ≡
  false
modularJInvariantAlphaReceiptKeepsAlphaValuesUnpromoted =
  refl

modularJInvariantAlphaReceiptRecordsJAtI :
  jAtIParts canonicalModularJInvariantAlphaReceipt
  ≡
  1728
modularJInvariantAlphaReceiptRecordsJAtI =
  refl

modularJInvariantAlphaReceiptRecordsJAtRho :
  jAtRhoParts canonicalModularJInvariantAlphaReceipt
  ≡
  0
modularJInvariantAlphaReceiptRecordsJAtRho =
  refl

modularJInvariantAlphaReceiptRecordsAlphaOneNearHit :
  alphaOneNumericalNearHit canonicalModularJInvariantAlphaReceipt
  ≡
  true
modularJInvariantAlphaReceiptRecordsAlphaOneNearHit =
  refl

modularJInvariantAlphaReceiptRecordsPDGMassRatioAlphaOne :
  alphaOnePDGMassRatioStatement canonicalModularJInvariantAlphaReceipt
  ≡
  alphaOnePDGMassRatioLabel
modularJInvariantAlphaReceiptRecordsPDGMassRatioAlphaOne =
  refl

modularJInvariantAlphaReceiptRecordsPDGRatioCheck :
  alphaOnePDGRatioCheckStatement canonicalModularJInvariantAlphaReceipt
  ≡
  alphaOnePDGRatioCheckLabel
modularJInvariantAlphaReceiptRecordsPDGRatioCheck =
  refl

modularJInvariantAlphaReceiptRecordsModularNaturalComparison :
  alphaOneModularNaturalComparison canonicalModularJInvariantAlphaReceipt
  ≡
  alphaOneModularNaturalComparisonLabel
modularJInvariantAlphaReceiptRecordsModularNaturalComparison =
  refl

modularJInvariantAlphaReceiptRecordsSquaredModularComparison :
  alphaOneSquaredModularComparison canonicalModularJInvariantAlphaReceipt
  ≡
  alphaOneSquaredModularComparisonLabel
modularJInvariantAlphaReceiptRecordsSquaredModularComparison =
  refl

modularJInvariantAlphaReceiptKeepsAlphaOneCorrectionUnidentified :
  alphaOneCorrectionIdentified canonicalModularJInvariantAlphaReceipt
  ≡
  false
modularJInvariantAlphaReceiptKeepsAlphaOneCorrectionUnidentified =
  refl

modularJInvariantAlphaReceiptRecordsAlphaTwoNoHit :
  alphaTwoNumericalMatch canonicalModularJInvariantAlphaReceipt
  ≡
  false
modularJInvariantAlphaReceiptRecordsAlphaTwoNoHit =
  refl

modularJInvariantAlphaReceiptKeepsAlphaTwoModularNearHitFalse :
  alphaTwoModularNearHit canonicalModularJInvariantAlphaReceipt
  ≡
  false
modularJInvariantAlphaReceiptKeepsAlphaTwoModularNearHitFalse =
  refl

modularJInvariantAlphaReceiptKeepsSimultaneousDerivationClosed :
  simultaneousAlphaOneAlphaTwoNumericalDerivation
    canonicalModularJInvariantAlphaReceipt
  ≡
  false
modularJInvariantAlphaReceiptKeepsSimultaneousDerivationClosed =
  refl
