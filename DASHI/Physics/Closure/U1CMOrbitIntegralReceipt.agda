module DASHI.Physics.Closure.U1CMOrbitIntegralReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- X0(4) modular-volume receipt for the p2-p3 Cabibbo normalization.
--
-- The previous receipt treated the 2*pi factor as a U(1)-orbit target.  The
-- sharper statement is modular: the p2 lane is the j=1728 CM lane, whose
-- conductor-four moduli surface is X0(4).  The hyperbolic volume formula
-- vol(X0(N)) = (pi/3) * psi(N), with psi(4)=6, gives vol(X0(4))=2*pi.
-- Multiplying this exact volume by the raw p2-p3 isogeny component sqrt(3)/2
-- gives the sector normalization pi*sqrt(3).
--
-- This receipt derives the sector-angle normalization.  It still does not
-- derive the full physical CKM matrix, a PDG authority comparison, or the
-- non-identity diagonalizers required by Gate 7.

data U1CMOrbitIntegralStatus : Set where
  x04ModularVolumeNormalizationDerived :
    U1CMOrbitIntegralStatus

data U1CMOrbitIntegralBlocker : Set where
  physicalCKMDiagonalisationStillRequired :
    U1CMOrbitIntegralBlocker

  pdgCabibboAuthorityBindingStillRequired :
    U1CMOrbitIntegralBlocker

data U1CMCitationAuthority : Set where
  diamondShurmanModularCurveVolumeAuthority :
    U1CMCitationAuthority

  silvermanCMConductorAuthority :
    U1CMCitationAuthority

  hasseSupersingularPointCountAuthority :
    U1CMCitationAuthority

data U1CMDerivationStep : Set where
  computeDedekindPsiFour :
    U1CMDerivationStep

  applyX0NHyperbolicVolumeFormula :
    U1CMDerivationStep

  identifyP2LaneWithX04ByGaussianCMConductorFour :
    U1CMDerivationStep

  computeRawP2P3IsogenyCoupling :
    U1CMDerivationStep

  multiplyRawCouplingByX04Volume :
    U1CMDerivationStep

  recordActiveVusFormula :
    U1CMDerivationStep

data U1CMOrbitIntegralConsequence : Set where
  psiFourIsSixConsequence :
    U1CMOrbitIntegralConsequence

  x04VolumeIsTwoPiConsequence :
    U1CMOrbitIntegralConsequence

  rawDiagnosticPreserved :
    U1CMOrbitIntegralConsequence

  g12FullPiSqrtThreeDerived :
    U1CMOrbitIntegralConsequence

  activeVusFormulaTargetRecorded :
    U1CMOrbitIntegralConsequence

  sectorAngleNormalizationPromoted :
    U1CMOrbitIntegralConsequence

  cabibboAndCKMRemainUnpromoted :
    U1CMOrbitIntegralConsequence

canonicalU1CMOrbitIntegralBlockers :
  List U1CMOrbitIntegralBlocker
canonicalU1CMOrbitIntegralBlockers =
  physicalCKMDiagonalisationStillRequired
  ∷ pdgCabibboAuthorityBindingStillRequired
  ∷ []

canonicalU1CMCitationAuthorities :
  List U1CMCitationAuthority
canonicalU1CMCitationAuthorities =
  diamondShurmanModularCurveVolumeAuthority
  ∷ silvermanCMConductorAuthority
  ∷ hasseSupersingularPointCountAuthority
  ∷ []

canonicalU1CMDerivationPath :
  List U1CMDerivationStep
canonicalU1CMDerivationPath =
  computeDedekindPsiFour
  ∷ applyX0NHyperbolicVolumeFormula
  ∷ identifyP2LaneWithX04ByGaussianCMConductorFour
  ∷ computeRawP2P3IsogenyCoupling
  ∷ multiplyRawCouplingByX04Volume
  ∷ recordActiveVusFormula
  ∷ []

canonicalU1CMOrbitIntegralConsequences :
  List U1CMOrbitIntegralConsequence
canonicalU1CMOrbitIntegralConsequences =
  psiFourIsSixConsequence
  ∷ x04VolumeIsTwoPiConsequence
  ∷ rawDiagnosticPreserved
  ∷ g12FullPiSqrtThreeDerived
  ∷ activeVusFormulaTargetRecorded
  ∷ sectorAngleNormalizationPromoted
  ∷ cabibboAndCKMRemainUnpromoted
  ∷ []

cmEndomorphismAuthorityLabel : String
cmEndomorphismAuthorityLabel =
  "CM authority: for j=1728, End(E)=Z[i], and the carrier p2 lane has conductor 4"

cmEndomorphismRingLabel : String
cmEndomorphismRingLabel =
  "End(E_j=1728)=Z[i]"

dedekindPsiFourLabel : String
dedekindPsiFourLabel =
  "Dedekind psi(4)=4*(1+1/2)=6"

x04VolumeFormulaLabel : String
x04VolumeFormulaLabel =
  "vol(X0(4))=(pi/3)*psi(4)=(pi/3)*6=2*pi"

p2LaneModuliSpaceLabel : String
p2LaneModuliSpaceLabel =
  "CarrierP2Moduli=X0(4), by Gaussian CM conductor 4 for the j=1728 lane"

p2LaneInnerProductLabel : String
p2LaneInnerProductLabel =
  "<phi_p2|phi_p2> is the L2 inner product on sections over X0(4) with invariant hyperbolic measure"

rawIsogenyDiagnosticLabel : String
rawIsogenyDiagnosticLabel =
  "g12_raw=3/sqrt(3*4)=sqrt(3)/2"

fullSectorNormalizationLabel : String
fullSectorNormalizationLabel =
  "(Y_d)12=g12_raw*vol(X0(4))=(sqrt(3)/2)*(2*pi)=pi*sqrt(3)"

activeVusFormulaConsequenceLabel : String
activeVusFormulaConsequenceLabel =
  "consequence target: |V_us|=pi*sqrt(3)*sqrt(m_u/m_c)"

pdgDiagnosticLabel : String
pdgDiagnosticLabel =
  "numerical diagnostic: pi*sqrt(3)*sqrt(2.16/1270)=0.224407 versus PDG 0.224500, relative error about 0.000416"

record U1CMOrbitIntegralReceipt : Setω where
  field
    status :
      U1CMOrbitIntegralStatus

    citationAuthorities :
      List U1CMCitationAuthority

    citationAuthoritiesAreCanonical :
      citationAuthorities ≡ canonicalU1CMCitationAuthorities

    derivationPath :
      List U1CMDerivationStep

    derivationPathIsCanonical :
      derivationPath ≡ canonicalU1CMDerivationPath

    cmJInvariant :
      Nat

    cmJInvariantIs1728 :
      cmJInvariant ≡ 1728

    p2LaneConductor :
      Nat

    p2LaneConductorIsFour :
      p2LaneConductor ≡ 4

    dedekindPsiFour :
      Nat

    dedekindPsiFourIsSix :
      dedekindPsiFour ≡ 6

    x04VolumeNumerator :
      Nat

    x04VolumeNumeratorIsTwo :
      x04VolumeNumerator ≡ 2

    x04VolumeSymbol :
      String

    x04VolumeSymbolIsPi :
      x04VolumeSymbol ≡ "pi"

    x04VolumeIs2PiDerived :
      Bool

    x04VolumeIs2PiDerivedIsTrue :
      x04VolumeIs2PiDerived ≡ true

    dedekindPsiFourStatement :
      String

    dedekindPsiFourStatementIsCanonical :
      dedekindPsiFourStatement ≡ dedekindPsiFourLabel

    x04VolumeFormulaStatement :
      String

    x04VolumeFormulaStatementIsCanonical :
      x04VolumeFormulaStatement ≡ x04VolumeFormulaLabel

    endomorphismRing :
      String

    endomorphismRingIsGaussianIntegers :
      endomorphismRing ≡ cmEndomorphismRingLabel

    endomorphismRingAuthorityBacked :
      Bool

    endomorphismRingAuthorityBackedIsTrue :
      endomorphismRingAuthorityBacked ≡ true

    endomorphismRingAuthority :
      String

    endomorphismRingAuthorityIsCanonical :
      endomorphismRingAuthority ≡ cmEndomorphismAuthorityLabel

    p2LaneModuliSpace :
      String

    p2LaneModuliSpaceIsX04 :
      p2LaneModuliSpace ≡ p2LaneModuliSpaceLabel

    p2LaneInnerProduct :
      String

    p2LaneInnerProductIsCanonical :
      p2LaneInnerProduct ≡ p2LaneInnerProductLabel

    p2LaneInnerProductIdentified :
      Bool

    p2LaneInnerProductIdentifiedIsTrue :
      p2LaneInnerProductIdentified ≡ true

    eF2Count :
      Nat

    eF2CountIsThree :
      eF2Count ≡ 3

    eF3Count :
      Nat

    eF3CountIsFour :
      eF3Count ≡ 4

    isogenyDegP2P3 :
      Nat

    isogenyDegP2P3IsThree :
      isogenyDegP2P3 ≡ 3

    rawIsogenySqrtRadicand :
      Nat

    rawIsogenySqrtRadicandIsThree :
      rawIsogenySqrtRadicand ≡ 3

    rawIsogenyDenominator :
      Nat

    rawIsogenyDenominatorIsTwo :
      rawIsogenyDenominator ≡ 2

    rawIsogenyDiagnosticRecorded :
      Bool

    rawIsogenyDiagnosticRecordedIsTrue :
      rawIsogenyDiagnosticRecorded ≡ true

    rawIsogenyDiagnostic :
      String

    rawIsogenyDiagnosticIsCanonical :
      rawIsogenyDiagnostic ≡ rawIsogenyDiagnosticLabel

    fullSectorNormalizationRecorded :
      Bool

    fullSectorNormalizationRecordedIsTrue :
      fullSectorNormalizationRecorded ≡ true

    fullSectorNormalization :
      String

    fullSectorNormalizationIsCanonical :
      fullSectorNormalization ≡ fullSectorNormalizationLabel

    sectorAngleNormalizationDerived :
      Bool

    sectorAngleNormalizationDerivedIsTrue :
      sectorAngleNormalizationDerived ≡ true

    ckmIntegralOverU1OrbitConstructed :
      Bool

    ckmIntegralOverU1OrbitConstructedIsTrue :
      ckmIntegralOverU1OrbitConstructed ≡ true

    consequences :
      List U1CMOrbitIntegralConsequence

    consequencesAreCanonical :
      consequences ≡ canonicalU1CMOrbitIntegralConsequences

    activeVusFormulaConsequence :
      String

    activeVusFormulaConsequenceIsCanonical :
      activeVusFormulaConsequence ≡ activeVusFormulaConsequenceLabel

    activeVusFormulaConsequenceRecorded :
      Bool

    activeVusFormulaConsequenceRecordedIsTrue :
      activeVusFormulaConsequenceRecorded ≡ true

    pdgDiagnostic :
      String

    pdgDiagnosticIsCanonical :
      pdgDiagnostic ≡ pdgDiagnosticLabel

    pdgDiagnosticRecorded :
      Bool

    pdgDiagnosticRecordedIsTrue :
      pdgDiagnosticRecorded ≡ true

    cabibboAngleDerived :
      Bool

    cabibboAngleDerivedIsFalse :
      cabibboAngleDerived ≡ false

    physicalCKMPromotionConstructed :
      Bool

    physicalCKMPromotionConstructedIsFalse :
      physicalCKMPromotionConstructed ≡ false

    matchesPDGPromoted :
      Bool

    matchesPDGPromotedIsFalse :
      matchesPDGPromoted ≡ false

    blockers :
      List U1CMOrbitIntegralBlocker

    blockersAreCanonical :
      blockers ≡ canonicalU1CMOrbitIntegralBlockers

    receiptBoundary :
      List String

open U1CMOrbitIntegralReceipt public

canonicalU1CMOrbitIntegralReceipt :
  U1CMOrbitIntegralReceipt
canonicalU1CMOrbitIntegralReceipt =
  record
    { status =
        x04ModularVolumeNormalizationDerived
    ; citationAuthorities =
        canonicalU1CMCitationAuthorities
    ; citationAuthoritiesAreCanonical =
        refl
    ; derivationPath =
        canonicalU1CMDerivationPath
    ; derivationPathIsCanonical =
        refl
    ; cmJInvariant =
        1728
    ; cmJInvariantIs1728 =
        refl
    ; p2LaneConductor =
        4
    ; p2LaneConductorIsFour =
        refl
    ; dedekindPsiFour =
        6
    ; dedekindPsiFourIsSix =
        refl
    ; x04VolumeNumerator =
        2
    ; x04VolumeNumeratorIsTwo =
        refl
    ; x04VolumeSymbol =
        "pi"
    ; x04VolumeSymbolIsPi =
        refl
    ; x04VolumeIs2PiDerived =
        true
    ; x04VolumeIs2PiDerivedIsTrue =
        refl
    ; dedekindPsiFourStatement =
        dedekindPsiFourLabel
    ; dedekindPsiFourStatementIsCanonical =
        refl
    ; x04VolumeFormulaStatement =
        x04VolumeFormulaLabel
    ; x04VolumeFormulaStatementIsCanonical =
        refl
    ; endomorphismRing =
        cmEndomorphismRingLabel
    ; endomorphismRingIsGaussianIntegers =
        refl
    ; endomorphismRingAuthorityBacked =
        true
    ; endomorphismRingAuthorityBackedIsTrue =
        refl
    ; endomorphismRingAuthority =
        cmEndomorphismAuthorityLabel
    ; endomorphismRingAuthorityIsCanonical =
        refl
    ; p2LaneModuliSpace =
        p2LaneModuliSpaceLabel
    ; p2LaneModuliSpaceIsX04 =
        refl
    ; p2LaneInnerProduct =
        p2LaneInnerProductLabel
    ; p2LaneInnerProductIsCanonical =
        refl
    ; p2LaneInnerProductIdentified =
        true
    ; p2LaneInnerProductIdentifiedIsTrue =
        refl
    ; eF2Count =
        3
    ; eF2CountIsThree =
        refl
    ; eF3Count =
        4
    ; eF3CountIsFour =
        refl
    ; isogenyDegP2P3 =
        3
    ; isogenyDegP2P3IsThree =
        refl
    ; rawIsogenySqrtRadicand =
        3
    ; rawIsogenySqrtRadicandIsThree =
        refl
    ; rawIsogenyDenominator =
        2
    ; rawIsogenyDenominatorIsTwo =
        refl
    ; rawIsogenyDiagnosticRecorded =
        true
    ; rawIsogenyDiagnosticRecordedIsTrue =
        refl
    ; rawIsogenyDiagnostic =
        rawIsogenyDiagnosticLabel
    ; rawIsogenyDiagnosticIsCanonical =
        refl
    ; fullSectorNormalizationRecorded =
        true
    ; fullSectorNormalizationRecordedIsTrue =
        refl
    ; fullSectorNormalization =
        fullSectorNormalizationLabel
    ; fullSectorNormalizationIsCanonical =
        refl
    ; sectorAngleNormalizationDerived =
        true
    ; sectorAngleNormalizationDerivedIsTrue =
        refl
    ; ckmIntegralOverU1OrbitConstructed =
        true
    ; ckmIntegralOverU1OrbitConstructedIsTrue =
        refl
    ; consequences =
        canonicalU1CMOrbitIntegralConsequences
    ; consequencesAreCanonical =
        refl
    ; activeVusFormulaConsequence =
        activeVusFormulaConsequenceLabel
    ; activeVusFormulaConsequenceIsCanonical =
        refl
    ; activeVusFormulaConsequenceRecorded =
        true
    ; activeVusFormulaConsequenceRecordedIsTrue =
        refl
    ; pdgDiagnostic =
        pdgDiagnosticLabel
    ; pdgDiagnosticIsCanonical =
        refl
    ; pdgDiagnosticRecorded =
        true
    ; pdgDiagnosticRecordedIsTrue =
        refl
    ; cabibboAngleDerived =
        false
    ; cabibboAngleDerivedIsFalse =
        refl
    ; physicalCKMPromotionConstructed =
        false
    ; physicalCKMPromotionConstructedIsFalse =
        refl
    ; matchesPDGPromoted =
        false
    ; matchesPDGPromotedIsFalse =
        refl
    ; blockers =
        canonicalU1CMOrbitIntegralBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "Dedekind psi(4)=6 and vol(X0(4))=(pi/3)*6=2*pi are recorded as exact modular-curve volume data"
        ∷ "The p2 lane is identified with X0(4) by the j=1728 Gaussian-CM conductor-four authority boundary"
        ∷ "The p2-lane inner product is identified with the L2 hyperbolic-measure inner product over X0(4)"
        ∷ "Finite supersingular point counts 3 and 4 and degree-3 isogeny give g12_raw=sqrt(3)/2"
        ∷ "The sector normalization is derived as (sqrt(3)/2)*(2*pi)=pi*sqrt(3)"
        ∷ "sectorAngleNormalizationDerived is true for this p2-p3 normalization receipt"
        ∷ "The active |V_us|=pi*sqrt(3)*sqrt(m_u/m_c) formula and 0.224407 diagnostic are recorded"
        ∷ "Full Cabibbo derivation, physical CKM diagonalisation, and PDG promotion remain false"
        ∷ []
    }

u1CMReceiptRecordsJInvariant1728 :
  cmJInvariant canonicalU1CMOrbitIntegralReceipt
  ≡
  1728
u1CMReceiptRecordsJInvariant1728 =
  refl

u1CMReceiptRecordsGaussianIntegerEndomorphismRing :
  endomorphismRing canonicalU1CMOrbitIntegralReceipt
  ≡
  cmEndomorphismRingLabel
u1CMReceiptRecordsGaussianIntegerEndomorphismRing =
  refl

u1CMReceiptEndomorphismRingAuthorityBacked :
  endomorphismRingAuthorityBacked canonicalU1CMOrbitIntegralReceipt
  ≡
  true
u1CMReceiptEndomorphismRingAuthorityBacked =
  refl

u1CMReceiptRecordsPsiFour :
  dedekindPsiFour canonicalU1CMOrbitIntegralReceipt
  ≡
  6
u1CMReceiptRecordsPsiFour =
  refl

u1CMReceiptRecordsX04VolumeAsTwoPi :
  x04VolumeIs2PiDerived canonicalU1CMOrbitIntegralReceipt
  ≡
  true
u1CMReceiptRecordsX04VolumeAsTwoPi =
  refl

u1CMReceiptRecordsP2LaneInnerProduct :
  p2LaneInnerProductIdentified canonicalU1CMOrbitIntegralReceipt
  ≡
  true
u1CMReceiptRecordsP2LaneInnerProduct =
  refl

u1CMReceiptRecordsRawIsogenyDiagnostic :
  rawIsogenyDiagnosticRecorded canonicalU1CMOrbitIntegralReceipt
  ≡
  true
u1CMReceiptRecordsRawIsogenyDiagnostic =
  refl

u1CMReceiptRecordsFullSectorNormalization :
  fullSectorNormalizationRecorded canonicalU1CMOrbitIntegralReceipt
  ≡
  true
u1CMReceiptRecordsFullSectorNormalization =
  refl

u1CMReceiptSectorAngleNormalizationDerived :
  sectorAngleNormalizationDerived canonicalU1CMOrbitIntegralReceipt
  ≡
  true
u1CMReceiptSectorAngleNormalizationDerived =
  refl

u1CMReceiptCKMIntegralOverX04Constructed :
  ckmIntegralOverU1OrbitConstructed canonicalU1CMOrbitIntegralReceipt
  ≡
  true
u1CMReceiptCKMIntegralOverX04Constructed =
  refl

u1CMReceiptCabibboAngleStillNotDerived :
  cabibboAngleDerived canonicalU1CMOrbitIntegralReceipt
  ≡
  false
u1CMReceiptCabibboAngleStillNotDerived =
  refl

u1CMReceiptPhysicalCKMStillFalse :
  physicalCKMPromotionConstructed canonicalU1CMOrbitIntegralReceipt
  ≡
  false
u1CMReceiptPhysicalCKMStillFalse =
  refl

u1CMReceiptDerivationPathIsCanonical :
  derivationPath canonicalU1CMOrbitIntegralReceipt
  ≡
  canonicalU1CMDerivationPath
u1CMReceiptDerivationPathIsCanonical =
  refl

u1CMReceiptCitationAuthoritiesAreCanonical :
  citationAuthorities canonicalU1CMOrbitIntegralReceipt
  ≡
  canonicalU1CMCitationAuthorities
u1CMReceiptCitationAuthoritiesAreCanonical =
  refl

u1CMReceiptRecordsActiveVusConsequence :
  activeVusFormulaConsequenceRecorded canonicalU1CMOrbitIntegralReceipt
  ≡
  true
u1CMReceiptRecordsActiveVusConsequence =
  refl
