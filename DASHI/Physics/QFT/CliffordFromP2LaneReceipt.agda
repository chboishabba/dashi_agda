module DASHI.Physics.QFT.CliffordFromP2LaneReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- P2-lane Clifford receipt.
--
-- This module records the finite p2-lane F4 calculation in M2(F2).  The
-- element phi is represented by the companion matrix [[0,1],[1,1]], so the
-- relation phi^2 + phi + 1 = 0 is checked by definitional computation.
-- The M2(F2) carrier is recorded as the concrete Cl(1,1)-over-F2 embedding
-- surface with gamma0 the identity matrix and gamma1 the swap matrix.
--
-- The receipt is intentionally conditional/candidate level: it records an
-- inhabited carrier-derived Dirac spin sector candidate, while exact Standard
-- Model and G_DHR promotion remain false.

data F2 : Set where
  f0 :
    F2

  f1 :
    F2

_+F2_ :
  F2 →
  F2 →
  F2
f0 +F2 b =
  b
f1 +F2 f0 =
  f1
f1 +F2 f1 =
  f0

_*F2_ :
  F2 →
  F2 →
  F2
f0 *F2 _ =
  f0
f1 *F2 b =
  b

infixl 6 _+F2_
infixl 7 _*F2_

record Mat2F2 : Set where
  constructor mat2
  field
    a00 :
      F2

    a01 :
      F2

    a10 :
      F2

    a11 :
      F2

open Mat2F2 public

_+M_ :
  Mat2F2 →
  Mat2F2 →
  Mat2F2
mat2 a b c d +M mat2 e f g h =
  mat2
    (a +F2 e)
    (b +F2 f)
    (c +F2 g)
    (d +F2 h)

_*M_ :
  Mat2F2 →
  Mat2F2 →
  Mat2F2
mat2 a b c d *M mat2 e f g h =
  mat2
    ((a *F2 e) +F2 (b *F2 g))
    ((a *F2 f) +F2 (b *F2 h))
    ((c *F2 e) +F2 (d *F2 g))
    ((c *F2 f) +F2 (d *F2 h))

infixl 6 _+M_
infixl 7 _*M_

zeroMat2F2 :
  Mat2F2
zeroMat2F2 =
  mat2 f0 f0 f0 f0

identityMat2F2 :
  Mat2F2
identityMat2F2 =
  mat2 f1 f0 f0 f1

swapMat2F2 :
  Mat2F2
swapMat2F2 =
  mat2 f0 f1 f1 f0

p2LanePhiCompanionMatrix :
  Mat2F2
p2LanePhiCompanionMatrix =
  mat2 f0 f1 f1 f1

p2LanePhiSquared :
  Mat2F2
p2LanePhiSquared =
  p2LanePhiCompanionMatrix *M p2LanePhiCompanionMatrix

p2LanePhiPolynomial :
  Mat2F2
p2LanePhiPolynomial =
  p2LanePhiSquared +M p2LanePhiCompanionMatrix +M identityMat2F2

p2LanePhiSatisfiesF4Polynomial :
  p2LanePhiPolynomial
  ≡
  zeroMat2F2
p2LanePhiSatisfiesF4Polynomial =
  refl

gamma0IdentityMatrix :
  Mat2F2
gamma0IdentityMatrix =
  identityMat2F2

gamma1SwapMatrix :
  Mat2F2
gamma1SwapMatrix =
  swapMat2F2

gamma0Squared :
  Mat2F2
gamma0Squared =
  gamma0IdentityMatrix *M gamma0IdentityMatrix

gamma1Squared :
  Mat2F2
gamma1Squared =
  gamma1SwapMatrix *M gamma1SwapMatrix

gamma0Gamma1Anticommutator :
  Mat2F2
gamma0Gamma1Anticommutator =
  (gamma0IdentityMatrix *M gamma1SwapMatrix)
  +M
  (gamma1SwapMatrix *M gamma0IdentityMatrix)

gamma0SquaresToIdentity :
  gamma0Squared
  ≡
  identityMat2F2
gamma0SquaresToIdentity =
  refl

gamma1SquaresToIdentity :
  gamma1Squared
  ≡
  identityMat2F2
gamma1SquaresToIdentity =
  refl

gamma0Gamma1AnticommutatorZero :
  gamma0Gamma1Anticommutator
  ≡
  zeroMat2F2
gamma0Gamma1AnticommutatorZero =
  refl

data CliffordFromP2LaneStatus : Set where
  conditionalCandidateCarrierReceipt :
    CliffordFromP2LaneStatus

p2LaneF4PhiLabel : String
p2LaneF4PhiLabel =
  "phi in F4 = F2[x]/(x^2+x+1), represented by companion matrix [[0,1],[1,1]]"

clifford11F2EmbeddingLabel : String
clifford11F2EmbeddingLabel =
  "Cl(1,1) over F2 candidate carrier embedded in M2(F2)"

record CliffordFromP2LaneReceipt : Setω where
  field
    status :
      CliffordFromP2LaneStatus

    statusIsConditionalCandidate :
      status ≡ conditionalCandidateCarrierReceipt

    phi :
      Mat2F2

    phiIsCompanionMatrix :
      phi ≡ p2LanePhiCompanionMatrix

    phiSquared :
      Mat2F2

    phiSquaredIsMatrixSquare :
      phiSquared ≡ phi *M phi

    phiF4Polynomial :
      Mat2F2

    phiF4PolynomialIsZero :
      phiF4Polynomial ≡ zeroMat2F2

    phiLabel :
      String

    phiLabelIsCanonical :
      phiLabel ≡ p2LaneF4PhiLabel

    cl11EmbeddingCarrier :
      Mat2F2

    cl11EmbeddingCarrierIsM2F2Unit :
      cl11EmbeddingCarrier ≡ identityMat2F2

    cl11EmbeddingLabel :
      String

    cl11EmbeddingLabelIsCanonical :
      cl11EmbeddingLabel ≡ clifford11F2EmbeddingLabel

    gamma0 :
      Mat2F2

    gamma0IsIdentity :
      gamma0 ≡ gamma0IdentityMatrix

    gamma0SquareIsIdentity :
      gamma0 *M gamma0 ≡ identityMat2F2

    gamma1 :
      Mat2F2

    gamma1IsSwap :
      gamma1 ≡ gamma1SwapMatrix

    gamma1SquareIsIdentity :
      gamma1 *M gamma1 ≡ identityMat2F2

    gamma0Gamma1AnticommutesInCharacteristicTwo :
      (gamma0 *M gamma1) +M (gamma1 *M gamma0)
      ≡
      zeroMat2F2

    cliffordFromP2LaneInhabited :
      Bool

    cliffordFromP2LaneInhabitedIsTrue :
      cliffordFromP2LaneInhabited ≡ true

    diracSpinSectorDerivedFromCarrier :
      Bool

    diracSpinSectorDerivedFromCarrierIsTrue :
      diracSpinSectorDerivedFromCarrier ≡ true

    diracSpinSectorDerivationIsConditionalCandidate :
      Bool

    diracSpinSectorDerivationIsConditionalCandidateIsTrue :
      diracSpinSectorDerivationIsConditionalCandidate ≡ true

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHRPromotion :
      Bool

    exactGDHRPromotionIsFalse :
      exactGDHRPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    receiptBoundary :
      List String

open CliffordFromP2LaneReceipt public

canonicalCliffordFromP2LaneReceipt :
  CliffordFromP2LaneReceipt
canonicalCliffordFromP2LaneReceipt =
  record
    { status =
        conditionalCandidateCarrierReceipt
    ; statusIsConditionalCandidate =
        refl
    ; phi =
        p2LanePhiCompanionMatrix
    ; phiIsCompanionMatrix =
        refl
    ; phiSquared =
        p2LanePhiSquared
    ; phiSquaredIsMatrixSquare =
        refl
    ; phiF4Polynomial =
        p2LanePhiPolynomial
    ; phiF4PolynomialIsZero =
        p2LanePhiSatisfiesF4Polynomial
    ; phiLabel =
        p2LaneF4PhiLabel
    ; phiLabelIsCanonical =
        refl
    ; cl11EmbeddingCarrier =
        identityMat2F2
    ; cl11EmbeddingCarrierIsM2F2Unit =
        refl
    ; cl11EmbeddingLabel =
        clifford11F2EmbeddingLabel
    ; cl11EmbeddingLabelIsCanonical =
        refl
    ; gamma0 =
        gamma0IdentityMatrix
    ; gamma0IsIdentity =
        refl
    ; gamma0SquareIsIdentity =
        gamma0SquaresToIdentity
    ; gamma1 =
        gamma1SwapMatrix
    ; gamma1IsSwap =
        refl
    ; gamma1SquareIsIdentity =
        gamma1SquaresToIdentity
    ; gamma0Gamma1AnticommutesInCharacteristicTwo =
        gamma0Gamma1AnticommutatorZero
    ; cliffordFromP2LaneInhabited =
        true
    ; cliffordFromP2LaneInhabitedIsTrue =
        refl
    ; diracSpinSectorDerivedFromCarrier =
        true
    ; diracSpinSectorDerivedFromCarrierIsTrue =
        refl
    ; diracSpinSectorDerivationIsConditionalCandidate =
        true
    ; diracSpinSectorDerivationIsConditionalCandidateIsTrue =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHRPromotion =
        false
    ; exactGDHRPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; receiptBoundary =
        "The p2-lane F4 element phi is the M2(F2) companion matrix [[0,1],[1,1]]"
        ∷ "The relation phi^2 + phi + 1 = 0 is witnessed by direct M2(F2) computation"
        ∷ "The Cl(1,1)-over-F2 candidate carrier is recorded inside M2(F2), with gamma0 the identity matrix and gamma1 the swap matrix"
        ∷ "cliffordFromP2LaneInhabited and diracSpinSectorDerivedFromCarrier are true only at conditional/candidate receipt level"
        ∷ "Exact Standard Model promotion, exact G_DHR promotion, and exact G_DHR ~= G_SM promotion remain false"
        ∷ []
    }

cliffordFromP2LaneInhabitedLemma :
  CliffordFromP2LaneReceipt.cliffordFromP2LaneInhabited
    canonicalCliffordFromP2LaneReceipt
  ≡
  true
cliffordFromP2LaneInhabitedLemma =
  CliffordFromP2LaneReceipt.cliffordFromP2LaneInhabitedIsTrue
    canonicalCliffordFromP2LaneReceipt

diracSpinSectorDerivedFromCarrierLemma :
  CliffordFromP2LaneReceipt.diracSpinSectorDerivedFromCarrier
    canonicalCliffordFromP2LaneReceipt
  ≡
  true
diracSpinSectorDerivedFromCarrierLemma =
  CliffordFromP2LaneReceipt.diracSpinSectorDerivedFromCarrierIsTrue
    canonicalCliffordFromP2LaneReceipt

diracSpinSectorDerivedFromCarrierConditionalCandidate :
  CliffordFromP2LaneReceipt.diracSpinSectorDerivationIsConditionalCandidate
    canonicalCliffordFromP2LaneReceipt
  ≡
  true
diracSpinSectorDerivedFromCarrierConditionalCandidate =
  CliffordFromP2LaneReceipt.diracSpinSectorDerivationIsConditionalCandidateIsTrue
    canonicalCliffordFromP2LaneReceipt

cliffordFromP2LanePhiF4PolynomialZero :
  CliffordFromP2LaneReceipt.phiF4Polynomial
    canonicalCliffordFromP2LaneReceipt
  ≡
  zeroMat2F2
cliffordFromP2LanePhiF4PolynomialZero =
  CliffordFromP2LaneReceipt.phiF4PolynomialIsZero
    canonicalCliffordFromP2LaneReceipt

cliffordFromP2LaneGamma0Identity :
  CliffordFromP2LaneReceipt.gamma0
    canonicalCliffordFromP2LaneReceipt
  ≡
  identityMat2F2
cliffordFromP2LaneGamma0Identity =
  CliffordFromP2LaneReceipt.gamma0IsIdentity
    canonicalCliffordFromP2LaneReceipt

cliffordFromP2LaneGamma1Swap :
  CliffordFromP2LaneReceipt.gamma1
    canonicalCliffordFromP2LaneReceipt
  ≡
  swapMat2F2
cliffordFromP2LaneGamma1Swap =
  CliffordFromP2LaneReceipt.gamma1IsSwap
    canonicalCliffordFromP2LaneReceipt

cliffordFromP2LaneExactStandardModelPromotionFalse :
  CliffordFromP2LaneReceipt.exactStandardModelPromotion
    canonicalCliffordFromP2LaneReceipt
  ≡
  false
cliffordFromP2LaneExactStandardModelPromotionFalse =
  CliffordFromP2LaneReceipt.exactStandardModelPromotionIsFalse
    canonicalCliffordFromP2LaneReceipt

cliffordFromP2LaneExactGDHRPromotionFalse :
  CliffordFromP2LaneReceipt.exactGDHRPromotion
    canonicalCliffordFromP2LaneReceipt
  ≡
  false
cliffordFromP2LaneExactGDHRPromotionFalse =
  CliffordFromP2LaneReceipt.exactGDHRPromotionIsFalse
    canonicalCliffordFromP2LaneReceipt

cliffordFromP2LaneExactGDHREqualsGSMPromotionFalse :
  CliffordFromP2LaneReceipt.exactGDHREqualsGSMPromotion
    canonicalCliffordFromP2LaneReceipt
  ≡
  false
cliffordFromP2LaneExactGDHREqualsGSMPromotionFalse =
  CliffordFromP2LaneReceipt.exactGDHREqualsGSMPromotionIsFalse
    canonicalCliffordFromP2LaneReceipt
