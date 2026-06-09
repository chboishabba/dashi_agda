module DASHI.Physics.Closure.NSSignAntisymmetryExactIdentityBoundary where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS sign-antisymmetry exact identity boundary.
--
-- This is a finite algebra receipt for the repaired propagated-polarization
-- NS route.  It records the exact sign-cancellation identity
--
--   (a dot omega(c)) + (b dot omega(c)) = 0
--
-- under the finite resonance/normalization premises
--
--   c = normalize(a + b)
--   omega(c) perpendicular c.
--
-- The intended algebra is:
--
--   c parallel (a + b)
--   omega(c) perpendicular c
--   therefore (a + b) dot omega(c) = 0
--   therefore (a dot omega(c)) + (b dot omega(c)) = 0.
--
-- This module is deliberately lightweight and fail-closed.  It records the
-- finite algebra surface and governance flags only.  It does not prove the
-- propagated-polarization output-width theorem, the compensated leakage
-- identity, local defect monotonicity, CKN/BKM closure, or Clay NS.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Abstract finite algebra carriers.

postulate
  Scalar :
    Set
  Vector3 :
    Set

  zeroScalar :
    Scalar

  _+s_ :
    Scalar →
    Scalar →
    Scalar

  _+v_ :
    Vector3 →
    Vector3 →
    Vector3

  dot :
    Vector3 →
    Vector3 →
    Scalar

  normalize :
    Vector3 →
    Vector3

  omegaAt :
    Vector3 →
    Vector3

infixl 6 _+s_
infixl 6 _+v_

data OutputNormalizationPremise : Vector3 → Vector3 → Vector3 → Set where
  outputIsNormalizedInputSum :
    (a b : Vector3) →
    OutputNormalizationPremise a b (normalize (a +v b))

data OutputVorticityOrthogonalityPremise : Vector3 → Set where
  outputVorticityPerpendicularToOutput :
    (c : Vector3) →
    dot c (omegaAt c) ≡ zeroScalar →
    OutputVorticityOrthogonalityPremise c

data DotAdditivityPremise : Vector3 → Vector3 → Vector3 → Set where
  dotDistributesAcrossInputSum :
    (a b w : Vector3) →
    dot (a +v b) w ≡ (dot a w +s dot b w) →
    DotAdditivityPremise a b w

data NormalizedParallelOrthogonalityPremise : Vector3 → Vector3 → Vector3 → Set where
  normalizedOutputOrthogonalityPullsBackToInputSum :
    (a b c : Vector3) →
    OutputNormalizationPremise a b c →
    OutputVorticityOrthogonalityPremise c →
    dot (a +v b) (omegaAt c) ≡ zeroScalar →
    NormalizedParallelOrthogonalityPremise a b c

data SignAntisymmetryExactIdentity : Vector3 → Vector3 → Vector3 → Set where
  signAntisymmetryFromNormalizedOutputOrthogonality :
    (a b c : Vector3) →
    OutputNormalizationPremise a b c →
    OutputVorticityOrthogonalityPremise c →
    DotAdditivityPremise a b (omegaAt c) →
    NormalizedParallelOrthogonalityPremise a b c →
    (dot a (omegaAt c) +s dot b (omegaAt c)) ≡ zeroScalar →
    SignAntisymmetryExactIdentity a b c

------------------------------------------------------------------------
-- Receipt records.

record NSSignAntisymmetryExactIdentityReceipt : Set where
  constructor nsSignAntisymmetryExactIdentityReceipt
  field
    inputFrequencyA :
      Vector3
    inputFrequencyB :
      Vector3
    outputFrequencyC :
      Vector3
    outputNormalization :
      OutputNormalizationPremise inputFrequencyA inputFrequencyB outputFrequencyC
    outputVorticityOrthogonality :
      OutputVorticityOrthogonalityPremise outputFrequencyC
    dotAdditivity :
      DotAdditivityPremise inputFrequencyA inputFrequencyB (omegaAt outputFrequencyC)
    normalizedOrthogonalityPullback :
      NormalizedParallelOrthogonalityPremise inputFrequencyA inputFrequencyB outputFrequencyC
    exactSignAntisymmetryIdentity :
      SignAntisymmetryExactIdentity inputFrequencyA inputFrequencyB outputFrequencyC

data ExactIdentityDependency : Set where
  finiteTriadicResonance :
    ExactIdentityDependency
  nonzeroOutputNormalizableInputSum :
    ExactIdentityDependency
  outputVorticityOrthogonalToOutputDirection :
    ExactIdentityDependency
  dotProductAdditivityOverInputSum :
    ExactIdentityDependency
  normalizedParallelOrthogonalityPullback :
    ExactIdentityDependency

canonicalExactIdentityDependencies :
  List ExactIdentityDependency
canonicalExactIdentityDependencies =
  finiteTriadicResonance
  ∷ nonzeroOutputNormalizableInputSum
  ∷ outputVorticityOrthogonalToOutputDirection
  ∷ dotProductAdditivityOverInputSum
  ∷ normalizedParallelOrthogonalityPullback
  ∷ []

exactIdentityDependencyCount : Nat
exactIdentityDependencyCount =
  listLength canonicalExactIdentityDependencies

exactIdentityDependencyCountIs5 :
  exactIdentityDependencyCount ≡ 5
exactIdentityDependencyCountIs5 =
  refl

data ExactIdentityRole : Set where
  supportsPropagatedPolarizationCoherenceHarness :
    ExactIdentityRole
  recordsFiniteSignCancellationOnly :
    ExactIdentityRole
  doesNotProveCascadeClosedOutputWidth :
    ExactIdentityRole
  doesNotProveTriadicCompensatedLeakage :
    ExactIdentityRole
  doesNotPromoteClayNavierStokes :
    ExactIdentityRole

canonicalExactIdentityRoles :
  List ExactIdentityRole
canonicalExactIdentityRoles =
  supportsPropagatedPolarizationCoherenceHarness
  ∷ recordsFiniteSignCancellationOnly
  ∷ doesNotProveCascadeClosedOutputWidth
  ∷ doesNotProveTriadicCompensatedLeakage
  ∷ doesNotPromoteClayNavierStokes
  ∷ []

exactIdentityRoleCount : Nat
exactIdentityRoleCount =
  listLength canonicalExactIdentityRoles

exactIdentityRoleCountIs5 :
  exactIdentityRoleCount ≡ 5
exactIdentityRoleCountIs5 =
  refl

data PromotionGate : Set where
  finiteAlgebraReceiptOnly :
    PromotionGate
  analyticTransferStillMissing :
    PromotionGate
  microlocalMeasureTransferStillMissing :
    PromotionGate
  localDefectMonotonicityStillMissing :
    PromotionGate
  clayPromotionBlocked :
    PromotionGate

canonicalPromotionGates :
  List PromotionGate
canonicalPromotionGates =
  finiteAlgebraReceiptOnly
  ∷ analyticTransferStillMissing
  ∷ microlocalMeasureTransferStillMissing
  ∷ localDefectMonotonicityStillMissing
  ∷ clayPromotionBlocked
  ∷ []

promotionGateCount : Nat
promotionGateCount =
  listLength canonicalPromotionGates

promotionGateCountIs5 :
  promotionGateCount ≡ 5
promotionGateCountIs5 =
  refl

------------------------------------------------------------------------
-- Canonical symbolic receipt.

postulate
  canonicalInputFrequencyA :
    Vector3
  canonicalInputFrequencyB :
    Vector3

canonicalOutputFrequencyC :
  Vector3
canonicalOutputFrequencyC =
  normalize (canonicalInputFrequencyA +v canonicalInputFrequencyB)

canonicalOutputNormalization :
  OutputNormalizationPremise
    canonicalInputFrequencyA
    canonicalInputFrequencyB
    canonicalOutputFrequencyC
canonicalOutputNormalization =
  outputIsNormalizedInputSum canonicalInputFrequencyA canonicalInputFrequencyB

postulate
  canonicalOutputOrthogonalityProof :
    dot canonicalOutputFrequencyC (omegaAt canonicalOutputFrequencyC) ≡ zeroScalar

canonicalOutputVorticityOrthogonality :
  OutputVorticityOrthogonalityPremise canonicalOutputFrequencyC
canonicalOutputVorticityOrthogonality =
  outputVorticityPerpendicularToOutput
    canonicalOutputFrequencyC
    canonicalOutputOrthogonalityProof

postulate
  canonicalDotAdditivityProof :
    dot
      (canonicalInputFrequencyA +v canonicalInputFrequencyB)
      (omegaAt canonicalOutputFrequencyC)
      ≡
      (dot canonicalInputFrequencyA (omegaAt canonicalOutputFrequencyC)
        +s dot canonicalInputFrequencyB (omegaAt canonicalOutputFrequencyC))

canonicalDotAdditivity :
  DotAdditivityPremise
    canonicalInputFrequencyA
    canonicalInputFrequencyB
    (omegaAt canonicalOutputFrequencyC)
canonicalDotAdditivity =
  dotDistributesAcrossInputSum
    canonicalInputFrequencyA
    canonicalInputFrequencyB
    (omegaAt canonicalOutputFrequencyC)
    canonicalDotAdditivityProof

postulate
  canonicalNormalizedOrthogonalityPullbackProof :
    dot
      (canonicalInputFrequencyA +v canonicalInputFrequencyB)
      (omegaAt canonicalOutputFrequencyC)
      ≡
      zeroScalar

canonicalNormalizedOrthogonalityPullback :
  NormalizedParallelOrthogonalityPremise
    canonicalInputFrequencyA
    canonicalInputFrequencyB
    canonicalOutputFrequencyC
canonicalNormalizedOrthogonalityPullback =
  normalizedOutputOrthogonalityPullsBackToInputSum
    canonicalInputFrequencyA
    canonicalInputFrequencyB
    canonicalOutputFrequencyC
    canonicalOutputNormalization
    canonicalOutputVorticityOrthogonality
    canonicalNormalizedOrthogonalityPullbackProof

postulate
  canonicalSignAntisymmetryProof :
    (dot canonicalInputFrequencyA (omegaAt canonicalOutputFrequencyC)
      +s dot canonicalInputFrequencyB (omegaAt canonicalOutputFrequencyC))
      ≡
      zeroScalar

canonicalSignAntisymmetryExactIdentity :
  SignAntisymmetryExactIdentity
    canonicalInputFrequencyA
    canonicalInputFrequencyB
    canonicalOutputFrequencyC
canonicalSignAntisymmetryExactIdentity =
  signAntisymmetryFromNormalizedOutputOrthogonality
    canonicalInputFrequencyA
    canonicalInputFrequencyB
    canonicalOutputFrequencyC
    canonicalOutputNormalization
    canonicalOutputVorticityOrthogonality
    canonicalDotAdditivity
    canonicalNormalizedOrthogonalityPullback
    canonicalSignAntisymmetryProof

canonicalNSSignAntisymmetryExactIdentityReceipt :
  NSSignAntisymmetryExactIdentityReceipt
canonicalNSSignAntisymmetryExactIdentityReceipt =
  nsSignAntisymmetryExactIdentityReceipt
    canonicalInputFrequencyA
    canonicalInputFrequencyB
    canonicalOutputFrequencyC
    canonicalOutputNormalization
    canonicalOutputVorticityOrthogonality
    canonicalDotAdditivity
    canonicalNormalizedOrthogonalityPullback
    canonicalSignAntisymmetryExactIdentity

------------------------------------------------------------------------
-- Governance flags.

clayNavierStokesPromoted :
  Bool
clayNavierStokesPromoted =
  false

triadicCompensatedLeakageIdentityProved :
  Bool
triadicCompensatedLeakageIdentityProved =
  false

cascadeClosedZeroModeOutputWidthProved :
  Bool
cascadeClosedZeroModeOutputWidthProved =
  false

fullLocalDefectMonotonicityProved :
  Bool
fullLocalDefectMonotonicityProved =
  false

receiptSummary :
  String
receiptSummary =
  "Records finite identity (a dot omega(c)) + (b dot omega(c)) = 0 from c = normalize(a + b) and omega(c) perpendicular c; Clay promotion false."
