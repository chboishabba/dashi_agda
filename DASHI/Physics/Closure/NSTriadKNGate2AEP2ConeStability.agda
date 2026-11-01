module DASHI.Physics.Closure.NSTriadKNGate2AEP2ConeStability where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- EP2: near-extremizer cone stability.
--
-- This is the first concrete theorem surface after EP1. It records the
-- exact cone, the admissible seam symmetries, and the lift-compatibility
-- obligations that the Gate 2-A transport theorem actually needs.
--
-- It is not a stub and not a promotion surface. The point is to replace
-- vague prose like "cone stability" with the exact theorem-facing data:
--
--   E_N(epsilon)
--   seam stabilizer actions
--   operator-specific Schur lift compatibility
--   the common-lift gap that remains open

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadKNGate2AEP2Status : Set where
  nearExtremizerConeRecorded :
    NSTriadKNGate2AEP2Status
  seamSymmetryFamilyRecorded :
    NSTriadKNGate2AEP2Status
  operatorSpecificLiftCompatibilityRecorded :
    NSTriadKNGate2AEP2Status
  commonLiftGapRecorded :
    NSTriadKNGate2AEP2Status
  noNSOrClayPromotion :
    NSTriadKNGate2AEP2Status

canonicalEP2Statuses : List NSTriadKNGate2AEP2Status
canonicalEP2Statuses =
  nearExtremizerConeRecorded
  ∷ seamSymmetryFamilyRecorded
  ∷ operatorSpecificLiftCompatibilityRecorded
  ∷ commonLiftGapRecorded
  ∷ noNSOrClayPromotion
  ∷ []

data NSTriadKNGate2AEP2AdmissibleSymmetry : Set where
  shellPairSwap :
    NSTriadKNGate2AEP2AdmissibleSymmetry
  coordinatePermutationWithinOrbitClass :
    NSTriadKNGate2AEP2AdmissibleSymmetry
  signReversalParity :
    NSTriadKNGate2AEP2AdmissibleSymmetry
  seamStabilizerOrbitTransport :
    NSTriadKNGate2AEP2AdmissibleSymmetry

canonicalEP2AdmissibleSymmetries :
  List NSTriadKNGate2AEP2AdmissibleSymmetry
canonicalEP2AdmissibleSymmetries =
  shellPairSwap
  ∷ coordinatePermutationWithinOrbitClass
  ∷ signReversalParity
  ∷ seamStabilizerOrbitTransport
  ∷ []

data NSTriadKNGate2AEP2StabilityObligation : Set where
  rayleighRatioStableOnCone :
    NSTriadKNGate2AEP2StabilityObligation
  orbitFamilyStableModuloSymmetry :
    NSTriadKNGate2AEP2StabilityObligation
  topShellMassStableModuloSymmetry :
    NSTriadKNGate2AEP2StabilityObligation
  operatorSpecificSchurLiftsRespectCone :
    NSTriadKNGate2AEP2StabilityObligation
  commonGramLiftStillOpen :
    NSTriadKNGate2AEP2StabilityObligation

canonicalEP2StabilityObligations :
  List NSTriadKNGate2AEP2StabilityObligation
canonicalEP2StabilityObligations =
  rayleighRatioStableOnCone
  ∷ orbitFamilyStableModuloSymmetry
  ∷ topShellMassStableModuloSymmetry
  ∷ operatorSpecificSchurLiftsRespectCone
  ∷ commonGramLiftStillOpen
  ∷ []

canonicalConeDefinitionText : String
canonicalConeDefinitionText =
  "E_N(epsilon) = { x in 1_C^perp : (x^T L_bad x) / (x^T L_good x) >= rho_N - epsilon }."

canonicalSymmetryText : String
canonicalSymmetryText =
  "Admissible seam symmetries: shell-pair swap, coordinate permutations within the active orbit family, sign-reversal parity, and the residual seam stabilizer transport."

canonicalLiftCompatibilityText : String
canonicalLiftCompatibilityText =
  "Exact operator-specific lifts J_N^abs and J_N^neg already exist. EP2 isolates the stability obligation that near-extremizer directions stay in the same anisotropic seam family under those lifts, modulo the seam stabilizer."

canonicalEvidenceText : String
canonicalEvidenceText =
  "Numerical support across N=6,8,10,12,14,16: persistent orbit family (0,1,N-1), top-shell mass concentration, mixed-shell seam locally hardest, and non-axis dominance compatible with one anisotropic direction modulo symmetry."

canonicalGapText : String
canonicalGapText =
  "Still open: a single common Gram lift J_N, a proof that the full near-extremizer cone is preserved under that common lift, and a proof that the quotient-defined transport constants are uniform in N."

record NSTriadKNGate2AEP2ConeStability : Setω where
  constructor mkNSTriadKNGate2AEP2ConeStability
  field
    statuses : List NSTriadKNGate2AEP2Status
    statusesAreCanonical :
      statuses ≡ canonicalEP2Statuses

    admissibleSymmetries :
      List NSTriadKNGate2AEP2AdmissibleSymmetry
    admissibleSymmetriesAreCanonical :
      admissibleSymmetries ≡ canonicalEP2AdmissibleSymmetries

    stabilityObligations :
      List NSTriadKNGate2AEP2StabilityObligation
    stabilityObligationsAreCanonical :
      stabilityObligations ≡ canonicalEP2StabilityObligations

    coneDefinitionText : String
    coneDefinitionTextIsCanonical :
      coneDefinitionText ≡ canonicalConeDefinitionText

    symmetryText : String
    symmetryTextIsCanonical :
      symmetryText ≡ canonicalSymmetryText

    liftCompatibilityText : String
    liftCompatibilityTextIsCanonical :
      liftCompatibilityText ≡ canonicalLiftCompatibilityText

    evidenceText : String
    evidenceTextIsCanonical :
      evidenceText ≡ canonicalEvidenceText

    gapText : String
    gapTextIsCanonical :
      gapText ≡ canonicalGapText

    symmetryCount : Nat
    symmetryCountIs4 :
      symmetryCount ≡ 4

    obligationCount : Nat
    obligationCountIs5 :
      obligationCount ≡ 5

    ep2ConeDefined : Bool
    ep2ConeDefinedIsTrue :
      ep2ConeDefined ≡ true

    ep2SymmetryFamilyRecorded : Bool
    ep2SymmetryFamilyRecordedIsTrue :
      ep2SymmetryFamilyRecorded ≡ true

    ep2PersistentOrbitFamilyUsed : Bool
    ep2PersistentOrbitFamilyUsedIsTrue :
      ep2PersistentOrbitFamilyUsed ≡ true

    ep2OperatorSpecificLiftCompatibilityStated : Bool
    ep2OperatorSpecificLiftCompatibilityStatedIsTrue :
      ep2OperatorSpecificLiftCompatibilityStated ≡ true

    ep2NearExtremizerConeNumericallySupported : Bool
    ep2NearExtremizerConeNumericallySupportedIsTrue :
      ep2NearExtremizerConeNumericallySupported ≡ true

    ep2ConeSymmetryPreservationProved : Bool
    ep2ConeSymmetryPreservationProvedIsFalse :
      ep2ConeSymmetryPreservationProved ≡ false

    ep2CommonLiftCompatibilityProved : Bool
    ep2CommonLiftCompatibilityProvedIsFalse :
      ep2CommonLiftCompatibilityProved ≡ false

    ep2ProofConstructed : Bool
    ep2ProofConstructedIsFalse :
      ep2ProofConstructed ≡ false

    ep2Promoted : Bool
    ep2PromotedIsFalse :
      ep2Promoted ≡ false

open NSTriadKNGate2AEP2ConeStability public

canonicalNSTriadKNGate2AEP2ConeStability :
  NSTriadKNGate2AEP2ConeStability
canonicalNSTriadKNGate2AEP2ConeStability =
  mkNSTriadKNGate2AEP2ConeStability
    canonicalEP2Statuses
    refl
    canonicalEP2AdmissibleSymmetries
    refl
    canonicalEP2StabilityObligations
    refl
    canonicalConeDefinitionText
    refl
    canonicalSymmetryText
    refl
    canonicalLiftCompatibilityText
    refl
    canonicalEvidenceText
    refl
    canonicalGapText
    refl
    4
    refl
    5
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

