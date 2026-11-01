module DASHI.Physics.Closure.NSTriadKNGate2AExtremizerAwareTransportTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import DASHI.Physics.Closure.NSTriadKNGate2AEP1ExtremizerClassification
  using (NSTriadKNGate2AEP1ExtremizerClassification;
         canonicalNSTriadKNGate2AEP1ExtremizerClassification)
open import DASHI.Physics.Closure.NSTriadKNGate2AEP2ConeStability
  using (NSTriadKNGate2AEP2ConeStability;
         canonicalNSTriadKNGate2AEP2ConeStability)
open import DASHI.Physics.Closure.NSTriadKNGate2AEP3DirectionalTransportBudget
  using (NSTriadKNGate2AEP3DirectionalTransportBudget;
         canonicalNSTriadKNGate2AEP3DirectionalTransportBudget)
open import DASHI.Physics.Closure.NSTriadKNGate2AEP4MarginClosing
  using (NSTriadKNGate2AEP4MarginClosing;
         canonicalNSTriadKNGate2AEP4MarginClosing)

----------------------------------------------------------------------
-- Gate 2-A extremizer-aware transport theorem.
--
-- Theorem structure:
--
--   For x in the Gate 1 near-extremizer cone
--     E_N(ε) = { x ∈ 1_C^⊥ : (x^T L_bad x) / (x^T L_good x) ≥ ρ_N − ε },
--   the transported Gram leakage satisfies
--
--     ⟨J_N x, L_neg J_N x⟩ / ⟨J_N x, L_abs J_N x⟩ ≤ θ_* < 1.
--
-- Conservative target: θ_* ≤ 1/4.
-- Conjectural sharp target: θ_* ≈ 1/6 + o(1).
--
-- Proof is conditional on four imported lemmas (EP1–EP4).
--
-- Status: conditional theorem surface / proof plan installed.
-- The analytic reductions (EP1-EP4) are recorded here; the full
-- internal Agda proof terms are not yet constructed.  This is not
-- a closed theorem until EP1-EP4 are discharged as actual proofs.

data NSTriadKNGate2AExtremizerAwareTransportProofStep : Set where
  ep1AnisotropicSubspaceClassification :
    NSTriadKNGate2AExtremizerAwareTransportProofStep
  ep2NearExtremizerConeStructure :
    NSTriadKNGate2AExtremizerAwareTransportProofStep
  ep3SchurLiftTransportComparison :
    NSTriadKNGate2AExtremizerAwareTransportProofStep
  ep4MarginClosing :
    NSTriadKNGate2AExtremizerAwareTransportProofStep

canonicalProofSteps :
  List NSTriadKNGate2AExtremizerAwareTransportProofStep
canonicalProofSteps =
  ep1AnisotropicSubspaceClassification
  ∷ ep2NearExtremizerConeStructure
  ∷ ep3SchurLiftTransportComparison
  ∷ ep4MarginClosing
  ∷ []

canonicalTheoremText : String
canonicalTheoremText =
  "Gate 2-A extremizer-aware transport theorem surface (conditional proof plan). "
  ++ "Target: θ_* ≤ 1/4 for x ∈ E_N(ε), conditional on EP1 (O(4) anisotropic "
  ++ "classification), EP2 (near-extremizer cone), EP3 (Schur lift transport "
  ++ "comparison), EP4 (margin closing). Not yet a closed theorem."

canonicalProofPlanText : String
canonicalProofPlanText =
  "EP1: O(4) anisotropic subspace is 1-dimensional (2602.0087 Thm 3.6, imported). "
  ++ "EP2: Near-extremizer cone E_N(epsilon) is symmetry-stable modulo the seam "
  ++ "stabilizer and compatible with the operator-specific Schur lifts. "
  ++ "EP3: Directional transport budget replaces the dead coarse quotient route; "
  ++ "it factors the transported ratio into directional numerator transport, "
  ++ "directional denominator transport, and the Gate 1 seam Rayleigh ratio. "
  ++ "EP4: Combining EP1-EP3 gives theta_* <= 1/4 (conservative) with observed "
  ++ "θ_N ≈ 1/6 leaving margin."

canonicalNumericalSupportText : String
canonicalNumericalSupportText =
  "Observed θ_N stable at ≈1/6 across N=6,8,10 "
  ++ "(θ_6≈0.16815, θ_8≈0.16779, θ_10≈0.16782). "
  ++ "Coarse route fails (~18-20×), extremizer-aware route closes at θ_*≤1/4."

canonicalSourcesText : String
canonicalSourcesText =
  "Sources: 2602.0087 Thm 3.6 (O(4) classification), "
  ++ "2602.0087 Thm 5.4 (coefficient bound), "
  ++ "2602.0087 Thm 6.6 (insertion integrability), "
  ++ "docs/ns_triad_kn_gate2a_normalized_carrier_agreement.md, "
  ++ "docs/ns_triad_kn_gate2a_near_extremizer_transport_target.md."

record NSTriadKNGate2AExtremizerAwareTransportTheorem : Setω where
  constructor mkNSTriadKNGate2AExtremizerAwareTransportTheorem
  field
    theoremText : String
    theoremTextIsCanonical :
      theoremText ≡ canonicalTheoremText

    proofPlanText : String
    proofPlanTextIsCanonical :
      proofPlanText ≡ canonicalProofPlanText

    numericalSupportText : String
    numericalSupportTextIsCanonical :
      numericalSupportText ≡ canonicalNumericalSupportText

    sourcesText : String
    sourcesTextIsCanonical :
      sourcesText ≡ canonicalSourcesText

    ep1Classification :
      NSTriadKNGate2AEP1ExtremizerClassification
    ep1ClassificationIsCanonical :
      ep1Classification ≡
        canonicalNSTriadKNGate2AEP1ExtremizerClassification

    ep2ConeStability :
      NSTriadKNGate2AEP2ConeStability
    ep2ConeStabilityIsCanonical :
      ep2ConeStability ≡
        canonicalNSTriadKNGate2AEP2ConeStability

    ep3DirectionalTransportBudget :
      NSTriadKNGate2AEP3DirectionalTransportBudget
    ep3DirectionalTransportBudgetIsCanonical :
      ep3DirectionalTransportBudget ≡
        canonicalNSTriadKNGate2AEP3DirectionalTransportBudget

    ep4MarginClosing :
      NSTriadKNGate2AEP4MarginClosing
    ep4MarginClosingIsCanonical :
      ep4MarginClosing ≡
        canonicalNSTriadKNGate2AEP4MarginClosing

    proofSteps :
      List NSTriadKNGate2AExtremizerAwareTransportProofStep
    proofStepsAreCanonical :
      proofSteps ≡ canonicalProofSteps

    ep1AnisotropicClassificationAvailable : Bool
    ep1AnisotropicClassificationAvailableIsTrue :
      ep1AnisotropicClassificationAvailable ≡ true

    ep2NearExtremizerConeAvailable : Bool
    ep2NearExtremizerConeAvailableIsTrue :
      ep2NearExtremizerConeAvailable ≡ true

    ep3SchurLiftComparisonAvailable : Bool
    ep3SchurLiftComparisonAvailableIsTrue :
      ep3SchurLiftComparisonAvailable ≡ true

    ep4MarginClosingAvailable : Bool
    ep4MarginClosingAvailableIsTrue :
      ep4MarginClosingAvailable ≡ true

    theoremPlanInstalled : Bool
    theoremPlanInstalledIsTrue :
      theoremPlanInstalled ≡ true

    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNGate2AExtremizerAwareTransportTheorem public

canonicalNSTriadKNGate2AExtremizerAwareTransportTheorem :
  NSTriadKNGate2AExtremizerAwareTransportTheorem
canonicalNSTriadKNGate2AExtremizerAwareTransportTheorem =
  mkNSTriadKNGate2AExtremizerAwareTransportTheorem
    canonicalTheoremText
    refl
    canonicalProofPlanText
    refl
    canonicalNumericalSupportText
    refl
    canonicalSourcesText
    refl
    canonicalNSTriadKNGate2AEP1ExtremizerClassification
    refl
    canonicalNSTriadKNGate2AEP2ConeStability
    refl
    canonicalNSTriadKNGate2AEP3DirectionalTransportBudget
    refl
    canonicalNSTriadKNGate2AEP4MarginClosing
    refl
    canonicalProofSteps
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

theoremKeepsClayFalse :
  clayPromoted canonicalNSTriadKNGate2AExtremizerAwareTransportTheorem ≡ false
theoremKeepsClayFalse =
  refl
