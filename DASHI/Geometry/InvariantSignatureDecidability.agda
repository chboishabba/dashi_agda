module DASHI.Geometry.InvariantSignatureDecidability where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.AdmissibilityJetSpec as Spec

------------------------------------------------------------------------
-- Invariant signatures and the formal meaning of "could not decide".
--
-- Two representatives may remain indistinguishable at a depth because the
-- admitted invariant family does not yet separate their redundancy orbits.
-- This module records that boundary without treating non-separation as error
-- and without claiming that Cartan completion has been constructed globally.


data SeparationStatus : Set where
  separatedAtDepth : SeparationStatus
  indistinguishableAtDepth : SeparationStatus
  liftRequired : SeparationStatus
  invariantFamilyIncomplete : SeparationStatus

separationStatusName : SeparationStatus → String
separationStatusName separatedAtDepth = "separated-at-depth"
separationStatusName indistinguishableAtDepth = "indistinguishable-at-depth"
separationStatusName liftRequired = "lift-required"
separationStatusName invariantFamilyIncomplete = "invariant-family-incomplete"

record InvariantSignatureRow : Set where
  constructor mkInvariantSignatureRow
  field
    signatureLabel : String
    admissibilitySpec : Spec.DepthAdmissibilitySpec
    invariantNames : List String
    status : SeparationStatus
    sameSignatureImpliesSameOrbitClaimed : Bool
    representativeUniquenessClaimed : Bool
    deeperLiftMaySeparate : Bool
    boundaryStatement : String

open InvariantSignatureRow public

metricTwoJetSignatureRow : InvariantSignatureRow
metricTwoJetSignatureRow =
  mkInvariantSignatureRow
    "metric-two-jet-invariant-signature"
    Spec.metricDiffeomorphismTwoJetSpec
    ("scalar-curvature"
     ∷ "ricci-curvature"
     ∷ "cartan-signature-candidate"
     ∷ [])
    invariantFamilyIncomplete
    false
    false
    true
    "two-jet curvature data is an admissible local signature, not a proved complete diffeomorphism classifier"

spinorOneJetSignatureRow : InvariantSignatureRow
spinorOneJetSignatureRow =
  mkInvariantSignatureRow
    "spinor-one-jet-invariant-signature"
    Spec.spinorOneJetSpec
    ("dirac-operator-candidate"
     ∷ "spin-covariant-derivative"
     ∷ [])
    liftRequired
    false
    false
    true
    "spinor sign and orientation may require the spin lift; tensor invariants alone need not separate representatives"

bitensorSignatureRow : InvariantSignatureRow
bitensorSignatureRow =
  mkInvariantSignatureRow
    "bitensor-relational-signature"
    Spec.bitensorTwoPointSpec
    ("two-point-correlator"
     ∷ "parallel-transport-candidate"
     ∷ "green-kernel-candidate"
     ∷ [])
    indistinguishableAtDepth
    false
    false
    true
    "pairwise invariant data can preserve relational structure while leaving point representatives undecided"

canonicalInvariantSignatureRows : List InvariantSignatureRow
canonicalInvariantSignatureRows =
  metricTwoJetSignatureRow
  ∷ spinorOneJetSignatureRow
  ∷ bitensorSignatureRow
  ∷ []

record OrbitSeparationWitness {State Signature : Set}
                              (signature : State → Signature) : Set₁ where
  constructor mkOrbitSeparationWitness
  field
    sameSignature→sameState :
      ∀ {x y : State} → signature x ≡ signature y → x ≡ y

open OrbitSeparationWitness public

record DepthDecisionBoundary : Set where
  constructor mkDepthDecisionBoundary
  field
    decisionLabel : String
    depth : Nat
    signatureRows : List InvariantSignatureRow
    currentDepthSeparatesAllOrbits : Bool
    undecidedMeansContradiction : Bool
    liftingPermitted : Bool
    boundaryHolds : Bool
    decisionStatement : String

open DepthDecisionBoundary public

canonicalDepthDecisionBoundary : DepthDecisionBoundary
canonicalDepthDecisionBoundary =
  mkDepthDecisionBoundary
    "invariant-signature-depth-decision-boundary"
    (suc (suc zero))
    canonicalInvariantSignatureRows
    false
    false
    true
    true
    "could-not-decide means the admitted invariant signature does not yet separate representatives; it is not a contradiction"

canonicalBoundaryDoesNotForceDecision :
  currentDepthSeparatesAllOrbits canonicalDepthDecisionBoundary ≡ false
canonicalBoundaryDoesNotForceDecision = refl

canonicalBoundaryAllowsLift : liftingPermitted canonicalDepthDecisionBoundary ≡ true
canonicalBoundaryAllowsLift = refl
