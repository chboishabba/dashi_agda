module DASHI.Physics.Closure.AdapterIrreducibilityNoGoIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Four empirical adapter irreducibility targets.
--
-- This module records the no-go theorem shapes required before the terminal
-- GRQFT receipt may claim that the remaining adapter inputs are irreducible.
-- It does not prove those no-go theorems and does not promote a TOE claim.

data AdapterIrreducibilityStatus : Set where
  noGoTargetsRecordedNoIrreducibilityProof :
    AdapterIrreducibilityStatus

data AdapterIrreducibilityTarget : Set where
  metricSignatureIrreducibility :
    AdapterIrreducibilityTarget

  bornStateIrreducibility :
    AdapterIrreducibilityTarget

  vacuumSelectionIrreducibility :
    AdapterIrreducibilityTarget

  couplingConstantIrreducibility :
    AdapterIrreducibilityTarget

canonicalAdapterIrreducibilityTargets :
  List AdapterIrreducibilityTarget
canonicalAdapterIrreducibilityTargets =
  metricSignatureIrreducibility
  ∷ bornStateIrreducibility
  ∷ vacuumSelectionIrreducibility
  ∷ couplingConstantIrreducibility
  ∷ []

data AdapterIrreducibilityOpenObligation : Set where
  missingSignatureNoPreferredReductionProof :
    AdapterIrreducibilityOpenObligation

  missingNonUniqueStateSpaceProof :
    AdapterIrreducibilityOpenObligation

  missingCurvedSpacetimeNoPreferredVacuumProof :
    AdapterIrreducibilityOpenObligation

  missingNoCanonicalGaugeCouplingRatioProof :
    AdapterIrreducibilityOpenObligation

  missingGUTReceiptBoundary :
    AdapterIrreducibilityOpenObligation

canonicalAdapterIrreducibilityOpenObligations :
  List AdapterIrreducibilityOpenObligation
canonicalAdapterIrreducibilityOpenObligations =
  missingSignatureNoPreferredReductionProof
  ∷ missingNonUniqueStateSpaceProof
  ∷ missingCurvedSpacetimeNoPreferredVacuumProof
  ∷ missingNoCanonicalGaugeCouplingRatioProof
  ∷ missingGUTReceiptBoundary
  ∷ []

data AdapterIrreducibilityPromotionAuthorityToken : Set where

record AdapterIrreducibilityNoGoIndex : Setω where
  field
    status :
      AdapterIrreducibilityStatus

    targets :
      List AdapterIrreducibilityTarget

    targetsAreCanonical :
      targets
      ≡
      canonicalAdapterIrreducibilityTargets

    openObligations :
      List AdapterIrreducibilityOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalAdapterIrreducibilityOpenObligations

    signatureNoGoShape :
      String

    signatureNoGoShape-v :
      signatureNoGoShape
      ≡
      "carrier-frame-data-admits-multiple-signature-reductions-no-structural-preference"

    bornRuleNoGoShape :
      String

    bornRuleNoGoShape-v :
      bornRuleNoGoShape
      ≡
      "state-space-of-local-algebra-is-nonunique-Born-rule-needs-selected-state"

    vacuumNoGoShape :
      String

    vacuumNoGoShape-v :
      vacuumNoGoShape
      ≡
      "vacuum-selection-is-conditional-on-metric-symmetry-spectrum-and-spacetime-background"

    couplingNoGoShape :
      String

    couplingNoGoShape-v :
      couplingNoGoShape
      ≡
      "independent-gauge-holonomy-normalisations-have-no-canonical-ratio-without-GUT-receipt"

    irreducibilityProved :
      Bool

    irreducibilityProvedIsFalse :
      irreducibilityProved ≡ false

    noPromotionWithoutAuthority :
      AdapterIrreducibilityPromotionAuthorityToken →
      ⊥

    noGoBoundary :
      List String

open AdapterIrreducibilityNoGoIndex public

canonicalAdapterIrreducibilityNoGoIndex :
  AdapterIrreducibilityNoGoIndex
canonicalAdapterIrreducibilityNoGoIndex =
  record
    { status =
        noGoTargetsRecordedNoIrreducibilityProof
    ; targets =
        canonicalAdapterIrreducibilityTargets
    ; targetsAreCanonical =
        refl
    ; openObligations =
        canonicalAdapterIrreducibilityOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; signatureNoGoShape =
        "carrier-frame-data-admits-multiple-signature-reductions-no-structural-preference"
    ; signatureNoGoShape-v =
        refl
    ; bornRuleNoGoShape =
        "state-space-of-local-algebra-is-nonunique-Born-rule-needs-selected-state"
    ; bornRuleNoGoShape-v =
        refl
    ; vacuumNoGoShape =
        "vacuum-selection-is-conditional-on-metric-symmetry-spectrum-and-spacetime-background"
    ; vacuumNoGoShape-v =
        refl
    ; couplingNoGoShape =
        "independent-gauge-holonomy-normalisations-have-no-canonical-ratio-without-GUT-receipt"
    ; couplingNoGoShape-v =
        refl
    ; irreducibilityProved =
        false
    ; irreducibilityProvedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; noGoBoundary =
        "adapter irreducibility is recorded as four no-go theorem targets, not as proved"
        ∷ "signature requires a no-preferred-reduction proof over possible metric signatures"
        ∷ "Born rule requires a nonunique-state-space proof plus selected-state adapter"
        ∷ "vacuum selection requires the curved-spacetime no-preferred-vacuum boundary"
        ∷ "couplings require a no-canonical-ratio proof unless a GUT receipt is supplied"
        ∷ "no terminal GRQFT or TOE promotion follows from this index"
        ∷ []
    }
