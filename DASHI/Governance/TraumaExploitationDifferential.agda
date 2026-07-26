module DASHI.Governance.TraumaExploitationDifferential where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set; Set₁)
open import Data.Empty using (⊥)

open import DASHI.Governance.TraumaExploitationAttractor

------------------------------------------------------------------------
-- Local tangent carriers for the heterogeneous social recursion.

record LocalLinearTransport
  (V W : Set)
  : Set₁ where
  field
    apply : V → W

open LocalLinearTransport public

composeTransport :
  {U V W : Set} →
  LocalLinearTransport V W →
  LocalLinearTransport U V →
  LocalLinearTransport U W
composeTransport F G =
  record { apply = λ u → apply F (apply G u) }

record TraumaExploitationDifferential
  (S : TraumaExploitationSystem)
  : Set₁ where
  field
    HistoricalTangent : HistoricalState S → Set
    SufferingTangent : SufferingField S → Set
    ProtocolTangent : ExploitationProtocol S → Set
    InstitutionTangent : Institution S → Set

    dTraumaProduction :
      (x : HistoricalState S) →
      LocalLinearTransport
        (HistoricalTangent x)
        (SufferingTangent (traumaProduction S x))

    dExploitationExtraction :
      (s : SufferingField S) →
      LocalLinearTransport
        (SufferingTangent s)
        (ProtocolTangent (exploitationExtraction S s))

    dInstitutionalise :
      (p : ExploitationProtocol S) →
      LocalLinearTransport
        (ProtocolTangent p)
        (InstitutionTangent (institutionalise S p))

    dReproduce :
      (i : Institution S) →
      (x : HistoricalState S) →
      LocalLinearTransport
        (InstitutionTangent i)
        (HistoricalTangent (reproduce S i x))

open TraumaExploitationDifferential public

fullStepDifferential :
  {S : TraumaExploitationSystem} →
  (D : TraumaExploitationDifferential S) →
  (x : HistoricalState S) →
  LocalLinearTransport
    (HistoricalTangent D x)
    (HistoricalTangent D (step S x))
fullStepDifferential {S} D x =
  let
    suffering = traumaProduction S x
    protocol = exploitationExtraction S suffering
    institution = institutionalise S protocol
  in
  composeTransport
    (dReproduce D institution x)
    (composeTransport
      (dInstitutionalise D protocol)
      (composeTransport
        (dExploitationExtraction D suffering)
        (dTraumaProduction D x)))

fullStepDifferentialIsChain :
  {S : TraumaExploitationSystem} →
  (D : TraumaExploitationDifferential S) →
  (x : HistoricalState S) →
  (v : HistoricalTangent D x) →
  apply (fullStepDifferential D x) v
  ≡ apply
      (dReproduce D
        (institutionalise S
          (exploitationExtraction S
            (traumaProduction S x)))
        x)
      (apply
        (dInstitutionalise D
          (exploitationExtraction S
            (traumaProduction S x)))
        (apply
          (dExploitationExtraction D
            (traumaProduction S x))
          (apply (dTraumaProduction D x) v)))
fullStepDifferentialIsChain D x v = refl

------------------------------------------------------------------------
-- Typed attribution of local amplification.

record DifferentialAttribution
  {S : TraumaExploitationSystem}
  (D : TraumaExploitationDifferential S)
  (x : HistoricalState S)
  : Set₁ where
  field
    Measure : Set

    sufferingEntry :
      HistoricalTangent D x → Measure

    extractionAmplification :
      SufferingTangent D (traumaProduction S x) → Measure

    scalabilityGain :
      ProtocolTangent D
        (exploitationExtraction S (traumaProduction S x)) →
      Measure

    externalisationGain :
      InstitutionTangent D
        (institutionalise S
          (exploitationExtraction S (traumaProduction S x))) →
      Measure

------------------------------------------------------------------------
-- No political conclusion follows from a large local gain alone.
--
-- The earlier surface merely returned Set.  The strengthened boundary requires
-- every normative authority to expose independent evidence, then makes a
-- gain-only authority attempt contradictory.

record DifferentialPromotionBoundary
  {S : TraumaExploitationSystem}
  (D : TraumaExploitationDifferential S)
  : Set₁ where
  field
    GainEvidence : Set
    IndependentEvidence : Set
    NormativeAuthority : Set
    authorityCarriesIndependentEvidence :
      NormativeAuthority → IndependentEvidence

open DifferentialPromotionBoundary public

record GainOnlyAuthorityAttempt
  {S : TraumaExploitationSystem}
  {D : TraumaExploitationDifferential S}
  (B : DifferentialPromotionBoundary D)
  : Set₁ where
  field
    gain : GainEvidence B
    noIndependentEvidenceAvailable : IndependentEvidence B → ⊥
    claimedAuthority : NormativeAuthority B

open GainOnlyAuthorityAttempt public

gainOnlyAuthorityAttemptImpossible :
  {S : TraumaExploitationSystem} →
  {D : TraumaExploitationDifferential S} →
  {B : DifferentialPromotionBoundary D} →
  GainOnlyAuthorityAttempt B → ⊥
gainOnlyAuthorityAttemptImpossible attempt =
  noIndependentEvidenceAvailable attempt
    (authorityCarriesIndependentEvidence _ (claimedAuthority attempt))

record TraumaExploitationDifferentialReceipt
  (S : TraumaExploitationSystem)
  : Set₁ where
  field
    differential : TraumaExploitationDifferential S
    attributionAt :
      (x : HistoricalState S) →
      DifferentialAttribution differential x
    promotionBoundary :
      DifferentialPromotionBoundary differential
