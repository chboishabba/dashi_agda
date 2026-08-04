module DASHI.Reasoning.TypedMemeCompiler where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Combinatorics.MemeDiagonal as MemeDiagonal
import DASHI.Reasoning.SFMVerifiedClaimPresentation as SFM

------------------------------------------------------------------------
-- Intellectual production as versioned delivery, method, ecosystem and
-- interpretant shipping.  Historical insertion is kept distinct from truth.
------------------------------------------------------------------------

data DeliveryKind : Set where
  objectDelivery methodDelivery ecosystemDelivery interpretantDelivery : DeliveryKind

data CommitKind : Set where
  featureCommit fixCommit refactorCommit documentationCommit : CommitKind
  testCommit revertCommit critiqueCommit reinterpretationCommit : CommitKind

record IntellectualState : Set where
  field
    authorOrTradition : String
    deliveredObjects : List String
    shippedMethods : List String
    ecosystemRelations : List String
    interpretants : List String
    unresolvedObligations : List String
    versionLabel : String

record IntellectualTransition : Set where
  field
    before after : IntellectualState
    commitKind : CommitKind
    transitionReceipt : String
    historicalOccurrenceRetained : Bool
    truthStatusMonotone : Bool
    provenanceRetained : Bool

record Delivery : Set where
  field
    deliveryKind : DeliveryKind
    content : String
    inducedTransformation : String
    witnessSurface : String
    deliveredMeansUniversallyCorrect : Bool

------------------------------------------------------------------------
-- Peircean sign events and Eco-style constrained openness.
------------------------------------------------------------------------

record SignEvent
  (Vehicle Object Interpretant Context : Set) : Set₁ where
  field
    vehicle : Vehicle
    object : Object
    interpretant : Interpretant
    context : Context
    interpretationReceipt : String

record SemiosisStep (Sign Interpretant : Set) : Set₁ where
  field
    currentSign : Sign
    currentInterpretant : Interpretant
    reifyInterpretant : Interpretant → Sign
    nextSignIsReifiedInterpretant :
      reifyInterpretant currentInterpretant ≡ currentSign

record AdmissibleInterpretation
  (Artifact Context Interpretation : Set) : Set₁ where
  field
    artifact : Artifact
    context : Context
    interpretation : Interpretation
    textualFit : Set
    contextualFit : Set
    coherent : Set
    provenancePresent : Set
    textualFitWitness : textualFit
    contextualFitWitness : contextualFit
    coherenceWitness : coherent
    provenanceWitness : provenancePresent

------------------------------------------------------------------------
-- Local evidence and sheaf-like gluing.
------------------------------------------------------------------------

record LocalEvidenceSystem
  (Region LocalSection GlobalSection : Set) : Set₁ where
  field
    restrict : GlobalSection → Region → LocalSection
    compatible : (Region → LocalSection) → Set
    glue :
      (locals : Region → LocalSection) →
      compatible locals →
      GlobalSection
    glueRestricts :
      ∀ locals witness region →
      restrict (glue locals witness) region ≡ locals region
    falsifiable : Region → LocalSection → Set
    falsifiabilityStableUnderRestrictionClaimed : Bool

record EvidenceTheoryAdjunction
  (Evidence Theory : Set) : Set₁ where
  field
    assemble : Evidence → Theory
    consequences : Theory → Evidence
    EvidenceMap : Evidence → Evidence → Set
    TheoryMap : Theory → Theory → Set
    transposeForward :
      ∀ evidence theory →
      TheoryMap (assemble evidence) theory →
      EvidenceMap evidence (consequences theory)
    transposeBackward :
      ∀ evidence theory →
      EvidenceMap evidence (consequences theory) →
      TheoryMap (assemble evidence) theory

------------------------------------------------------------------------
-- Garden-of-Eden reachability and zero-ontology boundary.
------------------------------------------------------------------------

record LocalRuleSystem (Configuration : Set) : Set₁ where
  field
    step : Configuration → Configuration
    localityReceipt : String
    equivarianceReceipt : String

GardenOfEden :
  ∀ {Configuration} →
  LocalRuleSystem Configuration →
  Configuration →
  Set
GardenOfEden system target =
  ¬ Σ _ λ source → LocalRuleSystem.step system source ≡ target

record Contractible (A : Set) : Set₁ where
  field
    centre : A
    contract : ∀ x → centre ≡ x

record IndexedTransformability (A Criterion : Set) : Set₁ where
  field
    related : Criterion → A → A → Set
    criterionReceipt : Criterion → String
    relationDoesNotImplyIdentity : Bool

------------------------------------------------------------------------
-- Polytemporal and persistent-drive systems.
------------------------------------------------------------------------

record PolytemporalSystem (Voice : Set) : Set₁ where
  field
    localClock : Voice → Nat → Nat
    couplingReceipt : String
    identicalClocksRequired : Bool
    globalCoherenceWitnessRequired : Bool

record PersistentDriveSystem (State Drive Action : Set) : Set₁ where
  field
    policy : State → Drive → Action
    updateState : State → Action → State
    updateDrive : Drive → State → Drive
    satisfaction : State → Drive → Nat
    satisfactionTerminatesDriveClaimed : Bool
    persistenceReceipt : String

------------------------------------------------------------------------
-- Typed meme compilation and epistemic status.
------------------------------------------------------------------------

data EpistemicStatus : Set where
  proved empirical plausible unsupported refuted : EpistemicStatus

data RhetoricalStatus : Set where
  literal metaphorical satirical parodic wordplay : RhetoricalStatus

record TypedClaim : Set where
  field
    proposition : String
    epistemic : EpistemicStatus
    rhetorical : RhetoricalStatus
    witness : String
    scope : String
    provenance : String

record TypedMemeCompilation : Set₁ where
  field
    inputVehicle : String
    extractedClaims : List TypedClaim
    formalAnalogues : List String
    proofObligations : List String
    outputClaimStates : List SFM.SFMClaimState
    diagonalStreamWitnessAvailable : Bool
    targetRulesGovernPromotion : Bool

record ProductiveMemeTranslation : Set where
  field
    sourceDomain targetDomain : String
    generatedQuestion : String
    declaredInvariant : String
    recordedLoss : String
    targetVerificationRule : String
    targetAccepted : Bool
    literalTruthRequiredForUsefulness : Bool

record TypedMemeCompilerAuthorityBoundary : Set where
  field
    mythCanPropose : Bool
    mythCanProve : Bool
    localResemblanceImpliesIdentity : Bool
    gardenOfEdenMeansMysticalInfinity : Bool
    allInstancesOfTypeAreIdentical : Bool
    infiniteMemeDiagonalTheoremAvailable : Bool
    finiteMemeStringsDeclaredUncountable : Bool
    humourAndProofStatusesSeparated : Bool
    boundaryNote : String

canonicalTypedMemeCompilerAuthorityBoundary :
  TypedMemeCompilerAuthorityBoundary
canonicalTypedMemeCompilerAuthorityBoundary = record
  { mythCanPropose = true
  ; mythCanProve = false
  ; localResemblanceImpliesIdentity = false
  ; gardenOfEdenMeansMysticalInfinity = false
  ; allInstancesOfTypeAreIdentical = false
  ; infiniteMemeDiagonalTheoremAvailable = true
  ; finiteMemeStringsDeclaredUncountable = false
  ; humourAndProofStatusesSeparated = true
  ; boundaryNote =
      "The typed meme compiler extracts candidate claims, exact analogues, losses and proof obligations; target-domain verification alone promotes."
  }
