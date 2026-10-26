module DASHI.Biology.IIT4FiniteCausalStructureExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- IIT 4.0 FINITE STRUCTURAL CARRIER
--
-- Source calibration:
-- Albantakis et al., "Integrated information theory (IIT) 4.0:
-- Formulating the properties of phenomenal existence in physical terms",
-- PLoS Computational Biology 19(10), 2023, e1011465.
-- DOI: 10.1371/journal.pcbi.1011465.
--
-- This owner formalises the finite carrier and the separation of the named IIT
-- quantities.  It deliberately does NOT fabricate a real/log probability
-- backend.  The finite probability and system-phi input owners downstream pay
-- the discrete repertoire / partition plumbing, leaving only the declared
-- analytic scalar and full distinction/relation unfolding as separate layers.
--
-- In particular:
--   phi_s  : system integrated information / partition irreducibility;
--   phi_d  : distinction integrated information;
--   phi_r  : relation integrated information;
--   Phi    : structure integrated information of distinctions + relations.
--
-- They are not collapsed into one generic `phi` scalar.
------------------------------------------------------------------------

data _ListedIn_ {A : Set} (x : A) : List A → Set where
  listedHere : ∀ {xs} → x ListedIn (x ∷ xs)
  listedThere : ∀ {y xs} → x ListedIn xs → x ListedIn (y ∷ xs)

record FiniteCarrier : Set₁ where
  constructor finiteCarrier
  field
    Carrier : Set
    enumeration : List Carrier
    enumerationComplete : (x : Carrier) → x ListedIn enumeration

open FiniteCarrier public

record FiniteCausalSystem : Set₁ where
  constructor finiteCausalSystem
  field
    units : FiniteCarrier
    states : FiniteCarrier
    currentState : Carrier states

    -- A finite transition-probability table is supplied abstractly as weights.
    -- The normalization convention is explicit metadata rather than silently
    -- assumed arithmetic over Nat.
    transitionWeight : Carrier states → Carrier states → Nat
    transitionNormalization : String

open FiniteCausalSystem public

UnitOf : FiniteCausalSystem → Set
UnitOf system = Carrier (units system)

StateOf : FiniteCausalSystem → Set
StateOf system = Carrier (states system)

UnitMask : FiniteCausalSystem → Set
UnitMask system = UnitOf system → Bool

Mechanism : FiniteCausalSystem → Set
Mechanism = UnitMask

Purview : FiniteCausalSystem → Set
Purview = UnitMask

------------------------------------------------------------------------
-- Directional system partitions, IIT 4.0 equations 14--18.
------------------------------------------------------------------------

data CutDirection : Set where
  cutInputs : CutDirection
  cutOutputs : CutDirection
  cutBoth : CutDirection

record DirectedPart (system : FiniteCausalSystem) : Set where
  constructor directedPart
  field
    member : UnitMask system
    direction : CutDirection
    partLabel : String

open DirectedPart public

record SystemPartition (system : FiniteCausalSystem) : Set where
  constructor systemPartition
  field
    parts : List (DirectedPart system)
    partitionLabel : String
    affectedConnectionCount : Nat
    nontrivialityReceipt : String
    disjointCoverReceipt : String

open SystemPartition public

record CausalDistinction (system : FiniteCausalSystem) : Set where
  constructor causalDistinction
  field
    mechanism : Mechanism system
    causePurview : Purview system
    effectPurview : Purview system
    distinctionLabel : String

open CausalDistinction public

record CausalRelation (system : FiniteCausalSystem) : Set where
  constructor causalRelation
  field
    relatedDistinctions : List (CausalDistinction system)
    relationLabel : String

open CausalRelation public

record IIT4ScoreBackend (system : FiniteCausalSystem) : Set₁ where
  constructor iit4ScoreBackend
  field
    Score : Set

    -- IIT 4.0 quantities remain definitionally separate.
    phiSystem : SystemPartition system → Score
    phiDistinction : CausalDistinction system → Score
    phiRelation : CausalRelation system → Score
    bigPhi :
      List (CausalDistinction system) →
      List (CausalRelation system) →
      Score

    -- Algorithmic selectors are supplied by the numerical backend.
    minimumSystemPartition : SystemPartition system
    maximalSubstrateReceipt : String
    probabilityMeasureReceipt : String

open IIT4ScoreBackend public

record IIT4PhiStructure
    (system : FiniteCausalSystem)
    (backend : IIT4ScoreBackend system) : Set where
  constructor iit4PhiStructure
  field
    distinctions : List (CausalDistinction system)
    relations : List (CausalRelation system)
    structureScore : Score backend
    scoreIsBackendBigPhi :
      structureScore ≡ bigPhi backend distinctions relations

open IIT4PhiStructure public

record IIT4SourceBoundary : Set where
  constructor iit4SourceBoundary
  field
    substrateSpecifiedByTransitionProbabilityFunction : Bool
    systemPartitionsAreDirectional : Bool
    systemPartitionPartsRequireDisjointCoverReceipt : Bool
    partitionNormalisationCountIsExplicit : Bool
    systemPhiUsesPartitionIrreducibility : Bool
    distinctionPhiAndRelationPhiAreSeparate : Bool
    bigPhiComposesDistinctionsAndRelations : Bool
    bigPhiIsDirectlyTheSystemPartitionScore : Bool
    historicalIIT3PhiCalculationAutomaticallyEqualsIIT4BigPhi : Bool
    scoreAloneEstablishesPhenomenalIdentityOutsideIITPostulates : Bool
    realLogProbabilityBackendImplementedHere : Bool

open IIT4SourceBoundary public

canonicalIIT4SourceBoundary : IIT4SourceBoundary
canonicalIIT4SourceBoundary =
  iit4SourceBoundary
    true true true true true true true
    false false false false

systemPhiAndBigPhiNotCollapsed :
  bigPhiIsDirectlyTheSystemPartitionScore canonicalIIT4SourceBoundary ≡ false
systemPhiAndBigPhiNotCollapsed = refl

historicalCounterexampleVersionBoundary :
  historicalIIT3PhiCalculationAutomaticallyEqualsIIT4BigPhi canonicalIIT4SourceBoundary ≡ false
historicalCounterexampleVersionBoundary = refl

numericalBackendStillExplicit :
  realLogProbabilityBackendImplementedHere canonicalIIT4SourceBoundary ≡ false
numericalBackendStillExplicit = refl
