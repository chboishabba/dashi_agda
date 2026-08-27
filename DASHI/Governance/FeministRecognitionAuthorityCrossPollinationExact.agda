module DASHI.Governance.FeministRecognitionAuthorityCrossPollinationExact where

open import DASHI.Core.Prelude
import DASHI.Core.RecognitionConstitutionNonfactorabilityExact as Recognition

------------------------------------------------------------------------
-- FEMINIST / RECOGNITION / ANTI-SUBLATION CROSS-POLLINATION
--
-- Internal theorem-pattern provenance:
--   PR #620: IntersectionalNonFactorability, PositiveRecharting and the
--            FeministRechartingSourceBridge.
--   Recent #620-line commits add:
--     * IrigarayLabialRelationalCarrierExact -- reciprocal contact, neither-one-
--       nor-two role boundary, endpoint nonseparability;
--     * LacanIrigarayTernaryGrammarBridgeExact -- same finite carrier does not
--       imply same relational grammar, and no enumerated ternary relabelling
--       identifies the two finite graphs;
--     * RepresentationSubjectPositionNonfactorabilityExact -- representability,
--       speech surface and exchange visibility do not recover originating
--       subject-position/authority.
--   PR #598: CapabilityRecognitionExact -- capability present != socially
--            legible != recognized; non-recognition != absence of capability.
--   PR #603: contested ambient authority / anti-sublation -- recognition or
--            coercive dominance does not self-issue/exhaust exterior authority.
--
-- External conceptual sources retained with the roles already calibrated on
-- #620 (not authorship of the generic theorem):
--   Luce Irigaray, This Sex Which Is Not One, ISBN 9780801493317.
--   Helene Cixous, The Laugh of the Medusa, DOI 10.1086/493306.
--   Audre Lorde, Uses of the Erotic: The Erotic as Power, ISBN 9780918314093;
--     later anthology DOI 10.1093/oso/9780198782506.003.0032.
--   Monique Wittig, One Is Not Born a Woman; later anthology DOI
--     10.1093/oso/9780192892706.003.0036.
--   Kimberle Crenshaw, Demarginalizing the Intersection of Race and Sex
--     (1989), no DOI asserted; Mapping the Margins (1991), DOI 10.2307/1229039.
--
-- The Moreton-Robinson/Smith/Whyte bridges on #625 are retrospective DASHI
-- theorem-pattern cross-pollination, not a claim that these authors belong to
-- one historical school or endorse one another's vocabulary.
------------------------------------------------------------------------

data TheoremPattern : Set where
  erasedCoordinateNonfactorability
  strictPositiveRecharting
  nonlinearIntersection
  capabilityRecognitionSeparation
  antiSublationExteriorAuthority
  recognitionConstitutionSeparation
  subjectPositionNonfactorability
  relationalMultiplicity
  sameCarrierDifferentGrammar
  : TheoremPattern

data SourceRegister : Set where
  irigarayRegister cixousRegister lordeRegister wittigRegister crenshawRegister
  moretonRobinsonRegister smithRegister whyteRegister : SourceRegister

record CrossPollinationRole : Set where
  constructor crossPollinationRole
  field
    sourceRegister : SourceRegister
    theoremPattern : TheoremPattern
    retrospectiveDASHIConnection : Bool

irigarayRechartRole : CrossPollinationRole
irigarayRechartRole =
  crossPollinationRole irigarayRegister relationalMultiplicity true

irigarayGrammarRole : CrossPollinationRole
irigarayGrammarRole =
  crossPollinationRole irigarayRegister sameCarrierDifferentGrammar true

crenshawInteractionRole : CrossPollinationRole
crenshawInteractionRole =
  crossPollinationRole crenshawRegister nonlinearIntersection true

moretonRobinsonRecognitionRole : CrossPollinationRole
moretonRobinsonRecognitionRole =
  crossPollinationRole moretonRobinsonRegister recognitionConstitutionSeparation true

smithSubjectPositionRole : CrossPollinationRole
smithSubjectPositionRole =
  crossPollinationRole smithRegister subjectPositionNonfactorability true

whyteHistoryRole : CrossPollinationRole
whyteHistoryRole =
  crossPollinationRole whyteRegister erasedCoordinateNonfactorability true

------------------------------------------------------------------------
-- Common recognition theorem shape.
------------------------------------------------------------------------

data SituatedState : Set where leftState rightState : SituatedState
data VisibleCode : Set where sameVisibleCode : VisibleCode
data SituatedCode : Set where leftSituated rightSituated : SituatedCode

visible : SituatedState → VisibleCode
visible leftState = sameVisibleCode
visible rightState = sameVisibleCode

situated : SituatedState → SituatedCode
situated leftState = leftSituated
situated rightState = rightSituated

commonSystem : Recognition.RecognitionSystem SituatedState VisibleCode SituatedCode
commonSystem = Recognition.recognitionSystem visible situated

commonCollision : Recognition.RecognitionCollision commonSystem
commonCollision = Recognition.recognitionCollision leftState rightState refl (λ ())

visibleSurfaceDoesNotExhaustSituatedCoordinate :
  Recognition.FactorsThroughRecognition commonSystem → ⊥
visibleSurfaceDoesNotExhaustSituatedCoordinate =
  Recognition.collisionBlocksAuthorityFactorization commonCollision

------------------------------------------------------------------------
-- Same carrier != same relational grammar.
-- This is a small source-neutral shadow of the stronger exhaustive finite
-- relabelling obstruction already implemented on the #620 lineage.
------------------------------------------------------------------------

data SharedCode : Set where code0 code1 code2 : SharedCode

oneCentredEdge : SharedCode → SharedCode → Bool
oneCentredEdge code1 code0 = true
oneCentredEdge code1 code2 = true
oneCentredEdge _ _ = false

reciprocalEdge : SharedCode → SharedCode → Bool
reciprocalEdge code1 code2 = true
reciprocalEdge code2 code1 = true
reciprocalEdge _ _ = false

sameCarrierIdentityChartDoesNotPreserveGrammar :
  ((left right : SharedCode) → oneCentredEdge left right ≡ reciprocalEdge left right) → ⊥
sameCarrierIdentityChartDoesNotPreserveGrammar preservation =
  trueNotFalse (preservation code1 code0)
  where
  trueNotFalse : true ≡ false → ⊥
  trueNotFalse ()

record FeministRecognitionCrossPollinationBoundary : Set where
  constructor feministRecognitionCrossPollinationBoundary
  field
    crossPollinationMeansHistoricalSourceIdentity : Bool
    crossPollinationMeansHistoricalSourceIdentityIsFalse :
      crossPollinationMeansHistoricalSourceIdentity ≡ false
    symbolicRelabelingRepairsErasedCoordinate : Bool
    symbolicRelabelingRepairsErasedCoordinateIsFalse :
      symbolicRelabelingRepairsErasedCoordinate ≡ false
    sameCarrierImpliesSameRelationalGrammar : Bool
    sameCarrierImpliesSameRelationalGrammarIsFalse :
      sameCarrierImpliesSameRelationalGrammar ≡ false
    recognitionCreatesCapabilityOrAuthority : Bool
    recognitionCreatesCapabilityOrAuthorityIsFalse :
      recognitionCreatesCapabilityOrAuthority ≡ false
    feministSourceCitationAuthorsDASHIFiniteWitness : Bool
    feministSourceCitationAuthorsDASHIFiniteWitnessIsFalse :
      feministSourceCitationAuthorsDASHIFiniteWitness ≡ false
    antiLacanianPatternMeansMoretonRobinsonIsHistoricallyAntiLacanian : Bool
    antiLacanianPatternMeansMoretonRobinsonIsHistoricallyAntiLacanianIsFalse :
      antiLacanianPatternMeansMoretonRobinsonIsHistoricallyAntiLacanian ≡ false

canonicalFeministRecognitionCrossPollinationBoundary :
  FeministRecognitionCrossPollinationBoundary
canonicalFeministRecognitionCrossPollinationBoundary =
  feministRecognitionCrossPollinationBoundary
    false refl false refl false refl false refl false refl false refl
