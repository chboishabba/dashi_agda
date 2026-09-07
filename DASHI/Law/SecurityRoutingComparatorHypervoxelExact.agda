module DASHI.Law.SecurityRoutingComparatorHypervoxelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Law.SecurityClassificationProvenanceBidiExact as Security
import DASHI.Law.FascismAtrocitySourceCrossPollinationExact as Fascism
import DASHI.Law.HerzogPoliceCountryColonialityCrossPollinationExact as Coloniality

------------------------------------------------------------------------
-- SECURITY ROUTING COMPARATOR HYPERVOXEL
--
-- Compare protective and coercive routing without assuming the compared events
-- are legally/factually identical and without inferring motive from disparity.
------------------------------------------------------------------------

data ComparatorEvent : Set where
  herzogTownHallProtest : ComparatorEvent
  sydneyMarathonIsraeliMilitaryDelegation : ComparatorEvent
  jewishInstitutionOrBondiSecurityOperation : ComparatorEvent
  syntheticComparatorEvent : ComparatorEvent

data PoliticalPosition : Set where
  antiGenocidePalestinianSolidarity : PoliticalPosition
  israeliStateOrMilitaryAssociated : PoliticalPosition
  jewishCommunityProtectionContext : PoliticalPosition
  politicalPositionMixed : PoliticalPosition
  politicalPositionUnresolved : PoliticalPosition

data SupportState : Set where
  supportObserved : SupportState
  supportReported : SupportState
  supportOpen : SupportState
  supportConflict : SupportState

data RoutingPattern : Set where
  protectiveDominant : RoutingPattern
  coerciveDominant : RoutingPattern
  mixedRouting : RoutingPattern
  routingUnresolved : RoutingPattern

data CoarseSecurityIntensity : Set where
  lowSecurityIntensity : CoarseSecurityIntensity
  elevatedSecurityIntensity : CoarseSecurityIntensity
  highSecurityIntensity : CoarseSecurityIntensity

record SecurityRoutingHypervoxel : Set where
  constructor securityRoutingHypervoxel
  field
    event : ComparatorEvent
    politicalPosition : PoliticalPosition
    classification : Security.ClassificationLabel
    preActionClassificationReceipt : SupportState
    intelligenceInputReceipt : SupportState
    policeDeploymentReceipt : SupportState
    protectiveEscortReceipt : SupportState
    containmentReceipt : SupportState
    mountedPoliceReceipt : SupportState
    chemicalAgentReceipt : SupportState
    arrestOrSearchReceipt : SupportState
    privateSecurityInputReceipt : SupportState
    foreignLiaisonReceipt : SupportState
    exitAccessReceipt : SupportState
    civilianDirectionReceipt : SupportState
    routingPattern : RoutingPattern
    coarseIntensity : CoarseSecurityIntensity
    sourceReference : String

open SecurityRoutingHypervoxel public

------------------------------------------------------------------------
-- Source-bounded event fixtures.  'reported' is not promoted to official fact;
-- pre-action classification remains unresolved unless the underlying document
-- has actually been acquired.
------------------------------------------------------------------------

herzogComparator : SecurityRoutingHypervoxel
herzogComparator = securityRoutingHypervoxel
  herzogTownHallProtest
  antiGenocidePalestinianSolidarity
  Security.classificationUnresolved
  supportOpen
  supportOpen
  supportObserved
  supportOpen
  supportReported
  supportReported
  supportObserved
  supportOpen
  supportOpen
  supportReported
  supportReported
  coerciveDominant
  highSecurityIntensity
  "Legal Observers NSW final report; ABC verified/reporting; NSW Police public account; LECC Operation Makalu. Underlying pre-action risk/intelligence documents remain open."

marathonComparator : SecurityRoutingHypervoxel
marathonComparator = securityRoutingHypervoxel
  sydneyMarathonIsraeliMilitaryDelegation
  israeliStateOrMilitaryAssociated
  Security.classificationUnresolved
  supportOpen
  supportOpen
  supportObserved
  supportReported
  supportOpen
  supportOpen
  supportOpen
  supportOpen
  supportOpen
  supportOpen
  supportOpen
  supportOpen
  protectiveDominant
  highSecurityIntensity
  "NSW Police marathon operation release plus Michael West Media report of dedicated running protection for six serving IDF runners; exact police order/classification remains open."

institutionSecurityComparator : SecurityRoutingHypervoxel
institutionSecurityComparator = securityRoutingHypervoxel
  jewishInstitutionOrBondiSecurityOperation
  jewishCommunityProtectionContext
  Security.classificationUnresolved
  supportOpen
  supportOpen
  supportObserved
  supportObserved
  supportOpen
  supportOpen
  supportOpen
  supportOpen
  supportObserved
  supportOpen
  supportOpen
  supportOpen
  protectiveDominant
  elevatedSecurityIntensity
  "Royal Commission evidence on Jewish community security coordination, licensed fixed-site armed security, and police/security-agency liaison; no generic public-patrol inference."

------------------------------------------------------------------------
-- A coarse security-intensity observer cannot reconstruct whether resources
-- were routed protectively or coercively.  This is the core x-pollination with
-- dominant-chart/non-factorability architecture.
------------------------------------------------------------------------

coarseSecurityObserver : SecurityRoutingHypervoxel → CoarseSecurityIntensity
coarseSecurityObserver = coarseIntensity

routingTarget : SecurityRoutingHypervoxel → RoutingPattern
routingTarget = routingPattern

syntheticProtectiveHigh : SecurityRoutingHypervoxel
syntheticProtectiveHigh = securityRoutingHypervoxel
  syntheticComparatorEvent politicalPositionMixed Security.classificationUnresolved
  supportOpen supportOpen supportObserved supportObserved
  supportOpen supportOpen supportOpen supportOpen supportOpen supportOpen
  supportOpen supportOpen protectiveDominant highSecurityIntensity
  "synthetic non-factorability witness: high-intensity protective routing"

syntheticCoerciveHigh : SecurityRoutingHypervoxel
syntheticCoerciveHigh = securityRoutingHypervoxel
  syntheticComparatorEvent politicalPositionMixed Security.classificationUnresolved
  supportOpen supportOpen supportObserved supportOpen
  supportObserved supportObserved supportObserved supportOpen supportOpen supportOpen
  supportOpen supportOpen coerciveDominant highSecurityIntensity
  "synthetic non-factorability witness: high-intensity coercive routing"

sameCoarseIntensity :
  coarseSecurityObserver syntheticProtectiveHigh ≡
  coarseSecurityObserver syntheticCoerciveHigh
sameCoarseIntensity = refl

routingPatternsDiffer :
  routingTarget syntheticProtectiveHigh ≡ routingTarget syntheticCoerciveHigh → ⊥
routingPatternsDiffer ()

coarseIntensityNonFactorability :
  NF.NonFactorabilityWitness coarseSecurityObserver routingTarget
coarseIntensityNonFactorability = NF.nonFactorabilityWitness
  syntheticProtectiveHigh
  syntheticCoerciveHigh
  sameCoarseIntensity
  routingPatternsDiffer

coarseSecurityIntensityCannotDetermineRouting :
  NF.FactorsThrough coarseSecurityObserver routingTarget → ⊥
coarseSecurityIntensityCannotDetermineRouting =
  NF.witnessRulesOutEveryFlatFactorisation coarseIntensityNonFactorability

------------------------------------------------------------------------
-- Comparator conditioning: observed routing difference is not yet a motive or
-- discrimination conclusion.  Comparable security need must be established.
------------------------------------------------------------------------

data ComparatorClaim : Set where
  protectiveCoerciveRoutingDiffers : ComparatorClaim
  eventsComparableOnSecurityNeed : ComparatorClaim
  routingDifferencePersistsAfterConditioning : ComparatorClaim
  identityOrPoliticalProvenanceAffectedRouting : ComparatorClaim
  ideologicalMotiveClosed : ComparatorClaim

data ComparatorProducer : Set where
  eventRoutingReceiptProducer : ComparatorProducer
  securityNeedCovariateProducer : ComparatorProducer
  conditionedComparatorProducer : ComparatorProducer
  classificationDecisionProvenanceProducer : ComparatorProducer
  motiveProducer : ComparatorProducer

reverseComparator : ComparatorClaim → ComparatorProducer
reverseComparator protectiveCoerciveRoutingDiffers = eventRoutingReceiptProducer
reverseComparator eventsComparableOnSecurityNeed = securityNeedCovariateProducer
reverseComparator routingDifferencePersistsAfterConditioning = conditionedComparatorProducer
reverseComparator identityOrPoliticalProvenanceAffectedRouting = classificationDecisionProvenanceProducer
reverseComparator ideologicalMotiveClosed = motiveProducer

record ComparatorCutset : Set where
  constructor comparatorCutset
  field
    routingClosed : Bool
    securityNeedClosed : Bool
    conditionedComparisonClosed : Bool
    classificationProvenanceClosed : Bool
    motiveClosed : Bool
    cutsetReference : String

open ComparatorCutset public

data ComparatorResidual : Set where
  routingResidual : ComparatorResidual
  securityNeedResidual : ComparatorResidual
  conditionedComparisonResidual : ComparatorResidual
  classificationProvenanceResidual : ComparatorResidual
  motiveResidual : ComparatorResidual
  comparatorClosed : ComparatorResidual

firstComparatorResidual : ComparatorClaim → ComparatorCutset → ComparatorResidual
firstComparatorResidual protectiveCoerciveRoutingDiffers c with routingClosed c
... | false = routingResidual
... | true = comparatorClosed
firstComparatorResidual eventsComparableOnSecurityNeed c with securityNeedClosed c
... | false = securityNeedResidual
... | true = comparatorClosed
firstComparatorResidual routingDifferencePersistsAfterConditioning c with routingClosed c
... | false = routingResidual
... | true with securityNeedClosed c
...   | false = securityNeedResidual
...   | true with conditionedComparisonClosed c
...     | false = conditionedComparisonResidual
...     | true = comparatorClosed
firstComparatorResidual identityOrPoliticalProvenanceAffectedRouting c with conditionedComparisonClosed c
... | false = conditionedComparisonResidual
... | true with classificationProvenanceClosed c
...   | false = classificationProvenanceResidual
...   | true = comparatorClosed
firstComparatorResidual ideologicalMotiveClosed c with classificationProvenanceClosed c
... | false = classificationProvenanceResidual
... | true with motiveClosed c
...   | false = motiveResidual
...   | true = comparatorClosed

canonicalObservedRoutingOnly : ComparatorCutset
canonicalObservedRoutingOnly = comparatorCutset
  true false false false false
  "routing surfaces partly observable; comparability, conditioned effect, classification provenance and motive remain open"

routingDifferenceDoesNotSkipComparability :
  firstComparatorResidual routingDifferencePersistsAfterConditioning canonicalObservedRoutingOnly
  ≡ securityNeedResidual
routingDifferenceDoesNotSkipComparability = refl

------------------------------------------------------------------------
-- Fascism and coloniality x-pollination: asymmetric routing is a testable
-- mechanism, not a diagnosis.  Political-content erasure is likewise an audit
-- target rather than proof of intent.
------------------------------------------------------------------------

asymmetricRoutingMechanism : Coloniality.PolicingMechanism
asymmetricRoutingMechanism =
  Coloniality.featureToPolicingMechanism Fascism.asymmetricRouting

record ComparatorCrossPollinationBoundary : Set where
  constructor comparatorCrossPollinationBoundary
  field
    protectiveCoerciveDifferenceImpliesFascism : Bool
    protectiveCoerciveDifferenceImpliesFascismIsFalse : protectiveCoerciveDifferenceImpliesFascism ≡ false
    differentPoliticalIdentityImpliesIdentityCausedRouting : Bool
    differentPoliticalIdentityImpliesIdentityCausedRoutingIsFalse : differentPoliticalIdentityImpliesIdentityCausedRouting ≡ false
    highSecurityIntensityImpliesSameSecurityNeed : Bool
    highSecurityIntensityImpliesSameSecurityNeedIsFalse : highSecurityIntensityImpliesSameSecurityNeed ≡ false
    securityClassificationExhaustsPoliticalMeaning : Bool
    securityClassificationExhaustsPoliticalMeaningIsFalse : securityClassificationExhaustsPoliticalMeaning ≡ false
    protectiveRoutingIsNecessarilyLawful : Bool
    protectiveRoutingIsNecessarilyLawfulIsFalse : protectiveRoutingIsNecessarilyLawful ≡ false
    coerciveRoutingIsNecessarilyUnlawful : Bool
    coerciveRoutingIsNecessarilyUnlawfulIsFalse : coerciveRoutingIsNecessarilyUnlawful ≡ false

canonicalComparatorCrossPollinationBoundary : ComparatorCrossPollinationBoundary
canonicalComparatorCrossPollinationBoundary =
  comparatorCrossPollinationBoundary
    false refl false refl false refl false refl false refl false refl
