module DASHI.Cognition.PNF.SensibLawGenocideConventionWrongTypeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawCountryRelationalLossGenocideBoundaryExact as Genocide
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as ElementAlgebra

------------------------------------------------------------------------
-- Genocide Convention as a proper WrongType fibre.
--
-- This owner does not decide that any event is genocide.  It supplies the
-- Convention wrong type, its three classification axes, and reverse routes when
-- one axis remains open/unsatisfied.  Failure of this narrow WrongType must not
-- erase other legal, relational or critical classifications.
------------------------------------------------------------------------

genocideConventionSystemId : Ontology.StableId
genocideConventionSystemId = Ontology.stableId "INTL.GENOCIDE-CONVENTION.1948"

genocideConventionSourceId : Ontology.StableId
genocideConventionSourceId = Ontology.stableId "source:UN:GenocideConvention:1948"

groupExistenceInterestId : Ontology.StableId
groupExistenceInterestId = Ontology.stableId "interest:group-existence-and-continuity"

genocideHarmClassId : Ontology.StableId
genocideHarmClassId = Ontology.stableId "harm:destruction-group-whole-or-part"

preventionRemedyId : Ontology.StableId
preventionRemedyId = Ontology.stableId "remedy:genocide:prevent"

punishmentRemedyId : Ontology.StableId
punishmentRemedyId = Ontology.stableId "remedy:genocide:punish"

reparationRemedyId : Ontology.StableId
reparationRemedyId = Ontology.stableId "remedy:state-responsibility:reparation"

genocideConventionWrongType : Ontology.WrongType
genocideConventionWrongType = Ontology.wrongTypeRecord
  (Ontology.stableId "wrong:intl:genocide-convention")
  genocideConventionSystemId
  (genocideConventionSourceId ∷ [])
  (groupExistenceInterestId ∷ [])
  []
  []
  Ontology.intentional
  (genocideHarmClassId ∷ [])
  []
  (preventionRemedyId ∷ punishmentRemedyId ∷ reparationRemedyId ∷ [])

------------------------------------------------------------------------
-- Three-axis Convention classifier.
------------------------------------------------------------------------

data ConventionElementAxis : Set where
  protectedGroupAxis
  enumeratedActAxis
  specificIntentAxis
  : ConventionElementAxis

data ElementState : Set where
  elementSatisfied
  elementFailed
  elementOpen
  : ElementState

axisLegalElementKind : ConventionElementAxis → ElementAlgebra.LegalElementKind
axisLegalElementKind protectedGroupAxis = ElementAlgebra.statutoryElement
axisLegalElementKind enumeratedActAxis = ElementAlgebra.statutoryElement
axisLegalElementKind specificIntentAxis = ElementAlgebra.mentalStateElement

specificIntentIsMentalStateElement :
  axisLegalElementKind specificIntentAxis ≡ ElementAlgebra.mentalStateElement
specificIntentIsMentalStateElement = refl

record ConventionElementState : Set where
  constructor convention-element-state
  field
    protectedGroupState : ElementState
    enumeratedActState : ElementState
    specificIntentState : ElementState
    sourceReference : String
    evaluatorReference : String

open ConventionElementState public

data ConventionWrongTypeStatus : Set where
  conventionWrongTypeClosed
  conventionWrongTypeOpen
  conventionWrongTypeRejectedOnCurrentRecord
  : ConventionWrongTypeStatus

classifyConventionWrongType : ConventionElementState → ConventionWrongTypeStatus
classifyConventionWrongType receipt with protectedGroupState receipt
... | elementFailed = conventionWrongTypeRejectedOnCurrentRecord
... | elementOpen = conventionWrongTypeOpen
... | elementSatisfied with enumeratedActState receipt
...   | elementFailed = conventionWrongTypeRejectedOnCurrentRecord
...   | elementOpen = conventionWrongTypeOpen
...   | elementSatisfied with specificIntentState receipt
...     | elementFailed = conventionWrongTypeRejectedOnCurrentRecord
...     | elementOpen = conventionWrongTypeOpen
...     | elementSatisfied = conventionWrongTypeClosed

------------------------------------------------------------------------
-- Exact bridge to the existing Genocide Convention owner.
------------------------------------------------------------------------

record ConventionElementBridge : Set where
  constructor convention-element-bridge
  field
    wrongType : Ontology.WrongType
    protectedGroupOwner : String
    enumeratedActOwner : String
    specificIntentOwner : String
    sameConventionSource : Bool
    sameConventionSourceIsTrue : sameConventionSource ≡ true

open ConventionElementBridge public

genocideConventionElementBridge : ConventionElementBridge
genocideConventionElementBridge = convention-element-bridge
  genocideConventionWrongType
  "SensibLawCountryRelationalLossGenocideBoundaryExact.ProtectedGroupKind"
  "SensibLawCountryRelationalLossGenocideBoundaryExact.ConventionAct"
  "SensibLawCountryRelationalLossGenocideBoundaryExact.GroupDestructionIntent"
  true refl

------------------------------------------------------------------------
-- Reverse/BIDI classification search.
--
-- A failed/open Convention element schedules another classification inquiry;
-- it does not manufacture the alternate wrong.
------------------------------------------------------------------------

data AlternativeClassificationTarget : Set where
  iccprHumanRightsViolationCandidate
  crimesAgainstHumanityCandidate
  forcibleChildTransferGenocideInquiryFindingLane
  domesticStatutoryOrCommonLawWrongCandidate
  decolonialCulturalGenocideCriticalLane
  countryRelationalDestructionLane
  : AlternativeClassificationTarget

data RouteAuthority : Set where
  legalWrongTypeSearch
  institutionalFindingSearch
  criticalInterpretiveSearch
  relationalHarmSearch
  : RouteAuthority

record WrongTypeReverseRoute : Set where
  constructor wrong-type-reverse-route
  field
    triggerAxis : ConventionElementAxis
    triggerState : ElementState
    target : AlternativeClassificationTarget
    authority : RouteAuthority
    targetAlreadyEstablished : Bool
    targetAlreadyEstablishedIsFalse : targetAlreadyEstablished ≡ false
    routeReference : String

open WrongTypeReverseRoute public

intentFailureToHumanRightsRoute : WrongTypeReverseRoute
intentFailureToHumanRightsRoute = wrong-type-reverse-route
  specificIntentAxis elementFailed
  iccprHumanRightsViolationCandidate
  legalWrongTypeSearch
  false refl
  "failure to prove dolus specialis does not erase separately elemented ICCPR/human-rights inquiries"

culturalLossToRelationalRoute : WrongTypeReverseRoute
culturalLossToRelationalRoute = wrong-type-reverse-route
  enumeratedActAxis elementOpen
  countryRelationalDestructionLane
  relationalHarmSearch
  false refl
  "irreversible Country/relation/transmission loss remains independently classifiable even where Convention act/intent closure is absent"

culturalLossToCriticalGenocideRoute : WrongTypeReverseRoute
culturalLossToCriticalGenocideRoute = wrong-type-reverse-route
  enumeratedActAxis elementOpen
  decolonialCulturalGenocideCriticalLane
  criticalInterpretiveSearch
  false refl
  "decolonial cultural-genocide lens is an explicit critical classification and is not the Convention wrong type"

childTransferToBTHRoute : WrongTypeReverseRoute
childTransferToBTHRoute = wrong-type-reverse-route
  enumeratedActAxis elementSatisfied
  forcibleChildTransferGenocideInquiryFindingLane
  institutionalFindingSearch
  false refl
  "Bringing Them Home source-specific genocide finding is independently attributed and is not automatically a criminal conviction"

------------------------------------------------------------------------
-- BIDI demand: what must be produced to close the Convention WrongType?
------------------------------------------------------------------------

data ConventionProducerNeed : Set where
  produceProtectedGroupReceipt
  produceEnumeratedActReceipt
  produceSpecificIntentReceipt
  : ConventionProducerNeed

firstMissingProducer : ConventionElementState → ConventionProducerNeed
firstMissingProducer receipt with protectedGroupState receipt
... | elementFailed = produceProtectedGroupReceipt
... | elementOpen = produceProtectedGroupReceipt
... | elementSatisfied with enumeratedActState receipt
...   | elementFailed = produceEnumeratedActReceipt
...   | elementOpen = produceEnumeratedActReceipt
...   | elementSatisfied = produceSpecificIntentReceipt

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data ConventionGenocideFailureMeansNoWrongOccurred : Set where
data CulturalDestructionAutomaticallySatisfiesEnumeratedAct : Set where
data POSIWIDAutomaticallySatisfiesSpecificIntent : Set where
data BringingThemHomeFindingAutomaticallyCreatesCriminalConviction : Set where
data AlternativeRouteAutomaticallyEstablishesAlternativeWrong : Set where

data WrongTypeIdentityAutomaticallyProvesAllElements : Set where

data ElementClosureAutomaticallyChoosesForum : Set where

conventionFailureDoesNotMeanNoWrong :
  ConventionGenocideFailureMeansNoWrongOccurred → ⊥
conventionFailureDoesNotMeanNoWrong ()

culturalDestructionDoesNotAutoPayConventionAct :
  CulturalDestructionAutomaticallySatisfiesEnumeratedAct → ⊥
culturalDestructionDoesNotAutoPayConventionAct ()

posiwidDoesNotAutoPayDolusSpecialis :
  POSIWIDAutomaticallySatisfiesSpecificIntent → ⊥
posiwidDoesNotAutoPayDolusSpecialis ()

bringingThemHomeDoesNotAutoBecomeConviction :
  BringingThemHomeFindingAutomaticallyCreatesCriminalConviction → ⊥
bringingThemHomeDoesNotAutoBecomeConviction ()

reverseRouteDoesNotEstablishDestination :
  AlternativeRouteAutomaticallyEstablishesAlternativeWrong → ⊥
reverseRouteDoesNotEstablishDestination ()

wrongTypeIdentityDoesNotProveElements :
  WrongTypeIdentityAutomaticallyProvesAllElements → ⊥
wrongTypeIdentityDoesNotProveElements ()

elementClosureDoesNotChooseForum : ElementClosureAutomaticallyChoosesForum → ⊥
elementClosureDoesNotChooseForum ()

------------------------------------------------------------------------
-- Existing owner remains the legal-definition authority surface.
------------------------------------------------------------------------

bringingThemHomeSourceSpecificConventionStatus : Genocide.GenocideLegalStatus
bringingThemHomeSourceSpecificConventionStatus =
  Genocide.status Genocide.bringingThemHomeGenocideFinding
