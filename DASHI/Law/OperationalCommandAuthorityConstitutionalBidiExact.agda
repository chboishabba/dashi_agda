module DASHI.Law.OperationalCommandAuthorityConstitutionalBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.ConstitutionalValidityLawfulnessCrossPollinationExact as Constitutional
import DASHI.Law.OperationalDirectionProvenanceBidiExact as Direction
import DASHI.Governance.AuthorityPhaseSeparationExact as Phase
import DASHI.Law.JarrettPostBondiConstitutionalSourceReceiptsExact as Jarrett

------------------------------------------------------------------------
-- Operational-command authority is a provenance fibre, not a Boolean.
------------------------------------------------------------------------

data CommandAuthorityState : Set where
  commandAuthorityClosed commandAuthorityOpen : CommandAuthorityState

record CommandAuthorityFibre : Set where
  constructor commandAuthorityFibre
  field
    powerReference : String
    applicableLaw : Constitutional.ApplicableLawReceipt
    constitutionalValidity : Constitutional.ConstitutionalValidityReceipt
    issuerCompetenceState : CommandAuthorityState
    issuerReference : String
    phase : Phase.InterventionPhase
    phaseAuthorityRole : Phase.PhaseAuthorityRole
    phaseRoleExact : phaseAuthorityRole ≡ Phase.phaseAuthorityRole phase
    scopeState : CommandAuthorityState
    scopeReference : String
    authorityReference : String

open CommandAuthorityFibre public

record CommandWithAuthority : Set where
  constructor commandWithAuthority
  field
    direction : Direction.OperationalDirectionFibre
    authorityFibre : CommandAuthorityFibre
    commandReference : String

open CommandWithAuthority public

------------------------------------------------------------------------
-- Strong authority closure requires all authority coordinates.
------------------------------------------------------------------------

data CommandAuthorityCoordinate : Set where
  powerCoordinate applicableLawCoordinate constitutionalValidityCoordinate
  issuerCompetenceCoordinate phaseCoordinate scopeCoordinate : CommandAuthorityCoordinate

data CoordinateState : Set where
  closed open : CoordinateState

record CommandAuthorityVector : Set where
  constructor commandAuthorityVector
  field
    powerState applicableLawState validityState issuerState phaseState scopeStateVector : CoordinateState

open CommandAuthorityVector public

data CommandAuthorityResult : Set where
  commandAuthorityAllClosed : CommandAuthorityResult
  firstOpenCommandAuthority : CommandAuthorityCoordinate → CommandAuthorityResult

firstOpenCommandAuthorityCoordinate : CommandAuthorityVector → CommandAuthorityResult
firstOpenCommandAuthorityCoordinate v with powerState v
... | open = firstOpenCommandAuthority powerCoordinate
... | closed with applicableLawState v
...   | open = firstOpenCommandAuthority applicableLawCoordinate
...   | closed with validityState v
...     | open = firstOpenCommandAuthority constitutionalValidityCoordinate
...     | closed with issuerState v
...       | open = firstOpenCommandAuthority issuerCompetenceCoordinate
...       | closed with phaseState v
...         | open = firstOpenCommandAuthority phaseCoordinate
...         | closed with scopeStateVector v
...           | open = firstOpenCommandAuthority scopeCoordinate
...           | closed = commandAuthorityAllClosed

------------------------------------------------------------------------
-- Jarrett regression: text/power/applicability may be known while the
-- constitutional producer is invalid/open for lawful-authority promotion.
------------------------------------------------------------------------

jarrettCommandAuthorityVector : CommandAuthorityVector
jarrettCommandAuthorityVector =
  commandAuthorityVector closed closed open open open open

jarrettCommandStopsAtValidity :
  firstOpenCommandAuthorityCoordinate jarrettCommandAuthorityVector
  ≡ firstOpenCommandAuthority constitutionalValidityCoordinate
jarrettCommandStopsAtValidity = refl

jarrettInvalidCommandValidity : Constitutional.ConstitutionalValidityReceipt
jarrettInvalidCommandValidity = Constitutional.jarrettInvalidityReceipt

------------------------------------------------------------------------
-- Reverse routing from downstream command claims to upstream producers.
------------------------------------------------------------------------

data CommandAuthorityClaim : Set where
  commandDocumentExisted
  commandHadValidLegalProducer
  commandIssuerWasCompetent
  commandWasWithinPhaseAuthority
  commandWasWithinScope
  commandGovernedFieldActionLawfully : CommandAuthorityClaim

data CommandAuthorityProducer : Set where
  commandDocumentProducer
  applicableLawAndValidityProducer
  issuerCompetenceProducer
  phaseAuthorityProducer
  scopeProducer
  executionProvenanceProducer : CommandAuthorityProducer

reverseCommandAuthority : CommandAuthorityClaim → CommandAuthorityProducer
reverseCommandAuthority commandDocumentExisted = commandDocumentProducer
reverseCommandAuthority commandHadValidLegalProducer = applicableLawAndValidityProducer
reverseCommandAuthority commandIssuerWasCompetent = issuerCompetenceProducer
reverseCommandAuthority commandWasWithinPhaseAuthority = phaseAuthorityProducer
reverseCommandAuthority commandWasWithinScope = scopeProducer
reverseCommandAuthority commandGovernedFieldActionLawfully = executionProvenanceProducer

------------------------------------------------------------------------
-- Cross-pollination with the operational direction chain.
------------------------------------------------------------------------

record CommandExecutionCutset : Set where
  constructor commandExecutionCutset
  field
    commandDocumentClosed : Bool
    commandAuthorityClosedCutset : Bool
    transmissionClosed : Bool
    fieldReceiptClosed : Bool
    civilianDirectionClosed : Bool
    executionClosed : Bool
    cutsetReference : String

open CommandExecutionCutset public

data CommandExecutionResidual : Set where
  documentResidual authorityResidual transmissionResidual fieldReceiptResidual
  civilianDirectionResidual executionResidual executionClosedResult : CommandExecutionResidual

firstCommandExecutionResidual : CommandExecutionCutset → CommandExecutionResidual
firstCommandExecutionResidual c with commandDocumentClosed c
... | false = documentResidual
... | true with commandAuthorityClosedCutset c
...   | false = authorityResidual
...   | true with transmissionClosed c
...     | false = transmissionResidual
...     | true with fieldReceiptClosed c
...       | false = fieldReceiptResidual
...       | true with civilianDirectionClosed c
...         | false = civilianDirectionResidual
...         | true with executionClosed c
...           | false = executionResidual
...           | true = executionClosedResult

canonicalCommandKnownAuthorityOpen : CommandExecutionCutset
canonicalCommandKnownAuthorityOpen = commandExecutionCutset
  true false false false false false
  "command document known; legal producer remains open"

commandDocumentCannotLeapfrogAuthority :
  firstCommandExecutionResidual canonicalCommandKnownAuthorityOpen ≡ authorityResidual
commandDocumentCannotLeapfrogAuthority = refl

------------------------------------------------------------------------
-- Source attribution: a court holding about invalidity is not attributed to
-- police, plaintiffs, government, or DASHI.
------------------------------------------------------------------------

jarrettRolePreserved :
  Constitutional.sourceRole jarrettInvalidCommandValidity ≡ Jarrett.courtHolding
jarrettRolePreserved = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record CommandAuthorityBoundary : Set where
  constructor commandAuthorityBoundary
  field
    commandExistsImpliesValidAuthority : Bool
    commandExistsImpliesValidAuthorityIsFalse : commandExistsImpliesValidAuthority ≡ false
    validAuthorityImpliesLawfulExecution : Bool
    validAuthorityImpliesLawfulExecutionIsFalse : validAuthorityImpliesLawfulExecution ≡ false
    constitutionallyValidPowerImpliesIssuerCompetent : Bool
    constitutionallyValidPowerImpliesIssuerCompetentIsFalse : constitutionallyValidPowerImpliesIssuerCompetent ≡ false
    phaseAuthorityImpliesScopeSatisfied : Bool
    phaseAuthorityImpliesScopeSatisfiedIsFalse : phaseAuthorityImpliesScopeSatisfied ≡ false
    invalidOneProducerImpliesEveryPossibleCommandAuthorityInvalid : Bool
    invalidOneProducerImpliesEveryPossibleCommandAuthorityInvalidIsFalse : invalidOneProducerImpliesEveryPossibleCommandAuthorityInvalid ≡ false

canonicalCommandAuthorityBoundary : CommandAuthorityBoundary
canonicalCommandAuthorityBoundary =
  commandAuthorityBoundary false refl false refl false refl false refl false refl
