module DASHI.GameTheory.GameTheoryIntrospectiveCompletionCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.GameTheory.GameTheoryCompletionFrontierExact as Frontier
import DASHI.GameTheory.FiniteMixedNashProductCorrectionExact as Correction
import DASHI.GameTheory.TernaryLifeStrategicKernelBridgeExact as TernaryLife

------------------------------------------------------------------------
-- INTROSPECTIVE COMPLETION CUT
--
-- Recent-repository x-pollination applied here:
--   * RH #847: consumer-minimal versus producer-useful theorem surfaces;
--   * CS #851: source status and proof-debt routing remain distinct;
--   * YM #849: lift/reuse an owned theorem rather than replaying local proof.
--
-- Applied to game theory, this exposed a real defect before theorem search:
-- arbitrary normalized profile law != independent product mixed strategy law.
-- The correction owner repairs that consumer.  The old Ternary-Life owner then
-- supplies an actually inhabited pure-Nash regression through a thin adapter.
------------------------------------------------------------------------

frontier : Frontier.GameTheoryCompletionFrontier
frontier = Frontier.canonicalGameTheoryCompletionFrontier

mixedCorrectionBoundary : Correction.FiniteMixedNashCorrectionBoundary
mixedCorrectionBoundary = Correction.canonicalFiniteMixedNashCorrectionBoundary

ternaryLifeBoundary : TernaryLife.TernaryLifeStrategicBridgeBoundary
ternaryLifeBoundary = TernaryLife.canonicalTernaryLifeStrategicBridgeBoundary

------------------------------------------------------------------------
-- Exact surviving producer class for the standard finite mixed-Nash theorem.
------------------------------------------------------------------------

data MixedNashExistenceResidual : Set where
  missingIndependentProductSourceAlignment
  missingFiniteSimplexRealisation
  missingNashFixedPointTheoremTranscription
  missingExactGameInstantiation
  missingKernelCertification : MixedNashExistenceResidual

producerClass : MixedNashExistenceResidual → Debt.DebtClass
producerClass missingIndependentProductSourceAlignment = Debt.transcriptionDebt
producerClass missingFiniteSimplexRealisation = Debt.transcriptionDebt
producerClass missingNashFixedPointTheoremTranscription = Debt.transcriptionDebt
producerClass missingExactGameInstantiation = Debt.mathematicalDebt
producerClass missingKernelCertification = Debt.certificationDebt

nashFixedPointTheoremRoute : Debt.ProofDebtRoutingReceipt
nashFixedPointTheoremRoute = Correction.finiteMixedNashExistenceDebt

nashFixedPointNextAction :
  Debt.scheduleAction
    (Debt.routedDebt nashFixedPointTheoremRoute)
    (Debt.statementStatus nashFixedPointTheoremRoute)
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.auditTranscription
nashFixedPointNextAction = Correction.finiteMixedNashExistenceNextAction

------------------------------------------------------------------------
-- Firewalls for tempting but invalid repository reuse.
------------------------------------------------------------------------

data DomainFixedPointMeansNashFixedPointPermission : Set where

data PureNashFixtureMeansGeneralMixedExistencePermission : Set where

data CorrectedConsumerMeansProducerExistsPermission : Set where

data SourceCitationMeansExactInstantiationPermission : Set where

unrelatedDomainFixedPointsDoNotPayNashExistence :
  DomainFixedPointMeansNashFixedPointPermission → ⊥
unrelatedDomainFixedPointsDoNotPayNashExistence ()

ternaryLifeFixtureDoesNotProveGeneralMixedExistence :
  PureNashFixtureMeansGeneralMixedExistencePermission → ⊥
ternaryLifeFixtureDoesNotProveGeneralMixedExistence ()

correctConsumerDoesNotManufactureFixedPointProducer :
  CorrectedConsumerMeansProducerExistsPermission → ⊥
correctConsumerDoesNotManufactureFixedPointProducer ()

sourceCitationDoesNotInstantiateExactGame :
  SourceCitationMeansExactInstantiationPermission → ⊥
sourceCitationDoesNotInstantiateExactGame ()

record GameTheoryIntrospectiveCut : Set where
  constructor game-theory-introspective-cut
  field
    oldJointLawIndependenceDefectExposed : Bool
    correctedStandardMixedNashConsumerClosed : Bool
    ternaryLifePureNashRegressionInhabited : Bool
    cooperativeMechanismIdentificationCheckerIntegrated : Bool
    brouwerKakutaniSpernerOwnerLocatedInRepo : Bool
    domainSpecificFixedPointMaySubstitute : Bool
    standardNashExistenceStillNeedsTranscriptionAlignment : Bool
    exactGameInstantiationStillSeparate : Bool
    kernelCertificationObtainedHere : Bool

canonicalGameTheoryIntrospectiveCut : GameTheoryIntrospectiveCut
canonicalGameTheoryIntrospectiveCut =
  game-theory-introspective-cut
    true true true true false false true true false
