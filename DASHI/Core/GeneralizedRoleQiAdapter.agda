module DASHI.Core.GeneralizedRoleQiAdapter where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole
open import DASHI.Core.ProofLens
import DASHI.Culture.QiOperatorTheoryBoundary as Qi

-- This adapter consumes the existing Qi role catalogue rather than inventing a
-- second toy Qi ontology.  Payloads remain the existing boundary objects.
QiGeneralizedRole : FormalRole → Set
QiGeneralizedRole carrierSpaceRole    = Qi.QiRoleCategory
QiGeneralizedRole stateRole           = Qi.QiRoleCategory
QiGeneralizedRole operatorRole        = Qi.OperatorFamily
QiGeneralizedRole observableRole      = Qi.QiRoleCategory
QiGeneralizedRole spectrumToolRole    = Qi.OperatorFamily
QiGeneralizedRole boundaryGateRole    = Qi.OperatorFamily
QiGeneralizedRole obstructionRole     = Qi.OperatorFamily
QiGeneralizedRole algebraRole         = Qi.OperatorFamily
QiGeneralizedRole proofObligationRole = Qi.OperatorFamily
QiGeneralizedRole decompositionRole   = Qi.OperatorFamily
QiGeneralizedRole hamiltonianRole     = Qi.QiRoleCategory
QiGeneralizedRole metricRole          = Qi.QiRoleCategory
QiGeneralizedRole projectionRole      = Qi.OperatorFamily
QiGeneralizedRole residualRole        = Qi.QiRoleCategory
QiGeneralizedRole receiptRole         = Qi.QiRoleCoreAlignmentRow
QiGeneralizedRole functorRole         = Qi.OperatorFamily
QiGeneralizedRole transitionRole      = Qi.OperatorFamily
QiGeneralizedRole invariantRole       = Qi.QiRoleCategory
QiGeneralizedRole symmetryRole        = Qi.OperatorFamily
QiGeneralizedRole modeRole            = Qi.QiRoleCategory
QiGeneralizedRole sourceRole          = Qi.QiRoleCategory
QiGeneralizedRole sinkRole            = Qi.QiRoleCategory
QiGeneralizedRole flowRole            = Qi.OperatorFamily
QiGeneralizedRole constraintRole      = Qi.QiRoleCategory
QiGeneralizedRole remedyRole          = Qi.OperatorFamily

qiGeneralizedDomain : RoleFamily
qiGeneralizedDomain =
  record
    { Carrier  = Qi.QiRoleCategory
    ; RoleType = QiGeneralizedRole
    }

-- The existing catalogue computes its shared role explicitly.  This bridge
-- preserves that computation without promoting the cultural reading.
qiCategoryToRole : Qi.QiRoleCategory → FormalRole
qiCategoryToRole Qi.QiStateSpace       = carrierSpaceRole
qiCategoryToRole Qi.QiOperator         = operatorRole
qiCategoryToRole Qi.QiObservable       = observableRole
qiCategoryToRole Qi.QiSpectrumTool     = spectrumToolRole
qiCategoryToRole Qi.QiBoundaryGate     = boundaryGateRole
qiCategoryToRole Qi.QiObstruction      = obstructionRole
qiCategoryToRole Qi.QiAlgebra          = algebraRole
qiCategoryToRole Qi.QiProofObligation  = proofObligationRole
qiCategoryToRole Qi.QiDecomposition    = decompositionRole
qiCategoryToRole Qi.HistoricalMetadata = receiptRole

record QiAdapterEvidence : Set where
  constructor qiAdapterEvidence
  field
    sourceRow : Qi.QiRoleCoreAlignmentRow

qiAlignmentTerm : Qi.QiRoleCoreAlignmentRow → TypedTerm QiAdapterEvidence
qiAlignmentTerm row =
  record
    { domain   = qiGeneralizedDomain
    ; role     = receiptRole
    ; evidence = qiAdapterEvidence row
    ; payload  = row
    }

-- Operator-family lens witnesses are role-indexed claims about the existing
-- catalogue.  They do not assert analytic operator theorems.
data QiOperatorLensWitness :
  ProofLens →
  (r : FormalRole) →
  QiGeneralizedRole r →
  Set where
  qiSpectralCatalogueWitness :
    (op : Qi.OperatorFamily) →
    QiOperatorLensWitness spectralLens spectrumToolRole op

  qiCategoryCatalogueWitness :
    (op : Qi.OperatorFamily) →
    QiOperatorLensWitness categoryLens operatorRole op

qiGeneralizedLenses : LensFamily qiGeneralizedDomain
qiGeneralizedLenses = record { LensWitness = QiOperatorLensWitness }
