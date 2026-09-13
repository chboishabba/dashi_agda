module DASHI.Empirical.DarkDimensionResidualDebtRoutingExact where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ProofDebtRouterExact as ProofDebt
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SourceSearch
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Empirical.DarkDimensionDAOSameKeyReconstructionRunExact as DAORun
import DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact as BedroyaManifest

------------------------------------------------------------------------
-- RESIDUAL DEBT ROUTING THROUGH EXISTING PARENTS
--
-- Do not collapse the current blockers into one scalar "unfinished" status.
-- The formal DAO statement is derived-in-repo and still uncertified, while the
-- requested numerical DAO execution has no runtime receipt.  Bedroya is
-- blocked earlier: the exact same-object numerical manifest is not located.
------------------------------------------------------------------------

daoFormalCertificationRoute :
  ProofDebt.routeDebt
    ProofDebt.deductiveTheorem
    ProofDebt.derivedInRepo
    ProofDebt.sourceAligned
    ProofDebt.uncertified
  ≡ ProofDebt.certificationDebt
daoFormalCertificationRoute = refl

daoExecutionStillOpen :
  DAORun.executionReceiptPresent
    DAORun.canonicalDAOSameKeyReconstructionRunStatus
  ≡ false
daoExecutionStillOpen = DAORun.reconstructionRunStillOpen

bedroyaFirstMissingSourceCoordinate : SourceSearch.SourceDiligenceGap
bedroyaFirstMissingSourceCoordinate = SourceSearch.sameObjectUnresolved

bedroyaSameObjectGapRoutesToIdentityProducer :
  SourceSearch.producerForSourceDiligenceGap
    bedroyaFirstMissingSourceCoordinate
  ≡ Search.identityProducer
bedroyaSameObjectGapRoutesToIdentityProducer = refl

bedroyaAcquisitionStillOpen :
  BedroyaManifest.exactStandardBestFitTuplePublished
    BedroyaManifest.canonicalBedroyaParameterManifestStatus
  ≡ false
bedroyaAcquisitionStillOpen = BedroyaManifest.exactStandardTupleStillOpen

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data DAOExecutionPaysBedroyaAcquisitionGap : Set where

data CertificationPaysMissingSourceIdentity : Set where

daoExecutionCannotPayBedroyaAcquisitionGap :
  DAOExecutionPaysBedroyaAcquisitionGap → ⊥
daoExecutionCannotPayBedroyaAcquisitionGap ()

certificationCannotPayMissingSourceIdentity :
  CertificationPaysMissingSourceIdentity → ⊥
certificationCannotPayMissingSourceIdentity ()

-- Alias used by downstream debt graphs: the residuals are independently
-- payable and cannot be collapsed by completing only the DAO execution lane.
residualKindsRemainDistinct :
  DAOExecutionPaysBedroyaAcquisitionGap → ⊥
residualKindsRemainDistinct = daoExecutionCannotPayBedroyaAcquisitionGap
