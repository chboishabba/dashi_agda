module DASHI.Governance.LegalDecisionCrossPollinationRegression where

------------------------------------------------------------------------
-- Focused kernel surface for the decision -> expression -> institutional
-- projection / legal-authority cross-pollination.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.DecisionPotentialAuthorityOrthogonalityExact as PotentialAuthority
import DASHI.Governance.LegalDecisionDoubleProjectionExact as Legal
import DASHI.Governance.LegalDecisionFibreDynamicsExact as Dynamics

-- Official outcome cannot reconstruct the selected fine decision+authority
-- state.
officialSurfaceNonfactorabilityRegression :
  NF.FactorsThrough Legal.officialSurface Legal.fineLegalStateOf → ⊥
officialSurfaceNonfactorabilityRegression =
  Legal.officialSurfaceCannotRecoverFineLegalState

-- Neither residual axis alone suffices.
decisionResidualInsufficientRegression :
  NF.FactorsThrough Legal.decisionResidualSurface Legal.fineLegalStateOf → ⊥
decisionResidualInsufficientRegression =
  Legal.decisionResidualAloneCannotRecoverFineLegalState

authorityResidualInsufficientRegression :
  NF.FactorsThrough Legal.authorityResidualSurface Legal.fineLegalStateOf → ⊥
authorityResidualInsufficientRegression =
  Legal.authorityResidualAloneCannotRecoverFineLegalState

-- Their typed pair is the least common observational refinement and the joined
-- residual is sufficient for the deliberately selected FineLegalState.
joinedResidualSufficiencyRegression :
  NF.FactorsThrough Legal.joinedResidualSurface Legal.fineLegalStateOf
joinedResidualSufficiencyRegression =
  Legal.joinedResidualRecoversChosenFineLegalState

-- Potential pressure and legal authority cannot decode one another.
potentialCannotIssueAuthorityRegression :
  NF.FactorsThrough
    PotentialAuthority.potentialReadout
    PotentialAuthority.authorityReadout → ⊥
potentialCannotIssueAuthorityRegression =
  PotentialAuthority.potentialCannotIssueAuthority

authorityCannotDeterminePotentialRegression :
  NF.FactorsThrough
    PotentialAuthority.authorityReadout
    PotentialAuthority.potentialReadout → ⊥
authorityCannotDeterminePotentialRegression =
  PotentialAuthority.authorityDoesNotDetermineObserverPotential

-- Hidden decision and authority updates are both fibre-preserving but order
-- sensitive.
hiddenUpdateOrderRegression :
  Dynamics.decisionAfterAuthorityAtBlocked
  ≡ Dynamics.authorityAfterDecisionAtBlocked → ⊥
hiddenUpdateOrderRegression =
  Dynamics.hiddenMotionsDoNotCommuteAtBlocked

hiddenOrdersShareOfficialEndpointRegression :
  Dynamics.witnessOfficialSurface Dynamics.decisionAfterAuthorityAtBlocked
  ≡ Dynamics.witnessOfficialSurface Dynamics.authorityAfterDecisionAtBlocked
hiddenOrdersShareOfficialEndpointRegression =
  Dynamics.bothCompositeOrdersRemainOfficiallyInvisible
