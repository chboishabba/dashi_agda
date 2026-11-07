module DASHI.Cognition.CCDCOEPersonalHolonomyBoundaryExact where

-- Finite context-transport / loop-holonomy interpretation of the authors'
-- second CCDCOE 2026 article on the human agent. It is not a measured
-- psychological mechanism or causal evidence of hostile influence.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.CCDCOECognitiveMultiplexInvariantExact as Group

data Context : Set where
  privateContext : Context
  professionalContext : Context
  civicContext : Context

data InnerState : Set where
  baselineState : InnerState
  revisedState : InnerState

data Connection : Set where
  identityConnection : Connection
  revisedConnection : Connection

-- Toy transport of an internal state between social contexts. The selected
-- revised edge is transparent; no physics connection/holonomy is imported.
transport : Connection → Context → Context → InnerState → InnerState
transport identityConnection _ _ state = state
transport revisedConnection privateContext professionalContext baselineState =
  revisedState
transport revisedConnection _ _ state = state

-- A closed *context* loop need not be an identity on the transported state.
holonomy : Connection → InnerState → InnerState
holonomy connection state =
  transport connection civicContext privateContext
    (transport connection professionalContext civicContext
      (transport connection privateContext professionalContext state))

identityLoopPreservesState :
  (state : InnerState) →
  holonomy identityConnection state ≡ state
identityLoopPreservesState _ = refl

revisedLoopChangesSelectedState :
  holonomy revisedConnection baselineState ≡ revisedState
revisedLoopChangesSelectedState = refl

revisedIsNotBaseline : revisedState ≡ baselineState → ⊥
revisedIsNotBaseline ()

identityAndRevisedLoopsDiffer :
  holonomy identityConnection baselineState ≡
  holonomy revisedConnection baselineState → ⊥
identityAndRevisedLoopsDiffer ()

-- A coarse identity label can remain fixed even as a loop action changes.
-- This is a counterexample to automatic inference, not a claim that an
-- actual person's identity is preserved under any specific intervention.
data CoarseInvariant : Set where
  samePublicRole : CoarseInvariant

publicRole : InnerState → CoarseInvariant
publicRole _ = samePublicRole

publicRolePreservedUnderBothLoops :
  (connection : Connection) (state : InnerState) →
  publicRole (holonomy connection state) ≡ publicRole state
publicRolePreservedUnderBothLoops _ _ = refl

coarseConnectionReport : Connection → CoarseInvariant
coarseConnectionReport _ = samePublicRole

loopNonFactorability :
  NF.NonFactorabilityWitness
    coarseConnectionReport
    (λ connection → holonomy connection baselineState)
loopNonFactorability =
  NF.nonFactorabilityWitness
    identityConnection revisedConnection
    refl
    identityAndRevisedLoopsDiffer

coarseRoleCannotDetermineHolonomy :
  NF.FactorsThrough
    coarseConnectionReport
    (λ connection → holonomy connection baselineState) → ⊥
coarseRoleCannotDetermineHolonomy =
  NF.witnessRulesOutEveryFlatFactorisation loopNonFactorability

-- The group source independently proves that the architecture cannot
-- determine provenance. Context-holonomy witness does not erase that gate.
groupArchitectureDoesNotDetermineOrigin :
  NF.FactorsThrough
    Group.episodeArchitecture Group.episodeOrigin → ⊥
groupArchitectureDoesNotDetermineOrigin =
  Group.architectureDoesNotDetermineOrigin

-- Empirical, ethical and governance gates are NOT discharged by these
-- finite transport calculations. The source uses the holonomy analogy
-- to describe candidate mechanisms; longitudinal measurement is missing.

record PersonalToInstitutionPromotionBoundary : Set where
  constructor boundary
  field
    finiteLoopProvesEmpiricalIdentityErosion : Bool
    loopChangeProvesHostileManipulation : Bool
    observedDisagreementProvesCausalAttack : Bool
    sharedPublicRoleGuaranteesStableInnerState : Bool
    privacyConsentAndMeasurementAreEstablished : Bool

canonicalBoundary : PersonalToInstitutionPromotionBoundary
canonicalBoundary =
  boundary false false false false false
