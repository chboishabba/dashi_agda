-- Cross-owner adapter: several authoritative imported DASHI donors predate
-- safe-kernel certification. Do not advertise this integrated adapter as a
-- Golden --safe theorem; prove safe leaf lemmas separately and kernel-check
-- the import closure before promotion.
module DASHI.Reasoning.LeechExpertSignNonAntipodeBoundaryExact where

-- Reuse the existing argument response and signed expert owners.
-- "Opposing argument", "inverted latent coordinates", "expert chart",
-- and "unsafe output" are distinct types, never equal by construction.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as Response
import DASHI.Reasoning.LeechSignedHistoryExpertBidiExact as Expert

data GeometricAction : Set where
  identityAction : GeometricAction
  antipodalAction : GeometricAction

data OutcomeLabel : Set where
  observedAcceptable : OutcomeLabel
  observedUnacceptable : OutcomeLabel
  notEvaluated : OutcomeLabel

-- A specific learned expert chart is acted upon by an involution only
-- when the chosen action actually specifies this transport.
actionOnState : GeometricAction → Expert.HistoryState → Expert.HistoryState
actionOnState identityAction x = x
actionOnState antipodalAction x = Expert.invertHistory x

antipodalSquare :
  (x : Expert.HistoryState) →
  actionOnState antipodalAction (actionOnState antipodalAction x) ≡ x
antipodalSquare x = Expert.invertHistoryInvolutive x

-- Structured responses do not determine either group action or a
-- behavioural/safety label. The explicit witness carries BOTH
-- independently, so a disagreement cannot silently flip a chart.
record EvaluatedExpertResponse : Set where
  constructor evaluatedExpertResponse
  field
    response : Response.ResponseKind
    geometry : GeometricAction
    observed : OutcomeLabel

-- Counterexamples to any automatic identification:
-- a challenge can coexist with identity geometry or the antipode;
-- same response may receive either independently assessed outcome.
challengeWithIdentity : EvaluatedExpertResponse
challengeWithIdentity =
  evaluatedExpertResponse Response.challengeEvidence identityAction notEvaluated

challengeWithAntipode : EvaluatedExpertResponse
challengeWithAntipode =
  evaluatedExpertResponse Response.challengeEvidence antipodalAction notEvaluated

semanticChallengeDoesNotDetermineSign :
  EvaluatedExpertResponse.response challengeWithIdentity
    ≡ EvaluatedExpertResponse.response challengeWithAntipode
semanticChallengeDoesNotDetermineSign = refl

-- A global MoE equivariance theorem needs routing and weighting
-- transported over the same action, or an exact corrective residual.
-- It is NOT obtained by inspecting a response kind or outcome label.
