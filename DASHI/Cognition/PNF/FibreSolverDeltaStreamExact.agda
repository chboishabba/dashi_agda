module DASHI.Cognition.PNF.FibreSolverDeltaStreamExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.DeltaNativePNFDreamFlowExact as Delta

------------------------------------------------------------------------
-- Fibre-local solver emission.
--
-- Balanced ternary is a compact commitment/evidence phase coordinate.  It is
-- deliberately not the whole semantic state.  Alternatives, typed PNF
-- structure, provenance and residuals remain explicit.
------------------------------------------------------------------------

record SolverEmission (SemanticDelta Candidate : Set) : Set where
  constructor solverEmission
  field
    semanticDelta : SemanticDelta
    residual : Residual.ResidualLevel
    commitment : BT.Trit
    alternatives : List Candidate

open SolverEmission public

record FibreLocalSolver
    (NumericEvent Fibre SemanticDelta Candidate : Set) : Set₁ where
  field
    localFibre : NumericEvent → Fibre
    solveLocal :
      (event : NumericEvent) →
      Fibre →
      SolverEmission SemanticDelta Candidate

    -- The ordinary solver entrypoint is definitionally fibre-local.  It has no
    -- accumulated document/global-state argument to scan.
    solveEvent : NumericEvent → SolverEmission SemanticDelta Candidate
    solveEvent event = solveLocal event (localFibre event)

open FibreLocalSolver public

------------------------------------------------------------------------
-- Exact residual accumulation is already a join-semilattice on the existing
-- SensibLaw residual carrier: associative, commutative and idempotent.
------------------------------------------------------------------------

mergeResidual :
  Residual.ResidualLevel →
  Residual.ResidualLevel →
  Residual.ResidualLevel
mergeResidual = Residual.joinResidual

mergeResidualAssociative :
  ∀ a b c →
  mergeResidual (mergeResidual a b) c
    ≡ mergeResidual a (mergeResidual b c)
mergeResidualAssociative = Residual.joinResidual-assoc

mergeResidualCommutative :
  ∀ a b → mergeResidual a b ≡ mergeResidual b a
mergeResidualCommutative = Residual.joinResidual-comm

mergeResidualIdempotent :
  ∀ a → mergeResidual a a ≡ a
mergeResidualIdempotent = Residual.joinResidual-idem

------------------------------------------------------------------------
-- Solver-stream composition.
--
-- Delta composition and residual accumulation are independent coordinates.
-- Commitment composition is policy supplied because balanced ternary is not
-- silently promoted to universal truth semantics.
------------------------------------------------------------------------

record SolverStreamAlgebra
    (Authority SemanticDelta Candidate : Set) : Set₁ where
  field
    deltaAlgebra : Delta.DeltaAlgebra Authority SemanticDelta
    mergeCommitment : BT.Trit → BT.Trit → BT.Trit

open SolverStreamAlgebra public

mergeEmissions :
  ∀ {Authority SemanticDelta Candidate : Set} →
  SolverStreamAlgebra Authority SemanticDelta Candidate →
  SolverEmission SemanticDelta Candidate →
  SolverEmission SemanticDelta Candidate →
  SolverEmission SemanticDelta Candidate
mergeEmissions stream left right =
  solverEmission
    (Delta.composeDelta
      (deltaAlgebra stream)
      (semanticDelta left)
      (semanticDelta right))
    (mergeResidual (residual left) (residual right))
    (mergeCommitment stream (commitment left) (commitment right))
    (append (alternatives left) (alternatives right))
  where
    append : ∀ {A : Set} → List A → List A → List A
    append [] ys = ys
    append (x ∷ xs) ys = x ∷ append xs ys

------------------------------------------------------------------------
-- PNF algebra is the semantic operation surface.
--
-- Existing PNF already exposes unresolved alternative fibres (⊕), contextual
-- fibre-product composition (⊗), temporal/causal composition (∘p), and explicit
-- residual outcomes.  The dream solver therefore emits/combines those semantic
-- objects rather than rebuilding an unrelated graph representation.
------------------------------------------------------------------------

record PNFAlgebraicSolverBridge
    (NumericEvent Fibre SemanticDelta Candidate : Set) : Set₁ where
  field
    solver : FibreLocalSolver NumericEvent Fibre SemanticDelta Candidate
    eventPNF : NumericEvent → PNF.EventPNF
    candidatePNF : Candidate → PNF.CandidatePNF

open PNFAlgebraicSolverBridge public

------------------------------------------------------------------------
-- Residuals are output, not a reason to replay the whole prior state.
------------------------------------------------------------------------

data ResidualRequiresGlobalReplay : Set where

data BalancedTernaryErasesAlternativeFibre : Set where

residualDoesNotRequireGlobalReplayByDefault :
  ResidualRequiresGlobalReplay → ∀ {A : Set} → A
residualDoesNotRequireGlobalReplayByDefault ()

ternaryCommitmentCannotEraseAlternativesByDefault :
  BalancedTernaryErasesAlternativeFibre → ∀ {A : Set} → A
ternaryCommitmentCannotEraseAlternativesByDefault ()
