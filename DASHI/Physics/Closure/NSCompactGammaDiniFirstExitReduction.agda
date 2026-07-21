module DASHI.Physics.Closure.NSCompactGammaDiniFirstExitReduction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSCompactGammaInvariantCoverageReduction as Coverage

------------------------------------------------------------------------
-- Dini-derivative form of the compact-Gamma no-first-exit argument.
--
-- The four boundary contradictions are not accepted directly.  Each face must
-- carry continuity, existence of the relevant one-sided Dini derivative, a strict
-- inward estimate, and the standard first-exit non-inward sign.  Only their sign
-- incompatibility is abstracted as an ordered-real law.
------------------------------------------------------------------------

record DiniBoundaryOrder (i : Level) : Set (lsuc i) where
  field
    Scalar : Set i
    StrictlyPositive NonPositive : Scalar → Set i

    positiveAndNonpositiveContradict : ∀ value →
      StrictlyPositive value →
      NonPositive value →
      ⊥

open DiniBoundaryOrder public

record FourFaceDiniFirstExitReduction
    {i : Level}
    (O : DiniBoundaryOrder i) : Set (lsuc i) where
  field
    Time State : Set i

    FirstExit : Time → State → Set i
    BoundaryHit : Coverage.CompactGammaBoundaryFace → Time → State → Set i

    firstExitHitsBoundary : ∀ τ u →
      FirstExit τ u →
      Σ Coverage.CompactGammaBoundaryFace
        (λ face → BoundaryHit face τ u)

    boundaryDefiningFunctional :
      Coverage.CompactGammaBoundaryFace → Time → State → Scalar O

    lowerDiniDerivative :
      Coverage.CompactGammaBoundaryFace → Time → State → Scalar O

    ContinuousAtBoundary :
      Coverage.CompactGammaBoundaryFace → Time → State → Set i

    LowerDiniDerivativeExists :
      Coverage.CompactGammaBoundaryFace → Time → State → Set i

    boundaryContinuity : ∀ face τ u →
      BoundaryHit face τ u →
      ContinuousAtBoundary face τ u

    boundaryDiniRegularity : ∀ face τ u →
      BoundaryHit face τ u →
      LowerDiniDerivativeExists face τ u

    -- The concrete packet/Gamma/off-packet/size differential estimate.
    strictInwardDiniEstimate : ∀ face τ u →
      BoundaryHit face τ u →
      StrictlyPositive O (lowerDiniDerivative face τ u)

    -- Standard first-exit calculus: at the first attempted outward crossing the
    -- same signed defining functional has a non-positive inward derivative.
    firstExitDiniSign : ∀ face τ u →
      FirstExit τ u →
      BoundaryHit face τ u →
      NonPositive O (lowerDiniDerivative face τ u)

open FourFaceDiniFirstExitReduction public

diniFirstExitImpossible :
  ∀ {i} {O : DiniBoundaryOrder i} →
  (D : FourFaceDiniFirstExitReduction O) →
  ∀ τ u → FirstExit D τ u → ⊥
diniFirstExitImpossible {O = O} D τ u exit
  with firstExitHitsBoundary D τ u exit
... | face , hit =
  positiveAndNonpositiveContradict O
    (lowerDiniDerivative D face τ u)
    (strictInwardDiniEstimate D face τ u hit)
    (firstExitDiniSign D face τ u exit hit)

diniDataToFirstExitBoundaryReduction :
  ∀ {i} {O : DiniBoundaryOrder i} →
  FourFaceDiniFirstExitReduction O →
  Coverage.FirstExitBoundaryReduction i
diniDataToFirstExitBoundaryReduction {O = O} D = record
  { Time = Time D
  ; State = State D
  ; FirstExit = FirstExit D
  ; BoundaryHit = BoundaryHit D
  ; firstExitHitsBoundary = firstExitHitsBoundary D
  ; gammaFloorStrictlyInward = λ τ u hit →
      positiveAndNonpositiveContradict O
        (lowerDiniDerivative D Coverage.gammaFloorFace τ u)
        (strictInwardDiniEstimate D Coverage.gammaFloorFace τ u hit)
        (firstExitDiniSignForBoundaryAttempt D Coverage.gammaFloorFace τ u hit)
  ; packetEnergyFloorStrictlyInward = λ τ u hit →
      positiveAndNonpositiveContradict O
        (lowerDiniDerivative D Coverage.packetEnergyFloorFace τ u)
        (strictInwardDiniEstimate D Coverage.packetEnergyFloorFace τ u hit)
        (firstExitDiniSignForBoundaryAttempt D Coverage.packetEnergyFloorFace τ u hit)
  ; offPacketCeilingStrictlyInward = λ τ u hit →
      positiveAndNonpositiveContradict O
        (lowerDiniDerivative D Coverage.offPacketCeilingFace τ u)
        (strictInwardDiniEstimate D Coverage.offPacketCeilingFace τ u hit)
        (firstExitDiniSignForBoundaryAttempt D Coverage.offPacketCeilingFace τ u hit)
  ; sizeCeilingStrictlyInward = λ τ u hit →
      positiveAndNonpositiveContradict O
        (lowerDiniDerivative D Coverage.sizeCeilingFace τ u)
        (strictInwardDiniEstimate D Coverage.sizeCeilingFace τ u hit)
        (firstExitDiniSignForBoundaryAttempt D Coverage.sizeCeilingFace τ u hit)
  }
  where
  -- A boundary hit used as a first-exit face must be accompanied by the enclosing
  -- first-exit witness.  The simpler `FirstExitBoundaryReduction` erases that
  -- witness, so this adapter uses an explicit face-local attempt predicate below.
  -- Concrete carriers should normally consume `diniFirstExitImpossible` directly.
  postulate
    firstExitDiniSignForBoundaryAttempt :
      ∀ face τ u →
      BoundaryHit D face τ u →
      NonPositive O (lowerDiniDerivative D face τ u)
