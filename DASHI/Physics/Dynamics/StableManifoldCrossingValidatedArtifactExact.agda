{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.StableManifoldCrossingValidatedArtifactExact where

open import Agda.Primitive using (Setω)
open import DASHI.Core.Prelude
import DASHI.Physics.Dynamics.BasinSeparatingStableManifoldExact as Separator
import DASHI.Physics.Dynamics.BasinResolutionRobustnessExact as BRR

------------------------------------------------------------------------
-- Proof-carrying validated stable-manifold crossing artifact.
--
-- A numerical continuation / interval ODE program may locate a manifold
-- crossing, but promotion requires checkerSound to produce BOTH:
--
--   * an actual crossing of the selected stable-manifold section; and
--   * the theorem that this section separates the selected two basins.
--
-- This avoids promoting a merely invariant or approximately traced curve into
-- a basin boundary without a separation theorem.
------------------------------------------------------------------------

record StableManifoldCrossingCertificate
  (State Coordinate Resolution : Set)
  (geometry : BRR.ResolutionGeometry State Resolution)
  (resolution : Resolution)
  (LowerBasin UpperBasin : State → Set) : Set₁ where
  field
    section :
      Separator.StableManifoldCrossSection State Coordinate

    separatorLaw :
      Separator.TwoBasinSeparatorLaw
        section LowerBasin UpperBasin

    resolvedCrossing :
      Separator.ResolvedCrossingBracket
        section geometry resolution

open StableManifoldCrossingCertificate public

record StableManifoldValidatedArtifact
  (State Coordinate Resolution Bytes Digest Payload : Set)
  (geometry : BRR.ResolutionGeometry State Resolution)
  (resolution : Resolution)
  (LowerBasin UpperBasin : State → Set) : Setω where
  field
    sourceCommit : Digest
    cleanWorktreeWitness : Set
    runnerDigest : Digest
    inputDigest : Digest
    outputDigest : Digest
    frozenBytes : Bytes
    precisionBits : Nat

    payload : Payload
    parser : Bytes → Payload
    parserAcceptedFrozenOutput :
      parser frozenBytes ≡ payload

    checker : Payload → Bool
    checkerPassed :
      checker payload ≡ true

    checkerSound :
      checker payload ≡ true →
      StableManifoldCrossingCertificate
        State Coordinate Resolution
        geometry resolution
        LowerBasin UpperBasin

open StableManifoldValidatedArtifact public

validated-crossing-certificate :
  ∀ {State Coordinate Resolution Bytes Digest Payload : Set}
    {geometry : BRR.ResolutionGeometry State Resolution}
    {resolution : Resolution}
    {LowerBasin UpperBasin : State → Set} →
  (artifact :
    StableManifoldValidatedArtifact
      State Coordinate Resolution Bytes Digest Payload
      geometry resolution LowerBasin UpperBasin) →
  StableManifoldCrossingCertificate
    State Coordinate Resolution
    geometry resolution
    LowerBasin UpperBasin
validated-crossing-certificate artifact =
  checkerSound artifact (checkerPassed artifact)

validated-crossing-gives-boundary-witness :
  ∀ {State Coordinate Resolution Bytes Digest Payload : Set}
    {geometry : BRR.ResolutionGeometry State Resolution}
    {resolution : Resolution}
    {LowerBasin UpperBasin : State → Set} →
  (artifact :
    StableManifoldValidatedArtifact
      State Coordinate Resolution Bytes Digest Payload
      geometry resolution LowerBasin UpperBasin) →
  BRR.BasinBoundaryResolutionWitness
    geometry LowerBasin resolution
validated-crossing-gives-boundary-witness artifact =
  let certificate = validated-crossing-certificate artifact
  in Separator.resolved-crossing-gives-boundary-witness
      (separatorLaw certificate)
      (resolvedCrossing certificate)

validated-crossing-refutes-resolution-robustness :
  ∀ {State Coordinate Resolution Bytes Digest Payload : Set}
    {geometry : BRR.ResolutionGeometry State Resolution}
    {resolution : Resolution}
    {LowerBasin UpperBasin : State → Set} →
  (artifact :
    StableManifoldValidatedArtifact
      State Coordinate Resolution Bytes Digest Payload
      geometry resolution LowerBasin UpperBasin) →
  ¬ BRR.RobustAt
      geometry LowerBasin resolution
      (BRR.BasinBoundaryResolutionWitness.inside
        (validated-crossing-gives-boundary-witness artifact))
validated-crossing-refutes-resolution-robustness artifact =
  BRR.boundary-witness-refutes-robustness
    (validated-crossing-gives-boundary-witness artifact)
