module DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCandidate256Shape where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)

open import Ontology.DNA.ChemistryUVCoordinates as UV
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Smallest local shape package for the active atomic blocker lane.
--
-- This does not yet prove a concrete separating pair. It records the exact
-- UV-coordinate shape that the next witness should instantiate:
-- same `v` everywhere, same `u` everywhere except one chosen slot, with a
-- `strong -> weak` flip at fixed `purine`.

record QuotientCrossBandCandidate256Shape : Set where
  field
    index : Nat
    sharedV : CDQ.FeatureV
    leftU : CDQ.FeatureU
    rightU : CDQ.FeatureU
    leftUV : UV.UVCoordinates 256
    rightUV : UV.UVCoordinates 256

candidateLeftFeature256 :
  QuotientCrossBandCandidate256Shape → CDQ.ChemistryFeature
candidateLeftFeature256 shape =
  UV.feature256
    (QuotientCrossBandCandidate256Shape.leftUV shape)

candidateRightFeature256 :
  QuotientCrossBandCandidate256Shape → CDQ.ChemistryFeature
candidateRightFeature256 shape =
  UV.feature256
    (QuotientCrossBandCandidate256Shape.rightUV shape)
