module DASHI.Analysis.NonArchimedeanSpectralBidiObligationExact where

------------------------------------------------------------------------
-- Reverse / BIDI obligation compiler for the non-Archimedean spectral lane.
--
-- This module deliberately does not re-prove the source mathematics.  It
-- records the exact producer obligations that must be discharged before a
-- downstream advertised claim can be promoted.  The forward direction is:
--
--   source theorem -> typed receipt -> consumer claim
--
-- The reverse direction is:
--
--   requested consumer claim -> missing same-object / strength obligation.
--
-- This lets theorem names and prose claims fail closed instead of silently
-- transporting across representation boundaries.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

record BidiClaim : Set where
  constructor bidiClaim
  field
    claimName : String
    producerName : String
    theoremExists : Bool
    sameObjectWeldOwned : Bool
    advertisedStrengthOwned : Bool
    promotionAllowed : Bool

open BidiClaim public

spectralCircleSpatialClaim : BidiClaim
spectralCircleSpatialClaim =
  bidiClaim
    "spatial twisted-block spectral circle"
    "character monomial dynamics + explicit unitary/Fourier intertwiner"
    true
    false
    false
    false

orbitProductClaim : BidiClaim
orbitProductClaim =
  bidiClaim
    "two x3 orbit products multiply to two"
    "odd-residue cyclotomic product + separate x3 orbit partition receipt"
    true
    true
    true
    true

multiPrimeCoverClaim : BidiClaim
multiPrimeCoverClaim =
  bidiClaim
    "arbitrary DAG admits multi-prime adelic cover"
    "construction of MultiPrimeTreeDecomposition from graph hypotheses"
    true
    false
    false
    false

multiPrimeSparsityClaim : BidiClaim
multiPrimeSparsityClaim =
  bidiClaim
    "depth-decaying active attention fraction"
    "nontrivial quantitative bound connecting routing depth to active set size"
    true
    false
    false
    false

holographicAreaClaim : BidiClaim
holographicAreaClaim =
  bidiClaim
    "contracted boundary-state entropy equals cut size times log two"
    "same-object equality between contracted density-state entropy and the existential entropy scalar"
    true
    false
    false
    false

ropeOptimalityClaim : BidiClaim
ropeOptimalityClaim =
  bidiClaim
    "RoPE medoid compression is transformer-optimal"
    "model-level loss / fidelity theorem built on the geometric invariance theorem"
    true
    false
    false
    false

------------------------------------------------------------------------
-- Exact reverse compiler outputs.
------------------------------------------------------------------------

data MissingObligation : Set where
  needSpatialIntertwiner : MissingObligation
  needOrbitPartitionWeld : MissingObligation
  needGraphToDecompositionProducer : MissingObligation
  needDepthDecayProducer : MissingObligation
  needBoundaryEntropySameObjectWeld : MissingObligation
  needModelLevelRoPEConsumerTheorem : MissingObligation
  noMissingObligation : MissingObligation

compileMissing : BidiClaim → MissingObligation
compileMissing c with claimName c
... | _ with promotionAllowed c
...   | true  = noMissingObligation
...   | false with sameObjectWeldOwned c | advertisedStrengthOwned c
...     | false | _ = needSpatialIntertwiner
...     | true  | false = needDepthDecayProducer
...     | true  | true = noMissingObligation

-- Claim-specific exact routing keeps distinct missing producers separate even
-- when their Boolean summary is identical.
claimSpecificMissing : String → MissingObligation
claimSpecificMissing "spatial twisted-block spectral circle" = needSpatialIntertwiner
claimSpecificMissing "two x3 orbit products multiply to two" = noMissingObligation
claimSpecificMissing "arbitrary DAG admits multi-prime adelic cover" = needGraphToDecompositionProducer
claimSpecificMissing "depth-decaying active attention fraction" = needDepthDecayProducer
claimSpecificMissing "contracted boundary-state entropy equals cut size times log two" = needBoundaryEntropySameObjectWeld
claimSpecificMissing "RoPE medoid compression is transformer-optimal" = needModelLevelRoPEConsumerTheorem
claimSpecificMissing _ = noMissingObligation

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record BidiFirewall : Set where
  constructor bidiFirewall
  field
    theoremNameImpliesAdvertisedStrength : Bool
    theoremExistsImpliesSameObjectWeld : Bool
    conditionalConsumerImpliesProducer : Bool
    architecturalAnalogyImpliesTheoremTransport : Bool

canonicalBidiFirewall : BidiFirewall
canonicalBidiFirewall = bidiFirewall false false false false

spectralCircleNeedsIntertwiner :
  claimSpecificMissing (claimName spectralCircleSpatialClaim) ≡ needSpatialIntertwiner
spectralCircleNeedsIntertwiner = refl

orbitProductIsPromotable :
  claimSpecificMissing (claimName orbitProductClaim) ≡ noMissingObligation
orbitProductIsPromotable = refl

multiPrimeCoverNeedsProducer :
  claimSpecificMissing (claimName multiPrimeCoverClaim) ≡ needGraphToDecompositionProducer
multiPrimeCoverNeedsProducer = refl

multiPrimeSparsityNeedsQuantitativeProducer :
  claimSpecificMissing (claimName multiPrimeSparsityClaim) ≡ needDepthDecayProducer
multiPrimeSparsityNeedsQuantitativeProducer = refl

holographicClaimNeedsSameObjectWeld :
  claimSpecificMissing (claimName holographicAreaClaim) ≡ needBoundaryEntropySameObjectWeld
holographicClaimNeedsSameObjectWeld = refl

ropeOptimalityNeedsModelConsumer :
  claimSpecificMissing (claimName ropeOptimalityClaim) ≡ needModelLevelRoPEConsumerTheorem
ropeOptimalityNeedsModelConsumer = refl
