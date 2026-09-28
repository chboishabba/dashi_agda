module DASHI.Reasoning.Trialectic369T5ComplementOggResidualBidiExact where

------------------------------------------------------------------------
-- T5 SELECTED-INVERSION QUOTIENT <-> OGG/SSP15 LANE x NINE RESIDUAL
--
-- DASHI CONTRIBUTION
--
-- The previous owner proves:
--
--   T5 -> PhaseOrbit15 x NineSheet
--
-- with a canonical section, where PhaseOrbit15 is the structural 3x5 quotient.
-- The existing chosen Ogg/PhaseOrbit bidi therefore gives an exact carrier
-- rechart
--
--   PhaseOrbit15 x NineSheet
--      <-> OggPrimeLane x NineSheet.
--
-- This is exact as a finite carrier presentation.  The Ogg labeling still
-- passes through the explicitly CHOSEN prime/internal indexing; it is not
-- promoted to an intrinsic arithmetic quotient of T5.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

import DASHI.Reasoning.Trialectic369T5ComplementPhaseOrbitResidualExact as T5
import DASHI.Moonshine.OggSSP15PhaseOrbitBidiExact as Ogg
import DASHI.Moonshine.OggSSP369RootRefinementBidiExact as Root
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

OggWithNineResidual : Set
OggWithNineResidual =
  Ogg.OggSSP15Lane × Triadic.NineSheet

phaseOrbitResidualToOggResidual :
  T5.PhaseOrbitWithNineResidual ->
  OggWithNineResidual
phaseOrbitResidualToOggResidual (phaseOrbit , residual) =
  Ogg.phaseOrbit15ToOgg phaseOrbit , residual

oggResidualToPhaseOrbitResidual :
  OggWithNineResidual ->
  T5.PhaseOrbitWithNineResidual
oggResidualToPhaseOrbitResidual (prime , residual) =
  Ogg.oggToPhaseOrbit15 prime , residual

phaseOrbitOggResidualRoundTrip :
  (state : T5.PhaseOrbitWithNineResidual) ->
  oggResidualToPhaseOrbitResidual
    (phaseOrbitResidualToOggResidual state)
  ≡ state
phaseOrbitOggResidualRoundTrip (phaseOrbit , residual)
  rewrite Ogg.phaseOrbitAfterOgg phaseOrbit = refl

oggPhaseOrbitResidualRoundTrip :
  (state : OggWithNineResidual) ->
  phaseOrbitResidualToOggResidual
    (oggResidualToPhaseOrbitResidual state)
  ≡ state
oggPhaseOrbitResidualRoundTrip (prime , residual)
  rewrite Ogg.oggAfterPhaseOrbit prime = refl

------------------------------------------------------------------------
-- 1. Direct T5 quotient and canonical section.
------------------------------------------------------------------------

quotientT5ToOggResidual :
  T5.Kernel5 ->
  OggWithNineResidual
quotientT5ToOggResidual kernel =
  phaseOrbitResidualToOggResidual
    (T5.quotientKernel5ToPhaseOrbitResidual kernel)

canonicalLiftOggResidual :
  OggWithNineResidual ->
  T5.Kernel5
canonicalLiftOggResidual state =
  T5.canonicalLiftPhaseOrbitResidual
    (oggResidualToPhaseOrbitResidual state)

quotientLiftOggResidualRoundTrip :
  (state : OggWithNineResidual) ->
  quotientT5ToOggResidual
    (canonicalLiftOggResidual state)
  ≡ state
quotientLiftOggResidualRoundTrip state =
  trans
    (cong
      phaseOrbitResidualToOggResidual
      (T5.quotientLiftPhaseOrbitResidualRoundTrip
        (oggResidualToPhaseOrbitResidual state)))
    (oggPhaseOrbitResidualRoundTrip state)

------------------------------------------------------------------------
-- 2. Rechart the lane factor as the canonical ROOT 369 refinement.
------------------------------------------------------------------------

Root369WithNineResidual : Set
Root369WithNineResidual =
  Root.Root369Refinement × Triadic.NineSheet

oggResidualToRoot369Residual :
  OggWithNineResidual ->
  Root369WithNineResidual
oggResidualToRoot369Residual (prime , residual) =
  Root.oggToRoot369 prime , residual

root369ResidualToOggResidual :
  Root369WithNineResidual ->
  OggWithNineResidual
root369ResidualToOggResidual (root , residual) =
  Root.root369ToOgg root , residual

oggRoot369ResidualRoundTrip :
  (state : OggWithNineResidual) ->
  root369ResidualToOggResidual
    (oggResidualToRoot369Residual state)
  ≡ state
oggRoot369ResidualRoundTrip (prime , residual)
  rewrite Root.root369OggRoundTrip prime = refl

root369OggResidualRoundTrip :
  (state : Root369WithNineResidual) ->
  oggResidualToRoot369Residual
    (root369ResidualToOggResidual state)
  ≡ state
root369OggResidualRoundTrip (root , residual)
  rewrite Root.oggRoot369RoundTrip root = refl

quotientT5ToRoot369Residual :
  T5.Kernel5 ->
  Root369WithNineResidual
quotientT5ToRoot369Residual kernel =
  oggResidualToRoot369Residual
    (quotientT5ToOggResidual kernel)

canonicalLiftRoot369Residual :
  Root369WithNineResidual ->
  T5.Kernel5
canonicalLiftRoot369Residual state =
  canonicalLiftOggResidual
    (root369ResidualToOggResidual state)

quotientLiftRoot369ResidualRoundTrip :
  (state : Root369WithNineResidual) ->
  quotientT5ToRoot369Residual
    (canonicalLiftRoot369Residual state)
  ≡ state
quotientLiftRoot369ResidualRoundTrip state =
  trans
    (cong
      oggResidualToRoot369Residual
      (quotientLiftOggResidualRoundTrip
        (root369ResidualToOggResidual state)))
    (root369OggResidualRoundTrip state)

------------------------------------------------------------------------
-- 3. Firewall.
------------------------------------------------------------------------

data T5QuotientDerivesOggArithmeticLabeling : Set where
data NineResidualIsArithmeticNoise : Set where
data Root369ResidualIsAnalyticPAdicProduct : Set where

t5QuotientDoesNotDeriveOggArithmeticLabeling :
  T5QuotientDerivesOggArithmeticLabeling -> ⊥
t5QuotientDoesNotDeriveOggArithmeticLabeling ()

nineResidualNotDiscardedAsNoise :
  NineResidualIsArithmeticNoise -> ⊥
nineResidualNotDiscardedAsNoise ()

root369ResidualNotPromotedToAnalyticPAdicProduct :
  Root369ResidualIsAnalyticPAdicProduct -> ⊥
root369ResidualNotPromotedToAnalyticPAdicProduct ()

record Trialectic369T5ComplementOggResidualBidiBoundary : Set where
  constructor trialectic-369-t5-complement-ogg-residual-bidi-boundary
  field
    phaseOrbitResidualToOggResidualBidiPaid : Bool
    t5QuotientToOggResidualSectionPaid : Bool
    oggResidualToRoot369ResidualBidiPaid : Bool
    t5QuotientToRoot369ResidualSectionPaid : Bool
    nineStateResidualRetained : Bool
    oggArithmeticLabelingDerivedFromT5 : Bool
    analyticPAdicProductClaimed : Bool

canonicalTrialectic369T5ComplementOggResidualBidiBoundary :
  Trialectic369T5ComplementOggResidualBidiBoundary
canonicalTrialectic369T5ComplementOggResidualBidiBoundary =
  trialectic-369-t5-complement-ogg-residual-bidi-boundary
    true true true true true false false
