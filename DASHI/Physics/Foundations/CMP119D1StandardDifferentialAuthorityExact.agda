{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119D1StandardDifferentialAuthorityExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.GRQFTCMP119CorrectedD1MaxCutExact as Corrected
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeD1ReductionRound152Exact as R152

------------------------------------------------------------------------
-- CORRECTED D1 STANDARD-DIFFERENTIAL AUTHORITY
--
-- Audit result: BC2.firstVariation is an unconstrained field of the current
-- CompactGroupHeatDoobOnCarrier source record.  Therefore linearity and the
-- physical composite chain rule are not derivable from that record alone.
--
-- The minimal legitimate source strengthening is precisely:
--   D1a. ordinary first-derivative congruence/zero/additivity;
--   D1b. chain rule through the already-selected physical background/tangent
--        transports.
--
-- This owner packages those two standard differential laws and compiles them
-- directly into the existing CorrectedCMP119D1PhysicalSemantics consumer.
------------------------------------------------------------------------

record CMP119D1StandardDifferentialAuthority
    {History Cell : Set} {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff)
    : Set₁ where
  field
    firstVariationLinearity :
      R143.PresentCutBC2FirstVariationLinearity present

    physicalCompositeChainRule :
      R152.PhysicalCompositeD1ChainRule present firstVariationLinearity

open CMP119D1StandardDifferentialAuthority public

compileCorrectedD1Semantics :
  ∀ {History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff} →
  CMP119D1StandardDifferentialAuthority present →
  Corrected.CorrectedCMP119D1PhysicalSemantics present
compileCorrectedD1Semantics authority = record
  { Corrected.CorrectedCMP119D1PhysicalSemantics.d1aBC2FirstVariationLinearity =
      firstVariationLinearity authority
  ; Corrected.CorrectedCMP119D1PhysicalSemantics.d1bPhysicalBackgroundTransportDerivative =
      physicalCompositeChainRule authority
  }

currentBC2SourceRecordAloneProvesD1Linearity : Bool
currentBC2SourceRecordAloneProvesD1Linearity = false

currentBC2SourceRecordAloneProvesPhysicalChainRule : Bool
currentBC2SourceRecordAloneProvesPhysicalChainRule = false

minimalD1AuthorityCutOwned : Bool
minimalD1AuthorityCutOwned = true

noOldTypeWrongD1bEqualityReintroduced : Bool
noOldTypeWrongD1bEqualityReintroduced = true

remainingD1DebtIsStandardDifferentialSourceInstantiation : Bool
remainingD1DebtIsStandardDifferentialSourceInstantiation = true
