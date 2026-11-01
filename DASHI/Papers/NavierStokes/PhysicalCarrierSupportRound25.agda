module DASHI.Papers.NavierStokes.PhysicalCarrierSupportRound25 where

------------------------------------------------------------------------
-- Paper-facing status for the Round 25 highest-alpha tranche.
--
-- This surface records one genuine ladder promotion: L4 moves from an open
-- physical producer to checked exact after classification of the literal Z^3
-- resonant output fibres and exact five-source recomposition.  L3 is narrowed
-- but remains open at finite-dimensional continuum ODE existence and
-- constraint propagation.  No nonlinear tax or Clay promotion is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaClayLemmaLadderRound24Exact as R24
import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaClayLemmaLadderRound25Exact as Ladder

record PhysicalCarrierSupportRound25Status : Set where
  constructor physical-carrier-support-round25-status
  field
    literalGalerkinCarrierCertificateConstructed : Bool
    physicalOutputFibreDuplicateFree : Bool
    actualPhysicalTriadsClassifiedExhaustively : Bool
    actualPhysicalClassificationUnique : Bool
    lowLowFarOutputExcluded : Bool
    exactPhysicalFiveSourceRecomposition : Bool
    L4CheckedExact : Bool
    finiteDimensionalODEInstanceProduced : Bool
    realityTransversalityPropagationProduced : Bool
    L7UniformPhysicalTaxesProduced : Bool
    L15StrictViscosityMarginProduced : Bool
    unconditionalClayTheoremPromoted : Bool

open PhysicalCarrierSupportRound25Status public

canonicalPhysicalCarrierSupportRound25Status :
  PhysicalCarrierSupportRound25Status
canonicalPhysicalCarrierSupportRound25Status =
  physical-carrier-support-round25-status
    true true true true true true true
    false false false false false

l4IsCheckedExact :
  L4CheckedExact canonicalPhysicalCarrierSupportRound25Status ≡ true
l4IsCheckedExact = refl

finiteODEInstanceRemainsOpen :
  finiteDimensionalODEInstanceProduced
    canonicalPhysicalCarrierSupportRound25Status
  ≡ false
finiteODEInstanceRemainsOpen = refl

physicalTaxesRemainOpen :
  L7UniformPhysicalTaxesProduced
    canonicalPhysicalCarrierSupportRound25Status
  ≡ false
physicalTaxesRemainOpen = refl

strictMarginRemainsOpen :
  L15StrictViscosityMarginProduced
    canonicalPhysicalCarrierSupportRound25Status
  ≡ false
strictMarginRemainsOpen = refl

clayPromotionRemainsFalse :
  unconditionalClayTheoremPromoted
    canonicalPhysicalCarrierSupportRound25Status
  ≡ false
clayPromotionRemainsFalse = refl

highestAlphaLadder : R24.HighestAlphaClayLemmaLadder
highestAlphaLadder =
  Ladder.canonicalHighestAlphaClayLemmaLadderRound25

exactEvidence : Ladder.Round25ExactEvidence
exactEvidence = Ladder.canonicalRound25ExactEvidence
