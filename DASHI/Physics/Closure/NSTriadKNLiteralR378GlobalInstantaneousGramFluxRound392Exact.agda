module DASHI.Physics.Closure.NSTriadKNLiteralR378GlobalInstantaneousGramFluxRound392Exact where

------------------------------------------------------------------------
-- ROUND392 / GLOBAL SAME-OBJECT INSTANTANEOUS GRAM FLUX
--
-- R391 closes the exact R378 Gram-flux identity on one literal physical output
-- fibre.  R378.globalGramDebt is itself only the finite map-sum over outputs.
-- This module performs that last finite aggregation without estimates.
--
-- The result is the exact global instantaneous identity
--
--   D_Gram^R378(global)
--     = - F'_off(global) + R_weighted(global).
--
-- Thus the remaining R303 weld is no longer a carrier or finite-summation
-- problem.  It is the actual temporal integration / endpoint theorem for this
-- already identified global flux observable.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (Positive)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCompanionGramLedgerRound378Exact as R378
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNLiteralR378InstantaneousGramFluxRound391Exact as R391

F : C3.RealField _
F = Rational.rationalRealField

module GlobalFlux
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem)))
    (positivePairRate :
      (alpha beta : Physical.PhysicalTriadIncidence) →
      Positive
        (R291.pairRate
          (R389.DoubleMixedPair.physicalDoubleMixedPair
            physicalSystem S alpha beta))) where

  module O = R391.LiteralOutputFlux
    physicalSystem S L H P positivePairRate

  append : ∀ {A : Set} → List A → List A → List A
  append [] ys = ys
  append (x ∷ xs) ys = x ∷ append xs ys

  globalPairs : Nat → List Z3.FourierMode → List R290.DampedGramPair
  globalPairs cutoff [] = []
  globalPairs cutoff (output ∷ outputs) =
    append (O.outputPairs cutoff output) (globalPairs cutoff outputs)

  fluxTangentAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumWeightedFluxTangent (append left right)
    ≡ R385.sumWeightedFluxTangent left + R385.sumWeightedFluxTangent right
  fluxTangentAppend [] right = refl
  fluxTangentAppend (pair ∷ rest) right
    rewrite fluxTangentAppend rest right = refl

  remainderAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumWeightedRemainder (append left right)
    ≡ R385.sumWeightedRemainder left + R385.sumWeightedRemainder right
  remainderAppend [] right = refl
  remainderAppend (pair ∷ rest) right
    rewrite remainderAppend rest right = refl

  literalGlobalGramFluxIdentity :
    (cutoff : Nat) (outputs : List Z3.FourierMode) →
    R378.globalGramDebt O.E S O.velocity cutoff outputs
    ≡
    (0ℚ - R385.sumWeightedFluxTangent (globalPairs cutoff outputs))
      + R385.sumWeightedRemainder (globalPairs cutoff outputs)
  literalGlobalGramFluxIdentity cutoff [] = refl
  literalGlobalGramFluxIdentity cutoff (output ∷ outputs) =
    let
      headPairs = O.outputPairs cutoff output
      tailPairs = globalPairs cutoff outputs
      headIdentity = O.literalOutputGramFluxIdentity cutoff output
      tailIdentity = literalGlobalGramFluxIdentity cutoff outputs
      fluxAppend = fluxTangentAppend headPairs tailPairs
      remAppend = remainderAppend headPairs tailPairs
    in
    trans
      (cong₂ _+_ headIdentity tailIdentity)
      (trans
        (solve
          ( R385.sumWeightedFluxTangent headPairs
          ∷ R385.sumWeightedFluxTangent tailPairs
          ∷ R385.sumWeightedRemainder headPairs
          ∷ R385.sumWeightedRemainder tailPairs
          ∷ []))
        (cong₂ _+_
          (cong (0ℚ -_) (sym fluxAppend))
          (sym remAppend)))
    where
    cong : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
    cong f refl = refl
    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

round392LiteralGlobalR378GramFluxClosed : Bool
round392LiteralGlobalR378GramFluxClosed = true

round392FiniteOutputAggregationStillOpen : Bool
round392FiniteOutputAggregationStillOpen = false

round392TemporalIntegrationStillOpen : Bool
round392TemporalIntegrationStillOpen = true

round392LiteralGlobalR378GramFluxClosedIsTrue :
  round392LiteralGlobalR378GramFluxClosed ≡ true
round392LiteralGlobalR378GramFluxClosedIsTrue = refl
