module DASHI.Physics.Closure.NSTriadKNFibreLocalR378GlobalInstantaneousGramFluxRound398Exact where

------------------------------------------------------------------------
-- ROUND398 / GLOBAL R378 FLUX WITH POSITIVITY ONLY ON SELECTED OUTPUT FIBRES
--
-- R397 removes the impossible global-all-incidence positivity premise at one
-- output.  This file performs the finite output aggregation while carrying one
-- local positivity witness per output actually present in the output list.
-- No positivity is requested for any unselected output or incidence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)
open import Data.List.Base using (_++_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCompanionGramLedgerRound378Exact as R378
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378InstantaneousGramFluxRound397Exact as R397

F : C3.RealField _
F = Rational.rationalRealField

module GlobalFluxLocal
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
      (Audit.velocityAt (Field30.finiteSystem physicalSystem))) where

  module O = R397.LiteralOutputFluxLocal physicalSystem S L H P
  module Local = R396.LocalEnumerate physicalSystem S

  data OutputFibresPositiveOn (cutoff : Nat) : List Z3.FourierMode → Set where
    positiveOutputsNil : OutputFibresPositiveOn cutoff []
    positiveOutputsCons :
      ∀ {output outputs} →
      Local.PairRatePositiveOn (Output.physicalOutputFiber cutoff output) →
      OutputFibresPositiveOn cutoff outputs →
      OutputFibresPositiveOn cutoff (output ∷ outputs)

  globalPairs :
    (cutoff : Nat) (outputs : List Z3.FourierMode) →
    OutputFibresPositiveOn cutoff outputs →
    List R290.DampedGramPair
  globalPairs cutoff [] positiveOutputsNil = []
  globalPairs cutoff (output ∷ outputs)
      (positiveOutputsCons headPositive tailPositive) =
    O.outputPairs cutoff output headPositive ++
      globalPairs cutoff outputs tailPositive

  fluxTangentAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumWeightedFluxTangent (left ++ right)
    ≡ R385.sumWeightedFluxTangent left + R385.sumWeightedFluxTangent right
  fluxTangentAppend [] right = refl
  fluxTangentAppend (pair ∷ rest) right
    rewrite fluxTangentAppend rest right = refl

  remainderAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumWeightedRemainder (left ++ right)
    ≡ R385.sumWeightedRemainder left + R385.sumWeightedRemainder right
  remainderAppend [] right = refl
  remainderAppend (pair ∷ rest) right
    rewrite remainderAppend rest right = refl

  literalGlobalGramFluxIdentity :
    (cutoff : Nat) (outputs : List Z3.FourierMode) →
    (positive : OutputFibresPositiveOn cutoff outputs) →
    R378.globalGramDebt O.E S O.velocity cutoff outputs
    ≡
    (0ℚ - R385.sumWeightedFluxTangent
      (globalPairs cutoff outputs positive))
      + R385.sumWeightedRemainder
        (globalPairs cutoff outputs positive)
  literalGlobalGramFluxIdentity cutoff [] positiveOutputsNil = refl
  literalGlobalGramFluxIdentity cutoff (output ∷ outputs)
      (positiveOutputsCons headPositive tailPositive) =
    let
      headPairs = O.outputPairs cutoff output headPositive
      tailPairs = globalPairs cutoff outputs tailPositive
      headIdentity = O.literalOutputGramFluxIdentity cutoff output headPositive
      tailIdentity = literalGlobalGramFluxIdentity cutoff outputs tailPositive
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
          (cong (0ℚ -_) (sym (fluxTangentAppend headPairs tailPairs)))
          (sym (remainderAppend headPairs tailPairs))))
    where
    cong : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
    cong f refl = refl

round398GlobalR378FluxUsesOnlySelectedOutputPositivity : Bool
round398GlobalR378FluxUsesOnlySelectedOutputPositivity = true

round398UnselectedIncidencePositivityRequired : Bool
round398UnselectedIncidencePositivityRequired = false

round398FiniteOutputAggregationClosed : Bool
round398FiniteOutputAggregationClosed = true
