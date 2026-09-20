module DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianR440WeldExact where

------------------------------------------------------------------------
-- PERIODIC B / INPUT-LAPLACIAN CENTERED RESIDUAL -> R294/R440 AMPLITUDE
--
-- The vector d1b2 reduction leaves the fixed-output input multiplier
--
--   S_tau = |p_tau|^2 + |q_tau|^2.
--
-- S_tau is exactly invariant under the physical p/q swap, so it defines a
-- legitimate R294.SwapInvariantCellWeight.  The corresponding R440 weighted
-- amplitude cell is definitionally the physical mixed (+,-) cell multiplied
-- by S_tau.
--
-- Hence the weighted vector sum appearing in the centered input-Laplacian
-- residual is the SAME R440 weightedAmplitudeAggregate already used by the
-- canonical signed quadratic-companion lane.
--
-- This is a representation weld only: no norm or spacetime estimate is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredInputLaplacianVectorResidualExact as Input

F : C3.RealField _
F = Rational.rationalRealField

inputMassSwapInvariant :
  ∀ {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence) →
  Input.inputMultiplier I (Symmetry.swapTriad tau)
  ≡ Input.inputMultiplier I tau
inputMassSwapInvariant I tau =
  trans
    (cong₂ _+_
      (cong (C3.normSquared I) (Symmetry.swapTriadP tau))
      (cong (C3.normSquared I) (Symmetry.swapTriadQ tau)))
    (solve
      ( C3.normSquared I (Physical.p tau)
      ∷ C3.normSquared I (Physical.q tau)
      ∷ []))

inputMassWeight :
  ∀ {E : C3.IntegerEmbedding F} →
  (I : C3.ModeInverseSquare F E) →
  R294.SwapInvariantCellWeight F
inputMassWeight I = record
  { R294.weight =
      λ tau → C3.realEmbed F (Input.inputMultiplier I tau)
  ; R294.swapInvariant =
      λ tau → cong (C3.realEmbed F) (inputMassSwapInvariant I tau)
  }

module PhysicalInputWeight
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I) where

  velocity = Audit.velocity system
  value = R224.mixedPlusMinus S velocity

  inputWeightedCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  inputWeightedCell tau =
    R291.realScale (Input.inputMultiplier I tau) (value tau)

  r440InputWeightedCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  r440InputWeightedCell =
    R440.weightedAmplitudeCell (inputMassWeight I) S system

  inputWeightedCellIsR440 :
    (tau : Physical.PhysicalTriadIncidence) →
    inputWeightedCell tau ≡ r440InputWeightedCell tau
  inputWeightedCellIsR440 tau = refl

  inputWeightedFoldIsR440 :
    (items : List Physical.PhysicalTriadIncidence) →
    Vector.weightedVectorSum (Input.inputMultiplier I) value items
    ≡ R440.weightedAmplitudeAggregate
        (inputMassWeight I) S system items
  inputWeightedFoldIsR440 [] = refl
  inputWeightedFoldIsR440 (tau ∷ rest) =
    cong₂ C3.complex3Add
      (inputWeightedCellIsR440 tau)
      (inputWeightedFoldIsR440 rest)

inputLaplacianWeightIsSwapInvariant : Bool
inputLaplacianWeightIsSwapInvariant = true

inputWeightedAmplitudeIsLiteralR440Aggregate : Bool
inputWeightedAmplitudeIsLiteralR440Aggregate = true

inputLaplacianResidualNowOnCanonicalR294R440Carrier : Bool
inputLaplacianResidualNowOnCanonicalR294R440Carrier = true

quantitativeR440InputLaplacianCovariancePaymentClosedHere : Bool
quantitativeR440InputLaplacianCovariancePaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

inputLaplacianWeightIsSwapInvariantIsTrue :
  inputLaplacianWeightIsSwapInvariant ≡ true
inputLaplacianWeightIsSwapInvariantIsTrue = refl
