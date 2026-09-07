module DASHI.Physics.Closure.NSTriadKNPhysicalCauchyResolventCompletionRound447Exact where

------------------------------------------------------------------------
-- ROUND447 / PHYSICAL NONZERO OUTPUT FIBRE -> R297 CAUCHY COMPLETION
--
-- R400 proves that every double-mixed cell on a selected nonzero output fibre
-- has a strictly positive viscous cell rate.  R446 proves the full rational
-- Cauchy-weighted Hermitian form on any such finite Complex3 family is
-- nonnegative.  This file attaches those two results to the literal physical
-- fibre and constructs R297's PositiveResolventCompletion directly.
--
-- The full form is split definitionally into diagonal plus unordered
-- off-diagonal terms.  The next same-object weld is only to identify this
-- off-diagonal scalar with R397/R385 `sumWeightedFlux`; no positivity or heat
-- representation remains in that step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNResolventEndpointCompletionRound297Exact as R297

F : C3.RealField _
F = Rational.rationalRealField

diagonalForm : List R446.PositiveRateComplex3Cell → ℚ
diagonalForm [] = 0ℚ
diagonalForm (cell ∷ rest) =
  R446.cauchyKernel cell cell
    * R446.R179.realHermitianCross (R446.value cell) (R446.value cell)
  + diagonalForm rest

offDiagonalRow :
  R446.PositiveRateComplex3Cell →
  List R446.PositiveRateComplex3Cell → ℚ
offDiagonalRow head [] = 0ℚ
offDiagonalRow head (cell ∷ rest) =
  (1ℚ + 1ℚ) * R446.cauchyKernel head cell
    * R446.R179.realHermitianCross (R446.value head) (R446.value cell)
  + offDiagonalRow head rest

offDiagonalForm : List R446.PositiveRateComplex3Cell → ℚ
offDiagonalForm [] = 0ℚ
offDiagonalForm (head ∷ rest) =
  offDiagonalRow head rest + offDiagonalForm rest

hermitianFormSplits :
  (cells : List R446.PositiveRateComplex3Cell) →
  R446.hermitianCauchyForm cells
  ≡ diagonalForm cells + offDiagonalForm cells
hermitianFormSplits [] = refl
hermitianFormSplits (head ∷ rest) =
  trans
    (cong₂ _+_ refl (hermitianFormSplits rest))
    (solve
      ( R446.cauchyKernel head head
      ∷ R446.R179.realHermitianCross (R446.value head) (R446.value head)
      ∷ R446.hermitianRow head rest
      ∷ diagonalForm rest
      ∷ offDiagonalRow head rest
      ∷ offDiagonalForm rest ∷ []))

module PhysicalOutputCauchy
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Data.Rational.Positive (Field30.viscosity physicalSystem))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module P = R389.DoubleMixedPair physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  buildCells :
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      tau R396._OccursIn_ items → Physical.k tau ≡ output) →
    List R446.PositiveRateComplex3Cell
  buildCells [] allOutput = []
  buildCells (tau ∷ rest) allOutput =
    R446.positive-rate-complex3-cell
      (P.D.Pair.cellRate tau)
      (R225.doubleMixedCell S P.D.Pair.velocity tau)
      (Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero tau (allOutput tau R396.here))
    ∷ buildCells rest
        (λ selected member → allOutput selected (R396.there member))

  physicalCells : List R446.PositiveRateComplex3Cell
  physicalCells =
    buildCells fibre (Rate.allElementsHaveOutput cutoff output)

  full : ℚ
  full = R446.hermitianCauchyForm physicalCells

  diagonal : ℚ
  diagonal = diagonalForm physicalCells

  offDiagonal : ℚ
  offDiagonal = offDiagonalForm physicalCells

  fullNonnegative : 0ℚ ≤ full
  fullNonnegative = R446.hermitianCauchyFormNonnegative physicalCells

  fullSplits : full ≡ diagonal + offDiagonal
  fullSplits = hermitianFormSplits physicalCells

  positiveResolventCompletion : R297.PositiveResolventCompletion
  positiveResolventCompletion = R297.positive-resolvent-completion
    full diagonal offDiagonal fullSplits fullNonnegative

  negativeOffDiagonalPaidByDiagonal :
    0ℚ - offDiagonal ≤ diagonal
  negativeOffDiagonalPaidByDiagonal =
    R297.negativeOffDiagonalPaidByDiagonal positiveResolventCompletion

round447PhysicalNonzeroOutputCauchyCompletionClosed : Bool
round447PhysicalNonzeroOutputCauchyCompletionClosed = true

round447R297FullCauchyPositivityInstalled : Bool
round447R297FullCauchyPositivityInstalled = true

round447OffDiagonalIdentifiedWithR397WeightedFlux : Bool
round447OffDiagonalIdentifiedWithR397WeightedFlux = false

round447HeatRepresentationRequired : Bool
round447HeatRepresentationRequired = false

round447PhysicalDiagonalEndpointPaid : Bool
round447PhysicalDiagonalEndpointPaid = false

round447PackageAClosed : Bool
round447PackageAClosed = false

round447ClayPromotion : Bool
round447ClayPromotion = false

round447HeatRepresentationRequiredIsFalse :
  round447HeatRepresentationRequired ≡ false
round447HeatRepresentationRequiredIsFalse = refl

round447OffDiagonalIdentifiedWithR397WeightedFluxIsFalse :
  round447OffDiagonalIdentifiedWithR397WeightedFlux ≡ false
round447OffDiagonalIdentifiedWithR397WeightedFluxIsFalse = refl
