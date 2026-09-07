module DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalR298WeldRound451Exact where

------------------------------------------------------------------------
-- ROUND451 / PHYSICAL R447 DIAGONAL -> R449/R298 SAME-OBJECT WELD
--
-- R447's diagonal is the finite sum
--
--   sum_tau K(rho_tau,rho_tau) Re<D_tau,D_tau>.
--
-- R450 supplies rho_tau >= nu on a canonically normalized nonzero output
-- fibre.  R446 identifies Re<D,D> with the sum of six rational squares, hence
-- each diagonal mass is nonnegative.  Therefore every physical R447 diagonal
-- cell compiles literally to an R298 WeightedDiagonalCell with common ceiling
-- 1/(2 nu).
--
-- This file proves the finite same-object equality.  It deliberately does NOT
-- claim the remaining normalized-double-mixed mass sum is already bounded by
-- R217's raw-slot ED estimate; those are different pointwise carriers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyResolventCompletionRound447Exact as R447
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNResolventDiagonalNoCardinalityRound298Exact as R298
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

F : C3.RealField _
F = Rational.rationalRealField

selfHermitianNonnegative :
  (value : C3.Complex3 F) →
  0ℚ ≤ R179.realHermitianCross value value
selfHermitianNonnegative value =
  let
    sixNN =
      Rational.addNonnegative
        (Rational.addNonnegative
          (Rational.addNonnegative
            (Rational.addNonnegative
              (Rational.addNonnegative
                (Rational.squareNonnegative (R446.xReal value))
                (Rational.squareNonnegative (R446.xImag value)))
              (Rational.squareNonnegative (R446.yReal value)))
            (Rational.squareNonnegative (R446.yImag value)))
          (Rational.squareNonnegative (R446.zReal value)))
        (Rational.squareNonnegative (R446.zImag value))
  in
  subst
    (0ℚ ≤_)
    (sym (R446.realHermitianCrossIsSixCoordinates value value))
    sixNN

module PhysicalDiagonalWeld
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (normalization : R450.CanonicalFourierUnitGap physicalSystem)
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module Floor = R450.PhysicalCellRateFloor
    physicalSystem S viscosityPositive normalization
  module Completion = R447.PhysicalOutputCauchy
    physicalSystem S viscosityPositive cutoff output outputNonzero

  nu : ℚ
  nu = Field30.viscosity physicalSystem

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  doubleMixedValue : Physical.PhysicalTriadIncidence → C3.Complex3 F
  doubleMixedValue tau = R225.doubleMixedCell S Pair.D.Pair.velocity tau

  buildRateFloorCells :
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    List (R449.DiagonalRateFloorCell nu)
  buildRateFloorCells [] allOutput = []
  buildRateFloorCells (tau ∷ rest) allOutput =
    Floor.rateFloorCell
      output outputNonzero tau (allOutput tau R396.here)
      (R179.realHermitianCross (doubleMixedValue tau) (doubleMixedValue tau))
      (selfHermitianNonnegative (doubleMixedValue tau))
    ∷ buildRateFloorCells rest
        (λ selected member → allOutput selected (R396.there member))

  rateFloorCells : List (R449.DiagonalRateFloorCell nu)
  rateFloorCells =
    buildRateFloorCells fibre (Rate.allElementsHaveOutput cutoff output)

  rateFloorFamily : R449.DiagonalRateFloorFamily nu
  rateFloorFamily = R449.diagonal-rate-floor-family
    Floor.nuPositive
    rateFloorCells

  r298Cells :
    List (R298.WeightedDiagonalCell
      (R449.diagonalCeilingAt nu Floor.nuPositive))
  r298Cells = R449.compileFamilyToR298 rateFloorFamily

  massSum : ℚ
  massSum = R298.sumMass r298Cells

  weightedDiagonal : ℚ
  weightedDiagonal = R298.sumWeightedMass r298Cells

  ceilingNonnegative :
    0ℚ ≤ R449.diagonalCeilingAt nu Floor.nuPositive
  ceilingNonnegative =
    ℚP.<⇒≤
      (Quotient.positiveReciprocalPositive
        (R449.two * nu) (R449.twicePositive Floor.nuPositive))

  weightedDiagonalBelowCeilingMass :
    weightedDiagonal
    ≤ R449.diagonalCeilingAt nu Floor.nuPositive * massSum
  weightedDiagonalBelowCeilingMass =
    R298.weightedDiagonalBelowCeilingMass
      (R449.diagonalCeilingAt nu Floor.nuPositive)
      ceilingNonnegative
      r298Cells

  builtWeightedDiagonalExact :
    (items : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    R298.sumWeightedMass
      (R449.compileCells Floor.nuPositive
        (buildRateFloorCells items allOutput))
    ≡ R447.diagonalForm (Completion.buildCells items allOutput)
  builtWeightedDiagonalExact [] allOutput = refl
  builtWeightedDiagonalExact (tau ∷ rest) allOutput =
    cong₂ _+_ refl
      (builtWeightedDiagonalExact rest
        (λ selected member → allOutput selected (R396.there member)))

  weightedDiagonalIsR447Diagonal :
    weightedDiagonal ≡ Completion.diagonal
  weightedDiagonalIsR447Diagonal =
    builtWeightedDiagonalExact
      fibre (Rate.allElementsHaveOutput cutoff output)

  r447DiagonalBelowCeilingMass :
    Completion.diagonal
    ≤ R449.diagonalCeilingAt nu Floor.nuPositive * massSum
  r447DiagonalBelowCeilingMass =
    subst
      (λ selected → selected
        ≤ R449.diagonalCeilingAt nu Floor.nuPositive * massSum)
      weightedDiagonalIsR447Diagonal
      weightedDiagonalBelowCeilingMass

round451PhysicalR447DiagonalCompilesToR298 : Bool
round451PhysicalR447DiagonalCompilesToR298 = true

round451LiteralWeightedDiagonalEqualsR447Diagonal : Bool
round451LiteralWeightedDiagonalEqualsR447Diagonal = true

round451SelfHermitianMassNonnegativeClosed : Bool
round451SelfHermitianMassNonnegativeClosed = true

round451DiagonalResolventWeightCeilingClosedGivenCanonicalUnitGap : Bool
round451DiagonalResolventWeightCeilingClosedGivenCanonicalUnitGap = true

round451NormalizedDoubleMixedMassBudgetClosed : Bool
round451NormalizedDoubleMixedMassBudgetClosed = false

round451RawR217MassSilentlyReusedForNormalizedCell : Bool
round451RawR217MassSilentlyReusedForNormalizedCell = false

round451PackageAClosed : Bool
round451PackageAClosed = false

round451ClayPromotion : Bool
round451ClayPromotion = false
