module DASHI.Physics.Closure.NSTriadKNR567HelicityResolvedForcingSquareExact where

------------------------------------------------------------------------
-- PERIODIC B / R567 FORCING SQUARE -> HOMOCHIRAL + HETEROCHIRAL EXACT SPLIT
--
-- The existing spectator/nested weld proves that the surviving R567 forcing
-- full square is the sum of spectator rows built from R573's nested four-sign
-- carrier.  R573HomochiralHeterochiralSplitExact now splits each literal
-- weighted nested cell before norms:
--
--   nestedCell = homochiralCell + heterochiralCell.
--
-- This owner pushes that identity through the finite inner fold, Hermitian
-- spectator pairing, and outer spectator sum.  Hence the ACTUAL R567 forcing
-- full square decomposes exactly into:
--
--   forcingFull = homochiralForcingFull + heterochiralForcingFull.
--
-- No absolute value, triangle inequality, Schur step, shell count, fibre
-- cardinality or spacetime majorization is introduced.  The homochiral term is
-- the only term eligible for the preferred R571 radial Taylor/M2 route; the
-- heterochiral term remains on its distinct HH->low / non-HH geometry route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNFactoredFullTransposeSymmetryRound566Exact as R566
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedForcingSquareBidiExact as BaseWeld
import DASHI.Physics.Closure.NSTriadKNR573HomochiralHeterochiralSplitExact as Split573
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543

F : C3.RealField _
F = Rational.rationalRealField

module Resolved
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  system = Field30.finiteSystem physicalSystem

  module Base = BaseWeld.Weld physicalSystem S L H velocityTransverse
  module Row = R545.Row physicalSystem S
  module T = R566.PhysicalTranspose physicalSystem S
  module Spec = R541.Spectator physicalSystem S

  module HSplit (beta : Physical.PhysicalTriadIncidence) =
    Split573.Split
      (Spec.spectatorWeight beta) S L H system velocityTransverse

  homochiralNestedVector :
    (output : Z3.FourierMode) →
    Physical.PhysicalTriadIncidence →
    C3.Complex3 F
  homochiralNestedVector output beta =
    R224.foldVector
      (HSplit.homochiralWeightedCompanionCell beta)
      (Output.physicalOutputFiber (Audit.cutoff system) output)

  heterochiralNestedVector :
    (output : Z3.FourierMode) →
    Physical.PhysicalTriadIncidence →
    C3.Complex3 F
  heterochiralNestedVector output beta =
    R224.foldVector
      (HSplit.heterochiralWeightedCompanionCell beta)
      (Output.physicalOutputFiber (Audit.cutoff system) output)

  homochiralForcingRow :
    Z3.FourierMode →
    Physical.PhysicalTriadIncidence → ℚ
  homochiralForcingRow output beta =
    R179.realHermitianCross
      (homochiralNestedVector output beta)
      (Row.doubleCell beta)

  heterochiralForcingRow :
    Z3.FourierMode →
    Physical.PhysicalTriadIncidence → ℚ
  heterochiralForcingRow output beta =
    R179.realHermitianCross
      (heterochiralNestedVector output beta)
      (Row.doubleCell beta)

  foldNestedWeightedCellSplit :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output
        module N = Base.Nested beta
    in
    R224.foldVector N.nestedWeightedCompanionCell items
    ≡
    C3.complex3Add
      (homochiralNestedVector output beta)
      (heterochiralNestedVector output beta)
  foldNestedWeightedCellSplit output beta =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      module N = Base.Nested beta
      whole = N.nestedWeightedCompanionCell
      split =
        λ alpha →
          C3.complex3Add
            (HSplit.homochiralWeightedCompanionCell beta alpha)
            (HSplit.heterochiralWeightedCompanionCell beta alpha)
    in
    trans
      (foldCong whole split items
        (HSplit.nestedWeightedCellIsHomoPlusHetero beta))
      (R230.foldAdd
        (HSplit.homochiralWeightedCompanionCell beta)
        (HSplit.heterochiralWeightedCompanionCell beta)
        items)
    where
    foldCong :
      (f g : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
      (items : List Physical.PhysicalTriadIncidence) →
      ((x : Physical.PhysicalTriadIncidence) → f x ≡ g x) →
      R224.foldVector f items ≡ R224.foldVector g items
    foldCong f g [] pointwise = refl
    foldCong f g (x ∷ xs) pointwise =
      cong₂ C3.complex3Add
        (pointwise x)
        (foldCong f g xs pointwise)

  nestedForcingRowIsHomoPlusHetero :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    Base.nestedForcingRow output beta
    ≡
    homochiralForcingRow output beta
      + heterochiralForcingRow output beta
  nestedForcingRowIsHomoPlusHetero output beta =
    trans
      (cong
        (λ value →
          R179.realHermitianCross value (Row.doubleCell beta))
        (foldNestedWeightedCellSplit output beta))
      (R291.realCrossAddLeft
        (homochiralNestedVector output beta)
        (heterochiralNestedVector output beta)
        (Row.doubleCell beta))

  sumHomochiralRows :
    Z3.FourierMode →
    List Physical.PhysicalTriadIncidence → ℚ
  sumHomochiralRows output [] = 0ℚ
  sumHomochiralRows output (beta ∷ rest) =
    homochiralForcingRow output beta
      + sumHomochiralRows output rest

  sumHeterochiralRows :
    Z3.FourierMode →
    List Physical.PhysicalTriadIncidence → ℚ
  sumHeterochiralRows output [] = 0ℚ
  sumHeterochiralRows output (beta ∷ rest) =
    heterochiralForcingRow output beta
      + sumHeterochiralRows output rest

  allNestedRowsSplit :
    (output : Z3.FourierMode) →
    (items : List Physical.PhysicalTriadIncidence) →
    Base.allNestedForcingRows output items
    ≡
    sumHomochiralRows output items
      + sumHeterochiralRows output items
  allNestedRowsSplit output [] = refl
  allNestedRowsSplit output (beta ∷ rest)
    rewrite nestedForcingRowIsHomoPlusHetero output beta
          | allNestedRowsSplit output rest =
    solve
      ( homochiralForcingRow output beta
      ∷ heterochiralForcingRow output beta
      ∷ sumHomochiralRows output rest
      ∷ sumHeterochiralRows output rest
      ∷ [])

  homochiralForcingFull : Z3.FourierMode → ℚ
  homochiralForcingFull output =
    sumHomochiralRows output
      (Output.physicalOutputFiber (Audit.cutoff system) output)

  heterochiralForcingFull : Z3.FourierMode → ℚ
  heterochiralForcingFull output =
    sumHeterochiralRows output
      (Output.physicalOutputFiber (Audit.cutoff system) output)

  forcingFullHelicityResolved :
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    R543.fullSquareSum T.forcingPair items
    ≡
    homochiralForcingFull output + heterochiralForcingFull output
  forcingFullHelicityResolved output =
    trans
      (Base.forcingFullIsNestedSpectatorRows output)
      (allNestedRowsSplit output
        (Output.physicalOutputFiber (Audit.cutoff system) output))

r567ForcingFullHelicityResolvedExactly : Bool
r567ForcingFullHelicityResolvedExactly = true

r567HomochiralM2RouteSeparatedFromHeterochiralRoute : Bool
r567HomochiralM2RouteSeparatedFromHeterochiralRoute = true

r567HelicitySplitIntroducesPositiveMajorant : Bool
r567HelicitySplitIntroducesPositiveMajorant = false

r567HelicitySplitIntroducesCardinalityTax : Bool
r567HelicitySplitIntroducesCardinalityTax = false

r567WholeForcingSquarePaidHere : Bool
r567WholeForcingSquarePaidHere = false

clayPromotion : Bool
clayPromotion = false

r567ForcingFullHelicityResolvedExactlyIsTrue :
  r567ForcingFullHelicityResolvedExactly ≡ true
r567ForcingFullHelicityResolvedExactlyIsTrue = refl

r567HelicitySplitIntroducesPositiveMajorantIsFalse :
  r567HelicitySplitIntroducesPositiveMajorant ≡ false
r567HelicitySplitIntroducesPositiveMajorantIsFalse = refl
