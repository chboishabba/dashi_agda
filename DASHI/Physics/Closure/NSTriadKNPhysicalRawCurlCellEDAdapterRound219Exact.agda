module DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDAdapterRound219Exact where

------------------------------------------------------------------------
-- ROUND219 / PHYSICAL ADAPTERS FOR THE ROUND217 CELL-MASS PAYMENT
--
-- This closes the two routine same-object seams around Round217:
--
--   (1) the R178 physical raw-curl cell is converted directly to
--       `RawCellRadialData` using Round218's literal resonance square triangle;
--
--   (2) the literal physical modal energy
--           E_m = ||u_m||^2
--       and dissipation
--           D_m = |m|^2 ||u_m||^2
--       instantiate Round109's arbitrary Boolean selected-pair theorem.
--
-- Thus resonance/helicity/Bony selection may be encoded entirely in the
-- selector without introducing a Fourier-cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNRawCurlCellMassEnergyDissipationRound217Exact as R217
import DASHI.Physics.Closure.NSTriadKNPhysicalResonantEuclideanSquareTriangleRound218Exact as R218

F : C3.RealField _
F = Rational.rationalRealField

modeSquareNonnegative :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (mode : Z3.FourierMode) →
  0ℚ ≤ C3.normSquared I mode
modeSquareNonnegative E I mode =
  subst
    (0ℚ ≤_)
    (R96.modeVectorNormSquaredMeaning E I mode)
    (Separation.complex3NormSquaredNonnegative (C3.modeVector E mode))

physicalRawCurlCellRadialData :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  {p q k : Z3.FourierMode}
  (uP uQ : C3.Complex3 F) →
  (resonance : Z3.Resonance p q k) →
  Helical.Transverse E p uP →
  Helical.Transverse E q uQ →
  R217.RawCellRadialData
physicalRawCurlCellRadialData E I {p} {q} {k}
    uP uQ resonance pTrans qTrans = record
  { R217.cellMass =
      L2.complex3NormSquared
        (R145.slotKernel (C3.modeVector E p) (C3.modeVector E q) uP uQ)
  ; R217.outputSquare = C3.normSquared I k
  ; R217.pSquare = C3.normSquared I p
  ; R217.qSquare = C3.normSquared I q
  ; R217.energyP = L2.complex3NormSquared uP
  ; R217.energyQ = L2.complex3NormSquared uQ
  ; R217.cellMassNN = Separation.complex3NormSquaredNonnegative
      (R145.slotKernel (C3.modeVector E p) (C3.modeVector E q) uP uQ)
  ; R217.outputSquareNN = modeSquareNonnegative E I k
  ; R217.pSquareNN = modeSquareNonnegative E I p
  ; R217.qSquareNN = modeSquareNonnegative E I q
  ; R217.energyPNN = Separation.complex3NormSquaredNonnegative uP
  ; R217.energyQNN = Separation.complex3NormSquaredNonnegative uQ
  ; R217.rawCurlMassBound =
      R178.rawLowOutputKernelMassBound E I uP uQ resonance pTrans qTrans
  ; R217.resonantSquareTriangle =
      R218.resonantEuclideanSquareTriangle E I resonance
  }

physicalRawCurlCellMassBelowEighteenEDKernel :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  {p q k : Z3.FourierMode}
  (uP uQ : C3.Complex3 F) →
  (resonance : Z3.Resonance p q k) →
  (pTrans : Helical.Transverse E p uP) →
  (qTrans : Helical.Transverse E q uQ) →
  R217.cellMass
    (physicalRawCurlCellRadialData E I uP uQ resonance pTrans qTrans)
  ≤ R217.eighteen *
      R217.pairEDKernel
        (physicalRawCurlCellRadialData E I uP uQ resonance pTrans qTrans)
physicalRawCurlCellMassBelowEighteenEDKernel
    E I uP uQ resonance pTrans qTrans =
  R217.rawCellMassBelowEighteenEDKernel
    (physicalRawCurlCellRadialData E I uP uQ resonance pTrans qTrans)

physicalModalED :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  R109.ModalEnergyDissipation Z3.FourierMode
physicalModalED E I velocity = record
  { R109.energy = λ mode → L2.complex3NormSquared (velocity mode)
  ; R109.dissipation = λ mode →
      C3.normSquared I mode * L2.complex3NormSquared (velocity mode)
  ; R109.energyNonnegative = λ mode →
      Separation.complex3NormSquaredNonnegative (velocity mode)
  ; R109.dissipationNonnegative = λ mode →
      R96.productNonnegative
        (modeSquareNonnegative E I mode)
        (Separation.complex3NormSquaredNonnegative (velocity mode))
  }

physicalSelectedPairEDBound :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (velocity : Z3.FourierMode → C3.Complex3 F)
  (select : Z3.FourierMode → Z3.FourierMode → Bool)
  (modes : List Z3.FourierMode) →
  R109.selectedOrderedPairSum (physicalModalED E I velocity) select modes modes
  ≤
  (R109.sumEnergy (physicalModalED E I velocity) modes
    * R109.sumDissipation (physicalModalED E I velocity) modes)
  +
  (R109.sumEnergy (physicalModalED E I velocity) modes
    * R109.sumDissipation (physicalModalED E I velocity) modes)
physicalSelectedPairEDBound E I velocity select modes =
  R109.selectedPairEnergyDissipationProductBound
    (physicalModalED E I velocity) select modes

round219PhysicalResonanceRadiusAdapterClosed : Bool
round219PhysicalResonanceRadiusAdapterClosed = true

round219PhysicalSelectorEDAdapterClosed : Bool
round219PhysicalSelectorEDAdapterClosed = true

round219IntroducesCardinalityTax : Bool
round219IntroducesCardinalityTax = false

round219CoherentGramResidualPaid : Bool
round219CoherentGramResidualPaid = false

round219PackageAClosed : Bool
round219PackageAClosed = false

round219ClayPromotion : Bool
round219ClayPromotion = false

round219PhysicalResonanceRadiusAdapterClosedIsTrue :
  round219PhysicalResonanceRadiusAdapterClosed ≡ true
round219PhysicalResonanceRadiusAdapterClosedIsTrue = refl

round219PhysicalSelectorEDAdapterClosedIsTrue :
  round219PhysicalSelectorEDAdapterClosed ≡ true
round219PhysicalSelectorEDAdapterClosedIsTrue = refl

round219IntroducesCardinalityTaxIsFalse :
  round219IntroducesCardinalityTax ≡ false
round219IntroducesCardinalityTaxIsFalse = refl

round219PackageAClosedIsFalse : round219PackageAClosed ≡ false
round219PackageAClosedIsFalse = refl

round219ClayPromotionIsFalse : round219ClayPromotion ≡ false
round219ClayPromotionIsFalse = refl
