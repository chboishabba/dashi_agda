module DASHI.Physics.Closure.NSTriadKNGlobalSelfFluxEndpointRound558Exact where

------------------------------------------------------------------------
-- ROUND558 / GLOBAL SELF-FLUX ENDPOINT WITHOUT OUTPUT COUNT
--
-- R549 gives, at one output,
--
--   selfFlux_k = 2 * R447.diagonal_k.
--
-- Do NOT insert the collapsed R457 48 E^2 bound independently per output.
-- Instead keep the physical mass visible:
--
--   selfFlux_k <= 2 W mass_k,
--   sum_k mass_k <= 48 E_N^2                 (R462).
--
-- This yields a global endpoint with no output-cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; nonNegative; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalR298WeldRound451Exact as R451
import DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact as R452
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact as R456
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalEnergySquareEndpointRound457Exact as R457
import DASHI.Physics.Closure.NSTriadKNGlobalNormalizedCompanionMassRound462Exact as R462
import DASHI.Physics.Closure.NSTriadKNDiagonalSelfFluxToR447Round549Exact as R549
import DASHI.Physics.Closure.NSTriadKNDiagonalSelfFluxEndpointCompilerRound554Exact as R554

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

twoNonnegative : 0ℚ ≤ two
twoNonnegative =
  let
    summed : 0ℚ + 0ℚ ≤ 1ℚ + 1ℚ
    summed = ℚP.+-mono-≤ ℚP.0≤1 ℚP.0≤1
    zeroPlusZero : 0ℚ + 0ℚ ≡ 0ℚ
    zeroPlusZero = solve []
  in
  subst (λ lower → lower ≤ two) zeroPlusZero summed

module GlobalSelfFlux
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws
      F (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (Pdata : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem)))
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem)
    (radiusCalibration :
      R456.PhysicalModeRadiusCalibration
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem) S)
    (cutoff : Nat) where

  velocity = Audit.velocityAt (Field30.finiteSystem physicalSystem)
  outputs = Canonical.nonzeroCutoffModes cutoff

  module Floor = R450.PhysicalCellRateFloor
    physicalSystem S viscosityPositive unitGap
  module Mass = R462.PhysicalGlobalMass S Pdata radiusCalibration cutoff

  nu : ℚ
  nu = Field30.viscosity physicalSystem

  W : ℚ
  W = R449.diagonalCeilingAt nu Floor.nuPositive

  WNN : 0ℚ ≤ W
  WNN = R451.PhysicalDiagonalWeld.ceilingNonnegative
    physicalSystem S viscosityPositive unitGap cutoff Z3.zeroMode
    (record { Z3.notZero = λ () })

  twoW : ℚ
  twoW = two * W

  twoWNN : 0ℚ ≤ twoW
  twoWNN =
    let
      instance
        twoNNI : NonNegative two
        twoNNI = nonNegative twoNonnegative
        WNNI : NonNegative W
        WNNI = nonNegative WNN
        productNNI = ℚP.nonNeg*nonNeg⇒nonNeg two W
    in ℚP.nonNegative⁻¹ twoW

  outputSelfFlux :
    (output : Z3.FourierMode) → Z3.NonZeroMode output → ℚ
  outputSelfFlux output outputNonzero =
    let
      module Fout = R549.PhysicalSelfFlux
        physicalSystem S viscosityPositive cutoff output outputNonzero
    in Fout.literalSelfFluxSum

  outputSelfFluxNonnegative :
    (output : Z3.FourierMode) → (outputNonzero : Z3.NonZeroMode output) →
    0ℚ ≤ outputSelfFlux output outputNonzero
  outputSelfFluxNonnegative output outputNonzero =
    let
      module E = R554.Endpoint
        physicalSystem S L H viscosityPositive unitGap radiusCalibration
        cutoff output outputNonzero
    in E.literalSelfFluxNonnegative

  outputSelfFluxBelowMass :
    (output : Z3.FourierMode) → (outputNonzero : Z3.NonZeroMode output) →
    outputSelfFlux output outputNonzero
    ≤ twoW * R456.sumDoubleMixedMass S velocity
        (DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber.physicalOutputFiber
          cutoff output)
  outputSelfFluxBelowMass output outputNonzero =
    let
      module Fout = R549.PhysicalSelfFlux
        physicalSystem S viscosityPositive cutoff output outputNonzero
      module D = R451.PhysicalDiagonalWeld
        physicalSystem S viscosityPositive unitGap cutoff output outputNonzero
      module E = R457.PhysicalDiagonalEndpoint
        physicalSystem S L H viscosityPositive unitGap radiusCalibration
        cutoff output outputNonzero

      diagonalUpper = D.r447DiagonalBelowCeilingMass
      massMeaning = E.massSumIsPhysicalMass

      scaled :
        two * Fout.Completion.diagonal ≤ two * (W * D.massSum)
      scaled =
        let instance twoNN = nonNegative twoNonnegative
        in ℚP.*-monoˡ-≤-nonNeg two diagonalUpper

      physicalMassScaled :
        two * Fout.Completion.diagonal
        ≤ twoW * R456.sumDoubleMixedMass S velocity
            (DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber.physicalOutputFiber
              cutoff output)
      physicalMassScaled =
        subst
          (λ selected →
            two * Fout.Completion.diagonal
            ≤ twoW * selected)
          massMeaning
          (subst
            (two * Fout.Completion.diagonal ≤_)
            (solve (two ∷ W ∷ D.massSum ∷ []))
            scaled)
    in
    subst
      (λ lower →
        lower ≤ twoW * R456.sumDoubleMixedMass S velocity
          (DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber.physicalOutputFiber
            cutoff output))
      Fout.literalSelfFluxIsTwiceR447Diagonal
      physicalMassScaled

  outputListSelfFlux :
    (selected : List Z3.FourierMode) →
    ((output : Z3.FourierMode) → output Cube.∈ selected → Z3.NonZeroMode output) → ℚ
  outputListSelfFlux [] allNonzero = 0ℚ
  outputListSelfFlux (output ∷ rest) allNonzero =
    outputSelfFlux output (allNonzero output (Cube.here refl))
    + outputListSelfFlux rest
        (λ selected member → allNonzero selected (Cube.there member))

  outputListSelfFluxNonnegative :
    (selected : List Z3.FourierMode) →
    (allNonzero :
      (output : Z3.FourierMode) → output Cube.∈ selected → Z3.NonZeroMode output) →
    0ℚ ≤ outputListSelfFlux selected allNonzero
  outputListSelfFluxNonnegative [] allNonzero = ℚP.≤-refl
  outputListSelfFluxNonnegative (output ∷ rest) allNonzero =
    Rational.addNonnegative
      (outputSelfFluxNonnegative output
        (allNonzero output (Cube.here refl)))
      (outputListSelfFluxNonnegative rest
        (λ selected member → allNonzero selected (Cube.there member)))

  outputListSelfFluxBelowMass :
    (selected : List Z3.FourierMode) →
    (allNonzero :
      (output : Z3.FourierMode) → output Cube.∈ selected → Z3.NonZeroMode output) →
    outputListSelfFlux selected allNonzero
    ≤ twoW * R462.outputMassSum S velocity cutoff selected
  outputListSelfFluxBelowMass [] allNonzero =
    subst (0ℚ ≤_) (solve (twoW ∷ [])) ℚP.≤-refl
  outputListSelfFluxBelowMass (output ∷ rest) allNonzero =
    let
      headNN = allNonzero output (Cube.here refl)
      headPaid = outputSelfFluxBelowMass output headNN
      tailPaid = outputListSelfFluxBelowMass rest
        (λ selected member → allNonzero selected (Cube.there member))
      added = ℚP.+-mono-≤ headPaid tailPaid
    in
    subst
      (λ upper → outputListSelfFlux (output ∷ rest) allNonzero ≤ upper)
      (solve
        (twoW
          ∷ R456.sumDoubleMixedMass S velocity
            (DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber.physicalOutputFiber
              cutoff output)
          ∷ R462.outputMassSum S velocity cutoff rest
          ∷ []))
      added

  canonicalNonzero :
    (output : Z3.FourierMode) → output Cube.∈ outputs → Z3.NonZeroMode output
  canonicalNonzero output member = R404.nonzeroCutoffMemberNonzero member

  globalSelfFlux : ℚ
  globalSelfFlux = outputListSelfFlux outputs canonicalNonzero

  globalSelfFluxNonnegative : 0ℚ ≤ globalSelfFlux
  globalSelfFluxNonnegative =
    outputListSelfFluxNonnegative outputs canonicalNonzero

  globalSelfFluxBelowSelectedMass :
    globalSelfFlux ≤ twoW * Mass.selectedMass
  globalSelfFluxBelowSelectedMass =
    outputListSelfFluxBelowMass outputs canonicalNonzero

  globalSelfFluxEnergySquareEndpoint :
    globalSelfFlux ≤ twoW * (R452.fortyEight * Mass.energySquare)
  globalSelfFluxEnergySquareEndpoint =
    ℚP.≤-trans globalSelfFluxBelowSelectedMass
      (let instance twoWNNI : NonNegative twoW = nonNegative twoWNN
       in ℚP.*-monoˡ-≤-nonNeg
          twoW Mass.globalNonzeroOutputMassBelowEnergySquare)

round558GlobalSelfFluxEndpointClosed : Bool
round558GlobalSelfFluxEndpointClosed = true

round558OutputCardinalityTaxIntroduced : Bool
round558OutputCardinalityTaxIntroduced = false

round558GlobalSelfFluxNonnegativeClosed : Bool
round558GlobalSelfFluxNonnegativeClosed = true

round558FactoredFullSpacetimeBoundClosed : Bool
round558FactoredFullSpacetimeBoundClosed = false

round558ClayPromotion : Bool
round558ClayPromotion = false

round558GlobalSelfFluxEndpointClosedIsTrue :
  round558GlobalSelfFluxEndpointClosed ≡ true
round558GlobalSelfFluxEndpointClosedIsTrue = refl

round558OutputCardinalityTaxIntroducedIsFalse :
  round558OutputCardinalityTaxIntroduced ≡ false
round558OutputCardinalityTaxIntroducedIsFalse = refl

round558ClayPromotionIsFalse : round558ClayPromotion ≡ false
round558ClayPromotionIsFalse = refl
