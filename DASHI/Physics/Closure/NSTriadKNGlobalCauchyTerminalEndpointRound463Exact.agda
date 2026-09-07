module DASHI.Physics.Closure.NSTriadKNGlobalCauchyTerminalEndpointRound463Exact where

------------------------------------------------------------------------
-- ROUND463 / GLOBAL R398 CAUCHY TERMINAL ENDPOINT WITHOUT OUTPUT COUNT
--
-- R458 paid one fixed-output negative weighted flux, but applying its already-
-- collapsed 48 E_N^2 bound independently at every output would introduce an
-- output-cardinality factor.  The correct route keeps the per-output mass
-- visible until AFTER output aggregation:
--
--   -F_k <= diagonal_k <= W mass_k,
--   -sum_k F_k <= W sum_k mass_k,
--   sum_k mass_k <= 48 E_N^2                  (R462).
--
-- R398's actual global pair list is the concatenation of the literal output
-- pair lists.  This owner works on that exact list.  R448's generic finite
-- equality is used with the SAME positivity witness carried by R398, so no
-- proof-irrelevance or replacement pair family is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_++_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; Positive; NonNegative; nonNegative; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378GlobalInstantaneousGramFluxRound398Exact as R398
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyOffDiagonalR397WeldRound448Exact as R448
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalR298WeldRound451Exact as R451
import DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact as R452
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact as R456
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalEnergySquareEndpointRound457Exact as R457
import DASHI.Physics.Closure.NSTriadKNGlobalNormalizedCompanionMassRound462Exact as R462
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

F : C3.RealField _
F = Rational.rationalRealField

sumWeightedFluxAppend :
  (left right : List R290.DampedGramPair) →
  R385.sumWeightedFlux (left ++ right)
  ≡ R385.sumWeightedFlux left + R385.sumWeightedFlux right
sumWeightedFluxAppend [] right = refl
sumWeightedFluxAppend (pair ∷ rest) right
  rewrite sumWeightedFluxAppend rest right = refl

module GlobalTerminalEndpoint
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

  module Global = R398.GlobalFluxLocal physicalSystem S L H Pdata
  module Local = R396.LocalEnumerate physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module Floor = R450.PhysicalCellRateFloor
    physicalSystem S viscosityPositive unitGap
  module Mass = R462.PhysicalGlobalMass S Pdata radiusCalibration cutoff

  nu : ℚ
  nu = Field30.viscosity physicalSystem

  W : ℚ
  W = R449.diagonalCeilingAt nu Floor.nuPositive

  WNN : 0ℚ ≤ W
  WNN =
    ℚP.<⇒≤
      (Quotient.positiveReciprocalPositive
        (R449.two * nu) (R449.twicePositive Floor.nuPositive))

  buildCanonicalOutputPositivity :
    (selected : List Z3.FourierMode) →
    ((mode : Z3.FourierMode) → mode Cube.∈ selected → mode Cube.∈ outputs) →
    Global.OutputFibresPositiveOn cutoff selected
  buildCanonicalOutputPositivity [] included = Global.positiveOutputsNil
  buildCanonicalOutputPositivity (output ∷ rest) included =
    Global.positiveOutputsCons
      (Rate.physicalOutputFibrePairRatesPositive
        cutoff output
        (R404.nonzeroCutoffMemberNonzero
          (included output (Cube.here refl))))
      (buildCanonicalOutputPositivity rest
        (λ mode member → included mode (Cube.there member)))

  canonicalOutputPositivity : Global.OutputFibresPositiveOn cutoff outputs
  canonicalOutputPositivity =
    buildCanonicalOutputPositivity outputs (λ mode member → member)

  globalPairs = Global.globalPairs cutoff outputs canonicalOutputPositivity

  globalFlux : ℚ
  globalFlux = R385.sumWeightedFlux globalPairs

  outputFlux :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    Local.PairRatePositiveOn (Output.physicalOutputFiber cutoff output) → ℚ
  outputFlux output outputNonzero positive =
    R385.sumWeightedFlux (Global.O.outputPairs cutoff output positive)

  outputNegativeFluxBelowCeilingMass :
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (positive : Local.PairRatePositiveOn
      (Output.physicalOutputFiber cutoff output)) →
    0ℚ - outputFlux output outputNonzero positive
    ≤ W * R456.sumDoubleMixedMass S velocity
        (Output.physicalOutputFiber cutoff output)
  outputNegativeFluxBelowCeilingMass output outputNonzero positive =
    let
      module O = R448.PhysicalOffDiagonalWeld
        physicalSystem S L H Pdata viscosityPositive cutoff output outputNonzero
      module D = R451.PhysicalDiagonalWeld
        physicalSystem S viscosityPositive unitGap cutoff output outputNonzero
      module E = R457.PhysicalDiagonalEndpoint
        physicalSystem S L H viscosityPositive unitGap radiusCalibration
        cutoff output outputNonzero

      fibre = Output.physicalOutputFiber cutoff output

      fluxToPhysical :
        outputFlux output outputNonzero positive ≡ O.physicalOffDiagonal fibre
      fluxToPhysical = O.allR290WeightedFluxExact fibre positive

      completionToPhysical :
        O.Completion.offDiagonal ≡ O.physicalOffDiagonal fibre
      completionToPhysical =
        O.builtOffDiagonalExact fibre
          (O.Rate.allElementsHaveOutput cutoff output)

      fluxToCompletion :
        outputFlux output outputNonzero positive ≡ O.Completion.offDiagonal
      fluxToCompletion = trans fluxToPhysical (sym completionToPhysical)

      negFluxBelowDiagonal :
        0ℚ - outputFlux output outputNonzero positive
        ≤ O.Completion.diagonal
      negFluxBelowDiagonal =
        subst
          (λ selected → 0ℚ - selected ≤ O.Completion.diagonal)
          fluxToCompletion
          O.Completion.negativeOffDiagonalPaidByDiagonal

      diagonalBelowMass :
        O.Completion.diagonal ≤ W * D.massSum
      diagonalBelowMass = D.r447DiagonalBelowCeilingMass

      massMeaning :
        D.massSum ≡ R456.sumDoubleMixedMass S velocity fibre
      massMeaning = E.massSumIsPhysicalMass

      paid :
        O.Completion.diagonal
        ≤ W * R456.sumDoubleMixedMass S velocity fibre
      paid = subst
        (λ selected → O.Completion.diagonal ≤ W * selected)
        massMeaning diagonalBelowMass
    in
    ℚP.≤-trans negFluxBelowDiagonal paid

  outputListNegativeFluxBelowMass :
    (selected : List Z3.FourierMode) →
    (positive : Global.OutputFibresPositiveOn cutoff selected) →
    ((output : Z3.FourierMode) → output Cube.∈ selected → Z3.NonZeroMode output) →
    0ℚ - R385.sumWeightedFlux (Global.globalPairs cutoff selected positive)
    ≤ W * R462.outputMassSum S velocity cutoff selected
  outputListNegativeFluxBelowMass [] Global.positiveOutputsNil allNonzero =
    subst
      (0ℚ ≤_)
      (solve (W ∷ []))
      ℚP.≤-refl
  outputListNegativeFluxBelowMass (output ∷ rest)
      (Global.positiveOutputsCons headPositive tailPositive) allNonzero =
    let
      headPairs = Global.O.outputPairs cutoff output headPositive
      tailPairs = Global.globalPairs cutoff rest tailPositive
      headFlux = R385.sumWeightedFlux headPairs
      tailFlux = R385.sumWeightedFlux tailPairs
      headMass = R456.sumDoubleMixedMass S velocity
        (Output.physicalOutputFiber cutoff output)
      tailMass = R462.outputMassSum S velocity cutoff rest

      headPaid = outputNegativeFluxBelowCeilingMass
        output (allNonzero output (Cube.here refl)) headPositive
      tailPaid = outputListNegativeFluxBelowMass rest tailPositive
        (λ selected member → allNonzero selected (Cube.there member))
      added = ℚP.+-mono-≤ headPaid tailPaid

      fluxAppend = sumWeightedFluxAppend headPairs tailPairs
      lhsMeaning :
        0ℚ - R385.sumWeightedFlux (headPairs ++ tailPairs)
        ≡ (0ℚ - headFlux) + (0ℚ - tailFlux)
      lhsMeaning = trans
        (congLocal (0ℚ -_) fluxAppend)
        (solve (headFlux ∷ tailFlux ∷ []))

      rhsMeaning :
        W * headMass + W * tailMass ≡ W * (headMass + tailMass)
      rhsMeaning = solve (W ∷ headMass ∷ tailMass ∷ [])
    in
    subst
      (λ lower → lower ≤ W * (headMass + tailMass))
      (sym lhsMeaning)
      (subst
        ((0ℚ - headFlux) + (0ℚ - tailFlux) ≤_)
        rhsMeaning added)
    where
    congLocal : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ y |> f
    congLocal f refl = refl

  globalNegativeFluxBelowSelectedMass :
    0ℚ - globalFlux ≤ W * Mass.selectedMass
  globalNegativeFluxBelowSelectedMass =
    outputListNegativeFluxBelowMass outputs canonicalOutputPositivity
      (λ output member → R404.nonzeroCutoffMemberNonzero member)

  scaledSelectedMassBelowEnergySquare :
    W * Mass.selectedMass ≤ W * (R452.fortyEight * Mass.energySquare)
  scaledSelectedMassBelowEnergySquare =
    let instance WNNI : NonNegative W = nonNegative WNN
    in ℚP.*-monoˡ-≤-nonNeg W Mass.globalNonzeroOutputMassBelowEnergySquare

  globalNegativeFluxEnergySquareEndpoint :
    0ℚ - globalFlux ≤ W * (R452.fortyEight * Mass.energySquare)
  globalNegativeFluxEnergySquareEndpoint =
    ℚP.≤-trans globalNegativeFluxBelowSelectedMass
      scaledSelectedMassBelowEnergySquare

round463GlobalR398NegativeFluxEndpointPaid : Bool
round463GlobalR398NegativeFluxEndpointPaid = true

round463OutputCardinalityTaxIntroduced : Bool
round463OutputCardinalityTaxIntroduced = false

round463UsesSameR398GlobalPairList : Bool
round463UsesSameR398GlobalPairList = true

round463ContainsPostulate : Bool
round463ContainsPostulate = false

round463PackageAClosed : Bool
round463PackageAClosed = false

round463ClayPromotion : Bool
round463ClayPromotion = false

round463OutputCardinalityTaxIntroducedIsFalse :
  round463OutputCardinalityTaxIntroduced ≡ false
round463OutputCardinalityTaxIntroducedIsFalse = refl

round463ContainsPostulateIsFalse : round463ContainsPostulate ≡ false
round463ContainsPostulateIsFalse = refl
