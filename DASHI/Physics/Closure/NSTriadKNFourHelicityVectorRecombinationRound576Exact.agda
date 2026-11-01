module DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact where

------------------------------------------------------------------------
-- ROUND576 / FIXED FOUR-CHANNEL GRAM RECOMBINATION COSTS ONLY FOUR
--
-- R575 shows that the SUM of the four R574 component masses is bounded by
--
--   9 |k|^2 ||u_p||^2 ||u_q||^2
--
-- with no channel-count factor.  What it intentionally does not prove is a
-- bound for the norm of the vector sum M+++M+-+M-++M--, because its cross
-- Gram terms need not vanish.
--
-- The channel set, however, has fixed size four.  We reuse the exact four-point
-- Jensen/SOS identity already owned by the Yang--Mills lane.  In division-free
-- form it is simply
--
--   (a+b+c+d)^2 <= 4(a^2+b^2+c^2+d^2),
--
-- because the difference is the sum of the six pairwise difference squares.
-- Applying this coordinatewise to C^3 gives
--
--   ||A+B+C+D||^2 <= 4(sum channel masses).
--
-- Combined with R575, every literal R571 four-sign inner cell therefore obeys
--
--   ||fourSignInner||^2 <= 36 |k|^2 ||u_p||^2 ||u_q||^2.
--
-- This closes the FIXED helicity recombination issue.  It still does not sum
-- over the variable convolution fibre p+q=k; that is now the genuine next
-- aggregation wall.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.YangMills.BalabanPath4AverageJensenExact as J4
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact as R571
import DASHI.Physics.Closure.NSTriadKNR106ComponentLowOutputBoundRound574Exact as R574
import DASHI.Physics.Closure.NSTriadKNFourHelicityComponentMassCollapseRound575Exact as R575
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

four : ℚ
four = J4.fourℚ

fourNN : 0ℚ ≤ four
fourNN = Rational.addNonnegative R178.threeNN R178.oneNN

fourScalarSumSquareBound :
  (a b c d : ℚ) →
  ((a + b) + (c + d)) * ((a + b) + (c + d))
  ≤ four * (a * a + b * b + c * c + d * d)
fourScalarSumSquareBound a b c d =
  let
    remainder = J4.sixPairDifferenceSquares a b c d
    remainderNN = J4.sixPairDifferenceSquaresNonnegative a b c d
    identity :
      four * (a * a + b * b + c * c + d * d)
      ≡ ((a + b) + (c + d)) * ((a + b) + (c + d)) + remainder
    identity = solve (a ∷ b ∷ c ∷ d ∷ [])
    baseBelow :
      ((a + b) + (c + d)) * ((a + b) + (c + d))
      ≤ ((a + b) + (c + d)) * ((a + b) + (c + d)) + remainder
    baseBelow =
      ℚP.+-mono-≤ ℚP.≤-refl remainderNN
  in
  subst
    (λ upper →
      ((a + b) + (c + d)) * ((a + b) + (c + d)) ≤ upper)
    identity baseBelow

fourComplexSumModulusBound :
  (a b c d : C3.Complex F) →
  L2.complexModulusSquared
    (C3.complexAdd (C3.complexAdd a b) (C3.complexAdd c d))
  ≤ four *
      (L2.complexModulusSquared a
       + L2.complexModulusSquared b
       + L2.complexModulusSquared c
       + L2.complexModulusSquared d)
fourComplexSumModulusBound
    (C3.complex ar ai) (C3.complex br bi)
    (C3.complex cr ci) (C3.complex dr di) =
  let
    realBound = fourScalarSumSquareBound ar br cr dr
    imagBound = fourScalarSumSquareBound ai bi ci di
    added = ℚP.+-mono-≤ realBound imagBound
    rearrange :
      four * (ar * ar + br * br + cr * cr + dr * dr)
        + four * (ai * ai + bi * bi + ci * ci + di * di)
      ≡ four *
          (L2.complexModulusSquared (C3.complex ar ai)
           + L2.complexModulusSquared (C3.complex br bi)
           + L2.complexModulusSquared (C3.complex cr ci)
           + L2.complexModulusSquared (C3.complex dr di))
    rearrange = solve
      (ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci ∷ dr ∷ di ∷ [])
  in
  subst
    (λ upper →
      L2.complexModulusSquared
        (C3.complexAdd
          (C3.complexAdd (C3.complex ar ai) (C3.complex br bi))
          (C3.complexAdd (C3.complex cr ci) (C3.complex dr di)))
      ≤ upper)
    rearrange added

fourVectorTotal :
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F
fourVectorTotal a b c d =
  C3.complex3Add (C3.complex3Add a b) (C3.complex3Add c d)

fourVectorSumNormSquaredBound :
  (a b c d : C3.Complex3 F) →
  L2.complex3NormSquared (fourVectorTotal a b c d)
  ≤ four *
      (L2.complex3NormSquared a
       + L2.complex3NormSquared b
       + L2.complex3NormSquared c
       + L2.complex3NormSquared d)
fourVectorSumNormSquaredBound
    (C3.complex3 ax ay az) (C3.complex3 bx by bz)
    (C3.complex3 cx cy cz) (C3.complex3 dx dy dz) =
  let
    xBound = fourComplexSumModulusBound ax bx cx dx
    yBound = fourComplexSumModulusBound ay by cy dy
    zBound = fourComplexSumModulusBound az bz cz dz
    added = ℚP.+-mono-≤ (ℚP.+-mono-≤ xBound yBound) zBound
    rearrange :
      four *
        (L2.complexModulusSquared ax + L2.complexModulusSquared bx
          + L2.complexModulusSquared cx + L2.complexModulusSquared dx)
      + four *
        (L2.complexModulusSquared ay + L2.complexModulusSquared by
          + L2.complexModulusSquared cy + L2.complexModulusSquared dy)
      + four *
        (L2.complexModulusSquared az + L2.complexModulusSquared bz
          + L2.complexModulusSquared cz + L2.complexModulusSquared dz)
      ≡ four *
        (L2.complex3NormSquared (C3.complex3 ax ay az)
         + L2.complex3NormSquared (C3.complex3 bx by bz)
         + L2.complex3NormSquared (C3.complex3 cx cy cz)
         + L2.complex3NormSquared (C3.complex3 dx dy dz))
    rearrange = solve
      ( L2.complexModulusSquared ax ∷ L2.complexModulusSquared ay
      ∷ L2.complexModulusSquared az ∷ L2.complexModulusSquared bx
      ∷ L2.complexModulusSquared by ∷ L2.complexModulusSquared bz
      ∷ L2.complexModulusSquared cx ∷ L2.complexModulusSquared cy
      ∷ L2.complexModulusSquared cz ∷ L2.complexModulusSquared dx
      ∷ L2.complexModulusSquared dy ∷ L2.complexModulusSquared dz ∷ [])
  in
  subst
    (λ upper →
      L2.complex3NormSquared
        (fourVectorTotal
          (C3.complex3 ax ay az) (C3.complex3 bx by bz)
          (C3.complex3 cx cy cz) (C3.complex3 dx dy dz))
      ≤ upper)
    rearrange added

thirtySix : ℚ
thirtySix = four * R178.nine

module PhysicalRecombination
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module C = R571.Componentwise system S L velocityTransverse
  module Collapse = R575.PhysicalCollapse E I O system S L velocityTransverse

  fourSignInner : Physical.PhysicalTriadIncidence → C3.Complex3 F
  fourSignInner tau =
    fourVectorTotal
      (C.multiplierDifferenceVector tau Helical.plus Helical.plus)
      (C.multiplierDifferenceVector tau Helical.plus Helical.minus)
      (C.multiplierDifferenceVector tau Helical.minus Helical.plus)
      (C.multiplierDifferenceVector tau Helical.minus Helical.minus)

  fourSignInnerLowOutputBound :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    L2.complex3NormSquared (fourSignInner tau)
    ≤ thirtySix * C3.normSquared I (Physical.k tau)
        * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
        * L2.complex3NormSquared (Audit.velocity system (Physical.q tau))
  fourSignInnerLowOutputBound tau outputNonzero =
    let
      channelBound = fourVectorSumNormSquaredBound
        (C.multiplierDifferenceVector tau Helical.plus Helical.plus)
        (C.multiplierDifferenceVector tau Helical.plus Helical.minus)
        (C.multiplierDifferenceVector tau Helical.minus Helical.plus)
        (C.multiplierDifferenceVector tau Helical.minus Helical.minus)

      summed = Collapse.sumFourComponentCellBounds tau outputNonzero

      scaled :
        four *
          ( L2.complex3NormSquared
              (C.multiplierDifferenceVector tau Helical.plus Helical.plus)
          + L2.complex3NormSquared
              (C.multiplierDifferenceVector tau Helical.plus Helical.minus)
          + L2.complex3NormSquared
              (C.multiplierDifferenceVector tau Helical.minus Helical.plus)
          + L2.complex3NormSquared
              (C.multiplierDifferenceVector tau Helical.minus Helical.minus))
        ≤ four *
          (R178.nine * C3.normSquared I (Physical.k tau)
            * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
            * L2.complex3NormSquared (Audit.velocity system (Physical.q tau)))
      scaled =
        let instance fourNNI = nonNegative fourNN
        in ℚP.*-monoˡ-≤-nonNeg four summed

      normalized :
        four *
          (R178.nine * C3.normSquared I (Physical.k tau)
            * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
            * L2.complex3NormSquared (Audit.velocity system (Physical.q tau)))
        ≡ thirtySix * C3.normSquared I (Physical.k tau)
            * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
            * L2.complex3NormSquared (Audit.velocity system (Physical.q tau))
      normalized = solve
        ( C3.normSquared I (Physical.k tau)
        ∷ L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
        ∷ L2.complex3NormSquared (Audit.velocity system (Physical.q tau)) ∷ [])
    in
    ℚP.≤-trans channelBound
      (subst
        (λ upper →
          four *
            ( L2.complex3NormSquared
                (C.multiplierDifferenceVector tau Helical.plus Helical.plus)
            + L2.complex3NormSquared
                (C.multiplierDifferenceVector tau Helical.plus Helical.minus)
            + L2.complex3NormSquared
                (C.multiplierDifferenceVector tau Helical.minus Helical.plus)
            + L2.complex3NormSquared
                (C.multiplierDifferenceVector tau Helical.minus Helical.minus))
          ≤ upper)
        normalized scaled)

------------------------------------------------------------------------
-- Status / next irreducible cut.
------------------------------------------------------------------------

round576FixedFourChannelGramRecombinationClosed : Bool
round576FixedFourChannelGramRecombinationClosed = true

round576FourSignInnerCellLowOutputBoundClosed : Bool
round576FourSignInnerCellLowOutputBoundClosed = true

round576FourSignInnerCellHighLegFrequencyAppears : Bool
round576FourSignInnerCellHighLegFrequencyAppears = false

round576FourSignInnerCellVariableCardinalityFactorAppears : Bool
round576FourSignInnerCellVariableCardinalityFactorAppears = false

round576VariableInnerFibreAggregationClosed : Bool
round576VariableInnerFibreAggregationClosed = false

round576OuterSpectatorWeightedSpacetimeBoundClosed : Bool
round576OuterSpectatorWeightedSpacetimeBoundClosed = false

round576CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round576CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round576ClayPromotion : Bool
round576ClayPromotion = false

round576FixedFourChannelGramRecombinationClosedIsTrue :
  round576FixedFourChannelGramRecombinationClosed ≡ true
round576FixedFourChannelGramRecombinationClosedIsTrue = refl

round576VariableInnerFibreAggregationClosedIsFalse :
  round576VariableInnerFibreAggregationClosed ≡ false
round576VariableInnerFibreAggregationClosedIsFalse = refl

round576ClayPromotionIsFalse : round576ClayPromotion ≡ false
round576ClayPromotionIsFalse = refl
