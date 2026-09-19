module DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCommutatorFourHelicityEDPaymentExact where

------------------------------------------------------------------------
-- GLOBAL FOUR-HELICITY PURE-COMMUTATOR MASS PAYMENT
--
-- R574 proves componentwise, for every helical sign pair,
--
--   ||M^{s,t}_{p,q}||^2 <= 9 |k|^2 E_p^s E_q^t.
--
-- Summing the four sign pairs and using exact helical Pythagoras gives
--
--   sum_{s,t} ||M^{s,t}_{p,q}||^2 <= 9 |k|^2 E_p E_q.
--
-- R218 gives the literal resonant square triangle
--
--   |k|^2 <= 2 (|p|^2 + |q|^2),
--
-- hence, with D_p = |p|^2 E_p,
--
--   sum_{s,t} ||M^{s,t}_{p,q}||^2
--     <= 18 (D_p E_q + E_p D_q).
--
-- Finally R109 sums ANY Boolean-selected ordered-pair family by
--
--   sum (D_p E_q + E_p D_q) <= 2 E D.
--
-- Therefore the complete literal nonzero-output selected family satisfies
--
--   sum commutator-component-mass <= 36 E D
--
-- with no pair count, output-fibre count, shell count, or Galerkin-cutoff
-- factor.  This is a positive mass theorem for the exact R571/R574 four-sign
-- multiplier-difference components.  It does not identify that mass by fiat
-- with the signed R568 resolvent full-square or with the R109 external quartic
-- production scalar; those remain separate same-object/weighting transports.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNWeightedHelicalGramOperatorSplitRound475Exact as R475
import DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact as R571
import DASHI.Physics.Closure.NSTriadKNR106ComponentLowOutputBoundRound574Exact as R574
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNPhysicalResonantEuclideanSquareTriangleRound218Exact as R218
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDAdapterRound219Exact as R219

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

eighteen : ℚ
eighteen = R178.nine * two

thirtySix : ℚ
thirtySix = eighteen * two

falseCannotEqualTrue : false ≡ true → ⊥
falseCannotEqualTrue ()

nonzeroFromModeEqualFalse :
  (mode : Z3.FourierMode) →
  Output.modeEqual mode Z3.zeroMode ≡ false →
  Z3.NonZeroMode mode
nonzeroFromModeEqualFalse mode decision = record
  { Z3.notZero = λ modeZero →
      falseCannotEqualTrue
        (trans
          (sym decision)
          (Output.modeEqualComplete modeZero))
  }

nonzeroOutputSelector :
  (cutoff : Nat) →
  Z3.FourierMode → Z3.FourierMode → Bool
nonzeroOutputSelector cutoff p q
  with Physical.modeWithinCutoff cutoff (Z3.addMode p q)
     | Output.modeEqual (Z3.addMode p q) Z3.zeroMode
... | true | false = true
... | _ | _ = false

module GlobalCommutatorPayment
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws
      F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S)
    (O : Leray.RationalInverseNormOrder
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system
  modes = Audit.modes system
  velocity = Audit.velocity system

  velocityTransverse :
    (mode : Z3.FourierMode) →
    mode Cube.∈ modes →
    Helical.Transverse E mode (velocity mode)
  velocityTransverse mode member =
    Field30.retainedVelocityTransverse physicalSystem mode member

  module C = R571.Componentwise
    system S L
    (λ mode →
      -- The componentwise algebra only consumes transversality on modes that
      -- occur in the selected physical pairs below.  The raw system itself
      -- carries a global divergence-free velocity law.
      Audit.divergenceFree system mode)

  module Low = R574.PhysicalComponents
    E I O system S L (Audit.divergenceFree system)

  componentEnergy :
    Helical.HelicitySign → Z3.FourierMode → ℚ
  componentEnergy sign mode =
    L2.complex3NormSquared (C.component sign mode)

  modalEnergy : Z3.FourierMode → ℚ
  modalEnergy mode = L2.complex3NormSquared (velocity mode)

  modalDissipation : Z3.FourierMode → ℚ
  modalDissipation mode = C3.normSquared I mode * modalEnergy mode

  componentEnergySplit :
    (mode : Z3.FourierMode) →
    componentEnergy Helical.plus mode
      + componentEnergy Helical.minus mode
    ≡ modalEnergy mode
  componentEnergySplit mode =
    sym
      (R475.l2NormHelicalSplit E I S L mode (velocity mode)
        (Audit.divergenceFree system mode))

  fourSignCommutatorMass :
    (tau : Physical.PhysicalTriadIncidence) →
    ℚ
  fourSignCommutatorMass tau =
      L2.complex3NormSquared
        (C.multiplierDifferenceVector tau Helical.plus Helical.plus)
    + L2.complex3NormSquared
        (C.multiplierDifferenceVector tau Helical.plus Helical.minus)
    + L2.complex3NormSquared
        (C.multiplierDifferenceVector tau Helical.minus Helical.plus)
    + L2.complex3NormSquared
        (C.multiplierDifferenceVector tau Helical.minus Helical.minus)

  fourSignCommutatorMassBelowOutputEnergyProduct :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    fourSignCommutatorMass tau
    ≤ R178.nine * C3.normSquared I (Physical.k tau)
        * modalEnergy (Physical.p tau)
        * modalEnergy (Physical.q tau)
  fourSignCommutatorMassBelowOutputEnergyProduct tau outputNonzero =
    let
      p = Physical.p tau
      q = Physical.q tau
      k2 = C3.normSquared I (Physical.k tau)

      bPP = Low.componentLowOutputBound
        tau outputNonzero Helical.plus Helical.plus
      bPM = Low.componentLowOutputBound
        tau outputNonzero Helical.plus Helical.minus
      bMP = Low.componentLowOutputBound
        tau outputNonzero Helical.minus Helical.plus
      bMM = Low.componentLowOutputBound
        tau outputNonzero Helical.minus Helical.minus

      summed =
        ℚP.+-mono-≤
          (ℚP.+-mono-≤ (ℚP.+-mono-≤ bPP bPM) bMP)
          bMM

      endpoint :
        (R178.nine * k2
          * componentEnergy Helical.plus p
          * componentEnergy Helical.plus q)
        +
        (R178.nine * k2
          * componentEnergy Helical.plus p
          * componentEnergy Helical.minus q)
        +
        (R178.nine * k2
          * componentEnergy Helical.minus p
          * componentEnergy Helical.plus q)
        +
        (R178.nine * k2
          * componentEnergy Helical.minus p
          * componentEnergy Helical.minus q)
        ≡
        R178.nine * k2 * modalEnergy p * modalEnergy q
      endpoint
        rewrite sym (componentEnergySplit p)
              | sym (componentEnergySplit q) =
        solve
          ( R178.nine ∷ k2
          ∷ componentEnergy Helical.plus p
          ∷ componentEnergy Helical.minus p
          ∷ componentEnergy Helical.plus q
          ∷ componentEnergy Helical.minus q
          ∷ [])
    in
    subst
      (fourSignCommutatorMass tau ≤_)
      endpoint
      summed

  fourSignCommutatorMassBelowEDKernel :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    fourSignCommutatorMass tau
    ≤ eighteen
        * (modalDissipation (Physical.p tau) * modalEnergy (Physical.q tau)
          + modalEnergy (Physical.p tau) * modalDissipation (Physical.q tau))
  fourSignCommutatorMassBelowEDKernel tau outputNonzero =
    let
      p = Physical.p tau
      q = Physical.q tau
      k = Physical.k tau
      ep = modalEnergy p
      eq = modalEnergy q
      p2 = C3.normSquared I p
      q2 = C3.normSquared I q
      k2 = C3.normSquared I k

      componentBound =
        fourSignCommutatorMassBelowOutputEnergyProduct tau outputNonzero

      epNN = Rational.complex3NormSquaredNonnegative (velocity p)
      eqNN = Rational.complex3NormSquaredNonnegative (velocity q)
      epEqNN : 0ℚ ≤ ep * eq
      epEqNN =
        let
          instance epNNI : NonNegative ep
          epNNI = nonNegative epNN
          eqNNI : NonNegative eq
          eqNNI = nonNegative eqNN
        in ℚP.nonNegative⁻¹ (ep * eq)

      triangle =
        R218.resonantEuclideanSquareTriangle E I (Physical.resonance tau)

      triangleTimesEnergy :
        k2 * (ep * eq)
        ≤ two * (p2 + q2) * (ep * eq)
      triangleTimesEnergy =
        let instance epEqNNI : NonNegative (ep * eq)
            epEqNNI = nonNegative epEqNN
        in ℚP.*-monoʳ-≤-nonNeg (ep * eq) triangle

      nineNN : 0ℚ ≤ R178.nine
      nineNN = Rational.squareNonnegative R178.three

      scaledTriangle :
        R178.nine * (k2 * (ep * eq))
        ≤ R178.nine * (two * (p2 + q2) * (ep * eq))
      scaledTriangle =
        let instance nineNNI : NonNegative R178.nine
            nineNNI = nonNegative nineNN
        in ℚP.*-monoˡ-≤-nonNeg R178.nine triangleTimesEnergy

      leftMeaning :
        R178.nine * k2 * ep * eq
        ≡ R178.nine * (k2 * (ep * eq))
      leftMeaning = solve (R178.nine ∷ k2 ∷ ep ∷ eq ∷ [])

      rightMeaning :
        R178.nine * (two * (p2 + q2) * (ep * eq))
        ≡ eighteen * (p2 * ep * eq + ep * (q2 * eq))
      rightMeaning =
        solve (R178.nine ∷ two ∷ p2 ∷ q2 ∷ ep ∷ eq ∷ [])

      triangleEndpoint :
        R178.nine * k2 * ep * eq
        ≤ eighteen * (p2 * ep * eq + ep * (q2 * eq))
      triangleEndpoint =
        subst
          (λ left →
            left ≤ eighteen * (p2 * ep * eq + ep * (q2 * eq)))
          (sym leftMeaning)
          (subst
            (R178.nine * (k2 * (ep * eq)) ≤_)
            rightMeaning
            scaledTriangle)
    in
    ℚP.≤-trans componentBound triangleEndpoint

  modalED : R109.ModalEnergyDissipation Z3.FourierMode
  modalED = R219.physicalModalED E I velocity

  massInner :
    (p : Z3.FourierMode) →
    p Cube.∈ modes →
    (rights : List Z3.FourierMode) →
    ((q : Z3.FourierMode) → q Cube.∈ rights → q Cube.∈ modes) →
    ℚ
  massInner p pMember [] include = 0ℚ
  massInner p pMember (q ∷ rest) include
      with Physical.modeWithinCutoff cutoff (Z3.addMode p q)
         | Output.modeEqual (Z3.addMode p q) Z3.zeroMode
  ... | true | false =
      let
        tau = Physical.pairTriad (Cube.pair p q)
        outputNonzero =
          nonzeroFromModeEqualFalse (Z3.addMode p q) refl
        includeTail :
          (selected : Z3.FourierMode) →
          selected Cube.∈ rest →
          selected Cube.∈ modes
        includeTail selected member =
          include selected (Cube.there member)
      in
      fourSignCommutatorMass tau
        + massInner p pMember rest includeTail
  ... | _ | _ =
      let
        includeTail :
          (selected : Z3.FourierMode) →
          selected Cube.∈ rest →
          selected Cube.∈ modes
        includeTail selected member =
          include selected (Cube.there member)
      in
      massInner p pMember rest includeTail

  massInnerBelowSelectedED :
    (p : Z3.FourierMode) →
    (pMember : p Cube.∈ modes) →
    (rights : List Z3.FourierMode) →
    (include :
      (q : Z3.FourierMode) → q Cube.∈ rights → q Cube.∈ modes) →
    massInner p pMember rights include
    ≤ eighteen * R109.selectedInner modalED
        (nonzeroOutputSelector cutoff) p rights
  massInnerBelowSelectedED p pMember [] include
    rewrite ℚP.*-zeroʳ eighteen = ℚP.≤-refl
  massInnerBelowSelectedED p pMember (q ∷ rest) include
      with Physical.modeWithinCutoff cutoff (Z3.addMode p q)
         | Output.modeEqual (Z3.addMode p q) Z3.zeroMode
  ... | true | false =
      let
        tau = Physical.pairTriad (Cube.pair p q)
        outputNonzero =
          nonzeroFromModeEqualFalse (Z3.addMode p q) refl
        includeTail :
          (selected : Z3.FourierMode) →
          selected Cube.∈ rest →
          selected Cube.∈ modes
        includeTail selected member =
          include selected (Cube.there member)

        headBound =
          fourSignCommutatorMassBelowEDKernel tau outputNonzero

        tailBound =
          massInnerBelowSelectedED p pMember rest includeTail

        endpoint :
          eighteen * R109.pairKernel modalED p q
            + eighteen * R109.selectedInner modalED
                (nonzeroOutputSelector cutoff) p rest
          ≡ eighteen *
              (R109.pairKernel modalED p q
                + R109.selectedInner modalED
                    (nonzeroOutputSelector cutoff) p rest)
        endpoint = solve
          ( eighteen
          ∷ R109.pairKernel modalED p q
          ∷ R109.selectedInner modalED
              (nonzeroOutputSelector cutoff) p rest
          ∷ [])
      in
      subst
        (massInner p pMember (q ∷ rest) include ≤_)
        endpoint
        (ℚP.+-mono-≤ headBound tailBound)
  ... | _ | _ =
      massInnerBelowSelectedED p pMember rest
        (λ selected member → include selected (Cube.there member))

  massSum :
    (lefts : List Z3.FourierMode) →
    ((p : Z3.FourierMode) → p Cube.∈ lefts → p Cube.∈ modes) →
    ℚ
  massSum [] include = 0ℚ
  massSum (p ∷ rest) include =
    massInner p
      (include p (Cube.here refl))
      modes
      (λ q member → member)
    +
    massSum rest
      (λ selected member → include selected (Cube.there member))

  massSumBelowSelectedED :
    (lefts : List Z3.FourierMode) →
    (include :
      (p : Z3.FourierMode) → p Cube.∈ lefts → p Cube.∈ modes) →
    massSum lefts include
    ≤ eighteen * R109.selectedOrderedPairSum modalED
        (nonzeroOutputSelector cutoff) lefts modes
  massSumBelowSelectedED [] include
    rewrite ℚP.*-zeroʳ eighteen = ℚP.≤-refl
  massSumBelowSelectedED (p ∷ rest) include =
    let
      head =
        massInnerBelowSelectedED
          p
          (include p (Cube.here refl))
          modes
          (λ q member → member)
      tail =
        massSumBelowSelectedED
          rest
          (λ selected member → include selected (Cube.there member))
      endpoint :
        eighteen * R109.selectedInner modalED
            (nonzeroOutputSelector cutoff) p modes
          + eighteen * R109.selectedOrderedPairSum modalED
              (nonzeroOutputSelector cutoff) rest modes
        ≡
        eighteen * R109.selectedOrderedPairSum modalED
          (nonzeroOutputSelector cutoff) (p ∷ rest) modes
      endpoint = solve
        ( eighteen
        ∷ R109.selectedInner modalED
            (nonzeroOutputSelector cutoff) p modes
        ∷ R109.selectedOrderedPairSum modalED
            (nonzeroOutputSelector cutoff) rest modes
        ∷ [])
    in
    subst
      (massSum (p ∷ rest) include ≤_)
      endpoint
      (ℚP.+-mono-≤ head tail)

  globalCommutatorComponentMass : ℚ
  globalCommutatorComponentMass =
    massSum modes (λ mode member → member)

  globalCommutatorComponentMassBelowThirtySixED :
    globalCommutatorComponentMass
    ≤ thirtySix
        * (R109.sumEnergy modalED modes * R109.sumDissipation modalED modes)
  globalCommutatorComponentMassBelowThirtySixED =
    let
      first =
        massSumBelowSelectedED modes (λ mode member → member)
      second =
        R109.selectedPairEnergyDissipationProductBound
          modalED (nonzeroOutputSelector cutoff) modes

      eighteenNN : 0ℚ ≤ eighteen
      eighteenNN =
        let
          nineNN = Rational.squareNonnegative R178.three
          twoNN = Rational.addNonnegative
            (Rational.squareNonnegative 1ℚ)
            (Rational.squareNonnegative 1ℚ)
          instance nineNNI : NonNegative R178.nine
          nineNNI = nonNegative nineNN
          twoNNI : NonNegative two
          twoNNI = nonNegative twoNN
        in ℚP.nonNegative⁻¹ eighteen

      scaledSecond :
        eighteen * R109.selectedOrderedPairSum modalED
            (nonzeroOutputSelector cutoff) modes modes
        ≤ eighteen *
            ((R109.sumEnergy modalED modes * R109.sumDissipation modalED modes)
              + (R109.sumEnergy modalED modes * R109.sumDissipation modalED modes))
      scaledSecond =
        let instance eighteenNNI : NonNegative eighteen
            eighteenNNI = nonNegative eighteenNN
        in ℚP.*-monoˡ-≤-nonNeg eighteen second

      endpoint :
        eighteen *
          ((R109.sumEnergy modalED modes * R109.sumDissipation modalED modes)
            + (R109.sumEnergy modalED modes * R109.sumDissipation modalED modes))
        ≡ thirtySix *
          (R109.sumEnergy modalED modes * R109.sumDissipation modalED modes)
      endpoint = solve
        ( eighteen
        ∷ two
        ∷ R109.sumEnergy modalED modes
        ∷ R109.sumDissipation modalED modes
        ∷ [])
    in
    ℚP.≤-trans first
      (subst
        (eighteen * R109.selectedOrderedPairSum modalED
          (nonzeroOutputSelector cutoff) modes modes ≤_)
        endpoint
        scaledSecond)
