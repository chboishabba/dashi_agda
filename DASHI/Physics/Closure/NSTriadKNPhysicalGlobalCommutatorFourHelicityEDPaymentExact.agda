module DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCommutatorFourHelicityEDPaymentExact where

------------------------------------------------------------------------
-- GLOBAL FOUR-HELICITY PURE-COMMUTATOR MASS PAYMENT
--
-- For every retained resonant ordered pair p,q -> k and every helical signs
-- s,t, R574 gives
--
--   ||M^{s,t}_{p,q}||^2 <= 9 |k|^2 E_p^s E_q^t.
--
-- The four helical input masses collapse exactly by R475, while R218 gives
--
--   |k|^2 <= 2 (|p|^2 + |q|^2).
--
-- Hence, writing D_p = |p|^2 E_p,
--
--   sum_{s,t} ||M^{s,t}_{p,q}||^2
--     <= 18 (D_p E_q + E_p D_q).
--
-- R109 then sums any Boolean-selected ordered-pair family without cardinality
-- loss:
--
--   sum (D_p E_q + E_p D_q) <= 2 E D.
--
-- Therefore the complete literal nonzero-output selected family obeys
--
--   sum commutator-component-mass <= 36 E D.
--
-- IMPORTANT: this owner uses only the retained-mode transversality actually
-- carried by PhysicalFiniteComplex3GalerkinSystem.  It does NOT assume a
-- stronger global divergence-free velocity law.  It also does not identify
-- this positive mass by fiat with R568's signed resolvent full-square or the
-- external Waleffe production scalar; those require explicit weighting/pairing
-- transports.
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
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact as Conv
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNWeightedHelicalGramOperatorSplitRound475Exact as R475
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
        (trans (sym decision) (Output.modeEqualComplete modeZero))
  }

nonzeroOutputSelector :
  Nat → Z3.FourierMode → Z3.FourierMode → Bool
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

  component :
    Helical.HelicitySign → Z3.FourierMode → C3.Complex3 F
  component sign mode =
    Helical.helicalProjector E I S sign mode (velocity mode)

  signedEigenvalue :
    Helical.HelicitySign → Z3.FourierMode → C3.Complex F
  signedEigenvalue Helical.plus mode =
    C3.realEmbed F (Helical.modeNorm S mode)
  signedEigenvalue Helical.minus mode =
    C3.realEmbed F (C3.negate F (Helical.modeNorm S mode))

  componentCurlEigen :
    (sign : Helical.HelicitySign) (mode : Z3.FourierMode) →
    Conv.curlFromWave (C3.modeVector E mode) (component sign mode)
    ≡ C3.complex3Scale
        (signedEigenvalue sign mode)
        (component sign mode)
  componentCurlEigen Helical.plus mode =
    Helical.helicalCurlEigenvaluePlus L mode (velocity mode)
  componentCurlEigen Helical.minus mode =
    Helical.helicalCurlEigenvalueMinus L mode (velocity mode)

  componentPairData :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.k tau) →
    (signP signQ : Helical.HelicitySign) →
    R106.ProjectedHelicalPairData E I
      (Physical.p tau) (Physical.q tau) (Physical.k tau)
  componentPairData tau outputNonzero signP signQ =
    R106.projected-helical-pair-data
      (Physical.resonance tau)
      outputNonzero
      (component signP (Physical.p tau))
      (component signQ (Physical.q tau))
      (signedEigenvalue signP (Physical.p tau))
      (signedEigenvalue signQ (Physical.q tau))
      (componentCurlEigen signP (Physical.p tau))
      (componentCurlEigen signQ (Physical.q tau))

  multiplierDifferenceVector :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.k tau) →
    Helical.HelicitySign → Helical.HelicitySign →
    C3.Complex3 F
  multiplierDifferenceVector tau outputNonzero signP signQ =
    R574.r106MultiplierDifferenceVector
      (componentPairData tau outputNonzero signP signQ)

  componentEnergy :
    Helical.HelicitySign → Z3.FourierMode → ℚ
  componentEnergy sign mode =
    L2.complex3NormSquared (component sign mode)

  modalEnergy : Z3.FourierMode → ℚ
  modalEnergy mode = L2.complex3NormSquared (velocity mode)

  modalDissipation : Z3.FourierMode → ℚ
  modalDissipation mode = C3.normSquared I mode * modalEnergy mode

  componentEnergySplit :
    (mode : Z3.FourierMode) →
    mode Cube.∈ modes →
    componentEnergy Helical.plus mode
      + componentEnergy Helical.minus mode
    ≡ modalEnergy mode
  componentEnergySplit mode member =
    sym
      (R475.l2NormHelicalSplit E I S L mode (velocity mode)
        (Field30.retainedVelocityTransverse physicalSystem mode member))

  componentBound :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    (signP signQ : Helical.HelicitySign) →
    L2.complex3NormSquared
      (multiplierDifferenceVector tau outputNonzero signP signQ)
    ≤ R178.nine * C3.normSquared I (Physical.k tau)
        * componentEnergy signP (Physical.p tau)
        * componentEnergy signQ (Physical.q tau)
  componentBound tau outputNonzero signP signQ =
    R574.r106MultiplierDifferenceLowOutputBound
      O
      (componentPairData tau outputNonzero signP signQ)
      (Helical.helicalProjectorDivergenceFree
        L signP (Physical.p tau) (velocity (Physical.p tau)))
      (Helical.helicalProjectorDivergenceFree
        L signQ (Physical.q tau) (velocity (Physical.q tau)))

  fourSignCommutatorMass :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.k tau) →
    ℚ
  fourSignCommutatorMass tau outputNonzero =
      L2.complex3NormSquared
        (multiplierDifferenceVector tau outputNonzero Helical.plus Helical.plus)
    + L2.complex3NormSquared
        (multiplierDifferenceVector tau outputNonzero Helical.plus Helical.minus)
    + L2.complex3NormSquared
        (multiplierDifferenceVector tau outputNonzero Helical.minus Helical.plus)
    + L2.complex3NormSquared
        (multiplierDifferenceVector tau outputNonzero Helical.minus Helical.minus)

  fourSignCommutatorMassBelowOutputEnergyProduct :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    (pMember : Physical.p tau Cube.∈ modes) →
    (qMember : Physical.q tau Cube.∈ modes) →
    fourSignCommutatorMass tau outputNonzero
    ≤ R178.nine * C3.normSquared I (Physical.k tau)
        * modalEnergy (Physical.p tau)
        * modalEnergy (Physical.q tau)
  fourSignCommutatorMassBelowOutputEnergyProduct
      tau outputNonzero pMember qMember =
    let
      p = Physical.p tau
      q = Physical.q tau
      k2 = C3.normSquared I (Physical.k tau)

      bPP = componentBound tau outputNonzero Helical.plus Helical.plus
      bPM = componentBound tau outputNonzero Helical.plus Helical.minus
      bMP = componentBound tau outputNonzero Helical.minus Helical.plus
      bMM = componentBound tau outputNonzero Helical.minus Helical.minus

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
        rewrite sym (componentEnergySplit p pMember)
              | sym (componentEnergySplit q qMember) =
        solve
          ( R178.nine ∷ k2
          ∷ componentEnergy Helical.plus p
          ∷ componentEnergy Helical.minus p
          ∷ componentEnergy Helical.plus q
          ∷ componentEnergy Helical.minus q
          ∷ [])
    in
    subst
      (fourSignCommutatorMass tau outputNonzero ≤_)
      endpoint
      summed

  fourSignCommutatorMassBelowEDKernel :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    (pMember : Physical.p tau Cube.∈ modes) →
    (qMember : Physical.q tau Cube.∈ modes) →
    fourSignCommutatorMass tau outputNonzero
    ≤ eighteen * R109.pairKernel
        (R219.physicalModalED E I velocity)
        (Physical.p tau) (Physical.q tau)
  fourSignCommutatorMassBelowEDKernel
      tau outputNonzero pMember qMember =
    let
      p = Physical.p tau
      q = Physical.q tau
      k = Physical.k tau
      ep = modalEnergy p
      eq = modalEnergy q
      p2 = C3.normSquared I p
      q2 = C3.normSquared I q
      k2 = C3.normSquared I k

      first =
        fourSignCommutatorMassBelowOutputEnergyProduct
          tau outputNonzero pMember qMember

      epEqNN : 0ℚ ≤ ep * eq
      epEqNN =
        R178.Rational.productNonnegative
          (Separation.complex3NormSquaredNonnegative (velocity p))
          (Separation.complex3NormSquaredNonnegative (velocity q))

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
      nineNN = Rational.productNonnegative R178.threeNN R178.threeNN

      scaledTriangle :
        R178.nine * (k2 * (ep * eq))
        ≤ R178.nine * (two * (p2 + q2) * (ep * eq))
      scaledTriangle =
        let instance nineNNI : NonNegative R178.nine
            nineNNI = nonNegative nineNN
        in ℚP.*-monoˡ-≤-nonNeg R178.nine triangleTimesEnergy

      endpoint :
        R178.nine * k2 * ep * eq
        ≤ eighteen * (p2 * ep * eq + ep * (q2 * eq))
      endpoint =
        subst
          (R178.nine * k2 * ep * eq ≤_)
          (solve (R178.nine ∷ two ∷ p2 ∷ q2 ∷ ep ∷ eq ∷ []))
          (subst
            (_≤ R178.nine * (two * (p2 + q2) * (ep * eq)))
            (solve (R178.nine ∷ k2 ∷ ep ∷ eq ∷ []))
            scaledTriangle)

      pairMeaning :
        R109.pairKernel (R219.physicalModalED E I velocity) p q
        ≡ p2 * ep * eq + ep * (q2 * eq)
      pairMeaning = solve (p2 ∷ q2 ∷ ep ∷ eq ∷ [])
    in
    ℚP.≤-trans first
      (subst
        (λ rhs → R178.nine * k2 * ep * eq ≤ eighteen * rhs)
        (sym pairMeaning)
        endpoint)

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
        outputNonzero = nonzeroFromModeEqualFalse (Z3.addMode p q) refl
        includeTail :
          (selected : Z3.FourierMode) →
          selected Cube.∈ rest → selected Cube.∈ modes
        includeTail selected member = include selected (Cube.there member)
      in
      fourSignCommutatorMass tau outputNonzero
        + massInner p pMember rest includeTail
  ... | _ | _ =
      massInner p pMember rest
        (λ selected member → include selected (Cube.there member))

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
        outputNonzero = nonzeroFromModeEqualFalse (Z3.addMode p q) refl
        qMember = include q (Cube.here refl)
        includeTail :
          (selected : Z3.FourierMode) →
          selected Cube.∈ rest → selected Cube.∈ modes
        includeTail selected member = include selected (Cube.there member)

        head =
          fourSignCommutatorMassBelowEDKernel
            tau outputNonzero pMember qMember
        tail =
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
        (ℚP.+-mono-≤ head tail)
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
          p (include p (Cube.here refl)) modes (λ q member → member)
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

      nineNN : 0ℚ ≤ R178.nine
      nineNN = Rational.productNonnegative R178.threeNN R178.threeNN
      twoNN : 0ℚ ≤ two
      twoNN = Rational.addNonnegative R178.oneNN R178.oneNN
      eighteenNN : 0ℚ ≤ eighteen
      eighteenNN = Rational.productNonnegative nineNN twoNN

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
        ( eighteen ∷ two
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
