module DASHI.Physics.Closure.NSTriadKNPhysicalGlobalSelfFourHelicityEDPaymentExact where

------------------------------------------------------------------------
-- GLOBAL PHYSICAL SELF-PHASE PAYMENT
--
-- For the literal finite Galerkin system, sum the complete four-helicity
-- self-phase contribution over retained ordered input modes p,q whenever the
-- resonant output k=p+q lies in the cutoff and is nonzero.
--
-- The local four-sign theorem gives
--
--   N_self(p,q) <= D_p E_q + E_p D_q.
--
-- R109 then pays the complete Boolean-selected ordered-pair family by
--
--   2 (sum E) (sum D)
--
-- with no pair-count, triad-count, shell-count or cutoff factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNMHDRadiusReciprocalToNormalizedDirectionRound464Exact as R464
import DASHI.Physics.Closure.NSTriadKNPhysicalHHAndNestedRadiusCompilerRound468Exact as R468
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDAdapterRound219Exact as R219
import DASHI.Physics.Closure.NSTriadKNPhysicalSelfFourHelicityEDPaymentExact as Local

F : C3.RealField _
F = Rational.rationalRealField

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

module GlobalSelfPayment
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws
      F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S)
    (O : Leray.RationalInverseNormOrder
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem)
    (radiusCalibration :
      R464.PhysicalSquareAndMHDCalibration
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem)
        S)
    (orientation : R468.PhysicalRadiusOrientation S) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system
  modes = Audit.modes system
  velocity = Audit.velocity system

  module H = Local.FourHelicityED
    physicalSystem S L O unitGap radiusCalibration orientation

  modalED : R109.ModalEnergyDissipation Z3.FourierMode
  modalED = R219.physicalModalED E I velocity

  selfInner :
    (p : Z3.FourierMode) →
    p Cube.∈ modes →
    (rights : List Z3.FourierMode) →
    ((q : Z3.FourierMode) → q Cube.∈ rights → q Cube.∈ modes) →
    ℚ
  selfInner p pMember [] include = 0ℚ
  selfInner p pMember (q ∷ rest) include
      with Physical.modeWithinCutoff cutoff (Z3.addMode p q)
         | Output.modeEqual (Z3.addMode p q) Z3.zeroMode
  ... | true | false =
      let
        tau = Physical.pairTriad (Cube.pair p q)
        outputNonzero =
          nonzeroFromModeEqualFalse
            (Z3.addMode p q) refl
        qMember = include q (Cube.here refl)
        includeTail :
          (selected : Z3.FourierMode) →
          selected Cube.∈ rest →
          selected Cube.∈ modes
        includeTail selected member =
          include selected (Cube.there member)
      in
      H.fourSignSelfPhase tau outputNonzero
        + selfInner p pMember rest includeTail
  ... | _ | _ =
      let
        includeTail :
          (selected : Z3.FourierMode) →
          selected Cube.∈ rest →
          selected Cube.∈ modes
        includeTail selected member =
          include selected (Cube.there member)
      in
      selfInner p pMember rest includeTail

  selfInnerBelowSelectedKernel :
    (p : Z3.FourierMode) →
    (pMember : p Cube.∈ modes) →
    (rights : List Z3.FourierMode) →
    (include :
      (q : Z3.FourierMode) → q Cube.∈ rights → q Cube.∈ modes) →
    selfInner p pMember rights include
    ≤ R109.selectedInner modalED
        (nonzeroOutputSelector cutoff) p rights
  selfInnerBelowSelectedKernel p pMember [] include = ℚP.≤-refl
  selfInnerBelowSelectedKernel p pMember (q ∷ rest) include
      with Physical.modeWithinCutoff cutoff (Z3.addMode p q)
         | Output.modeEqual (Z3.addMode p q) Z3.zeroMode
  ... | true | false =
      let
        tau = Physical.pairTriad (Cube.pair p q)
        outputNonzero =
          nonzeroFromModeEqualFalse
            (Z3.addMode p q) refl
        qMember = include q (Cube.here refl)
        includeTail :
          (selected : Z3.FourierMode) →
          selected Cube.∈ rest →
          selected Cube.∈ modes
        includeTail selected member =
          include selected (Cube.there member)

        headBound =
          H.fourSignSelfPhaseBelowModalED
            tau outputNonzero pMember qMember

        tailBound =
          selfInnerBelowSelectedKernel
            p pMember rest includeTail
      in
      ℚP.+-mono-≤ headBound tailBound
  ... | _ | _ =
      let
        includeTail :
          (selected : Z3.FourierMode) →
          selected Cube.∈ rest →
          selected Cube.∈ modes
        includeTail selected member =
          include selected (Cube.there member)
      in
      selfInnerBelowSelectedKernel p pMember rest includeTail

  selfSum :
    (lefts : List Z3.FourierMode) →
    ((p : Z3.FourierMode) → p Cube.∈ lefts → p Cube.∈ modes) →
    ℚ
  selfSum [] include = 0ℚ
  selfSum (p ∷ rest) include =
    selfInner p
      (include p (Cube.here refl))
      modes
      (λ q member → member)
    +
    selfSum rest
      (λ selected member → include selected (Cube.there member))

  selfSumBelowSelectedPairs :
    (lefts : List Z3.FourierMode) →
    (include :
      (p : Z3.FourierMode) → p Cube.∈ lefts → p Cube.∈ modes) →
    selfSum lefts include
    ≤
    R109.selectedOrderedPairSum modalED
      (nonzeroOutputSelector cutoff) lefts modes
  selfSumBelowSelectedPairs [] include = ℚP.≤-refl
  selfSumBelowSelectedPairs (p ∷ rest) include =
    ℚP.+-mono-≤
      (selfInnerBelowSelectedKernel
        p
        (include p (Cube.here refl))
        modes
        (λ q member → member))
      (selfSumBelowSelectedPairs
        rest
        (λ selected member → include selected (Cube.there member)))

  globalSelfPhase : ℚ
  globalSelfPhase =
    selfSum modes (λ mode member → member)

  globalSelfPhaseBelowTwoED :
    globalSelfPhase
    ≤
    (R109.sumEnergy modalED modes * R109.sumDissipation modalED modes)
      +
    (R109.sumEnergy modalED modes * R109.sumDissipation modalED modes)
  globalSelfPhaseBelowTwoED =
    ℚP.≤-trans
      (selfSumBelowSelectedPairs modes (λ mode member → member))
      (R109.selectedPairEnergyDissipationProductBound
        modalED (nonzeroOutputSelector cutoff) modes)
