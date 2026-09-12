module DASHI.Physics.Closure.NSTriadKNSpectatorAmplitudeEnergyMassUnitGapBidiExact where

------------------------------------------------------------------------
-- SPECTATOR AMPLITUDE POSITIVE MASS -> C_nu^2 * GLOBAL CUTOFF ENERGY^2
--
-- On one nonzero physical output fibre R450 gives the shared cell-rate floor
-- nu.  The preceding same-output resolvent owner gives
--
--   W_beta(alpha) <= C_nu = 1/(2 nu).
--
-- Positivity of the reciprocal plus the repository product-monotonicity gives
-- W^2 <= C_nu^2.  The mixed-helicity cell owner already gives
--
--   ||A_alpha||^2 <= E_p E_q.
--
-- Summing over the literal output fibre introduces no cardinality factor, and
-- R454 closes the remaining selected pair-energy sum by the square of total
-- cutoff energy.  Thus the positive cell-mass half of the amplitude Gram ledger
-- is no longer a live analytic residual; only selected signed interference
-- remains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; Positive; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.Closure.NSTriadKNFixedOutputEnergySquareRoutingRound454Exact as R454
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergySquareRound453Exact as R453
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventUnitGapCeilingBidiExact as Ceiling
import DASHI.Physics.Closure.NSTriadKNSpectatorAmplitudeSelectedGramEnergyFrontierBidiExact as Frontier
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

F : C3.RealField _
F = Rational.rationalRealField

module UnitGapAmplitudeMass
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode))
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem) where

  module C = Ceiling.SameOutputResolventCeiling
    physicalSystem S viscosityPositive unitGap
  module A = Frontier.AmplitudeFrontier
    physicalSystem S L velocityTransverse

  velocity = Audit.velocity (Field30.finiteSystem physicalSystem)

  energy : Z3.FourierMode → ℚ
  energy mode = L2.complex3NormSquared (velocity mode)

  modalEnergy : R453.ModalEnergy Z3.FourierMode
  modalEnergy = R453.modal-energy energy
    (λ mode → Separation.complex3NormSquaredNonnegative (velocity mode))

  ceilingNN : 0ℚ ≤ C.ceiling
  ceilingNN =
    ℚP.<⇒≤
      (Quotient.positiveReciprocalPositive
        (R449.two * C.nu) (R449.twicePositive C.Floor.nuPositive))

  pairResolventNN :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    0ℚ ≤ C.Pair.pairResolvent alpha beta
  pairResolventNN output outputNonzero alpha beta alphaK betaK =
    let
      denomPositive = C.pairRatePositive output outputNonzero alpha beta alphaK betaK
      asPositive = R449.safeReciprocalIsPositiveReciprocal _ denomPositive
    in
    subst
      (0ℚ ≤_)
      (sym asPositive)
      (ℚP.<⇒≤
        (Quotient.positiveReciprocalPositive _ denomPositive))

  resolventSquareBelowCeilingSquare :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    C.Pair.pairResolvent alpha beta * C.Pair.pairResolvent alpha beta
    ≤ C.ceiling * C.ceiling
  resolventSquareBelowCeilingSquare output outputNonzero alpha beta alphaK betaK =
    Rational.nonnegativeProductMonotone
      (pairResolventNN output outputNonzero alpha beta alphaK betaK)
      (pairResolventNN output outputNonzero alpha beta alphaK betaK)
      ceilingNN ceilingNN
      (C.pairResolventBelowCeiling output outputNonzero alpha beta alphaK betaK)
      (C.pairResolventBelowCeiling output outputNonzero alpha beta alphaK betaK)

  data AllSameOutput (output : Z3.FourierMode) :
      List Physical.PhysicalTriadIncidence → Set where
    same[] : AllSameOutput output []
    same∷ : ∀ {alpha rest} →
      Physical.k alpha ≡ output →
      AllSameOutput output rest →
      AllSameOutput output (alpha ∷ rest)

  weightedMajorantBelowCeilingPairs :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (beta : Physical.PhysicalTriadIncidence) →
    Physical.k beta ≡ output →
    (items : List Physical.PhysicalTriadIncidence) →
    AllSameOutput output items →
    A.weightedEnergyMajorant beta items
    ≤ (C.ceiling * C.ceiling) * R454.triadEnergyProductSum energy items
  weightedMajorantBelowCeilingPairs output outputNonzero beta betaK [] same[] =
    ℚP.≤-refl
  weightedMajorantBelowCeilingPairs output outputNonzero beta betaK
      (alpha ∷ rest) (same∷ alphaK restK) =
    let
      c2 = C.ceiling * C.ceiling
      w2Below = resolventSquareBelowCeilingSquare
        output outputNonzero alpha beta alphaK betaK
      pairEnergy = energy (Physical.p alpha) * energy (Physical.q alpha)
      restPairs = R454.triadEnergyProductSum energy rest
      pairNN = Rational.productNonnegative
        (Separation.complex3NormSquaredNonnegative (velocity (Physical.p alpha)))
        (Separation.complex3NormSquaredNonnegative (velocity (Physical.q alpha)))
      headBound :
        (C.Pair.pairResolvent alpha beta * C.Pair.pairResolvent alpha beta) * pairEnergy
        ≤ c2 * pairEnergy
      headBound =
        let instance pairNNI = nonNegative pairNN
        in ℚP.*-monoʳ-≤-nonNeg pairEnergy w2Below
      tailBound = weightedMajorantBelowCeilingPairs
        output outputNonzero beta betaK rest restK
      summed :
        (C.Pair.pairResolvent alpha beta * C.Pair.pairResolvent alpha beta) * pairEnergy
          + A.weightedEnergyMajorant beta rest
        ≤ c2 * pairEnergy + c2 * restPairs
      summed = ℚP.+-mono-≤ headBound tailBound
      distribute : c2 * pairEnergy + c2 * restPairs ≡ c2 * (pairEnergy + restPairs)
      distribute = solve (c2 ∷ pairEnergy ∷ restPairs ∷ [])
    in
    subst
      (λ upper →
        (C.Pair.pairResolvent alpha beta * C.Pair.pairResolvent alpha beta) * pairEnergy
          + A.weightedEnergyMajorant beta rest
        ≤ upper)
      distribute
      summed

  allSameFromMembership :
    (output : Z3.FourierMode) →
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha Cube.∈ items → Physical.k alpha ≡ output) →
    AllSameOutput output items
  allSameFromMembership output [] sound = same[]
  allSameFromMembership output (alpha ∷ rest) sound =
    same∷
      (sound alpha (Cube.here refl))
      (allSameFromMembership output rest
        (λ item member → sound item (Cube.there member)))

  physicalFibreAllSame :
    (cutoff : Nat) (output : Z3.FourierMode) →
    AllSameOutput output (Output.physicalOutputFiber cutoff output)
  physicalFibreAllSame cutoff output =
    allSameFromMembership output (Output.physicalOutputFiber cutoff output)
      (λ alpha member → Output.physicalOutputFiberSound member)

  physicalWeightedEnergyMajorantBelowGlobalEnergySquare :
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (beta : Physical.PhysicalTriadIncidence) →
    Physical.k beta ≡ output →
    A.weightedEnergyMajorant beta (Output.physicalOutputFiber cutoff output)
    ≤ (C.ceiling * C.ceiling)
      * (R453.sumEnergy modalEnergy (Cube.cutoffModes cutoff)
        * R453.sumEnergy modalEnergy (Cube.cutoffModes cutoff))
  physicalWeightedEnergyMajorantBelowGlobalEnergySquare
      cutoff output outputNonzero beta betaK =
    let
      local = weightedMajorantBelowCeilingPairs
        output outputNonzero beta betaK
        (Output.physicalOutputFiber cutoff output)
        (physicalFibreAllSame cutoff output)
      selected = R454.WithEnergy.physicalOutputFibreEnergyBelowSquare
        modalEnergy cutoff output
      c2NN = Rational.productNonnegative ceilingNN ceilingNN
      scaledSelected =
        let instance c2NNI = nonNegative c2NN
        in ℚP.*-monoˡ-≤-nonNeg (C.ceiling * C.ceiling) selected
    in
    ℚP.≤-trans local scaledSelected

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

spectatorAmplitudePositiveMassUniformInCutoffPaid : Bool
spectatorAmplitudePositiveMassUniformInCutoffPaid = true

spectatorAmplitudePositiveMassCardinalityTax : Bool
spectatorAmplitudePositiveMassCardinalityTax = false

spectatorAmplitudeSelectedSignedGramStillOpen : Bool
spectatorAmplitudeSelectedSignedGramStillOpen = true

clayPromotion : Bool
clayPromotion = false
