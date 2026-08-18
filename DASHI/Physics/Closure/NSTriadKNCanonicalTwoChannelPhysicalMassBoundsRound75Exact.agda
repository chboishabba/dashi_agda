module DASHI.Physics.Closure.NSTriadKNCanonicalTwoChannelPhysicalMassBoundsRound75Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite-dimensional Cauchy--Schwarz inequality; DOI not applicable.
--
-- ROUND75 / BOTH CANONICAL TWO-CHANNEL MASSES ARE PHYSICAL NORM QUANTITIES
--
-- Round74 identified, on each literal PhysicalTriadIncidence,
--
--   Q_tau = |-i (u_p dot q)|^2,
--   W_tau = |<test_k, P_k u_q>|^2.
--
-- Round74 already constructed the sharp rational response estimate
--
--   W_tau <= ||test_k||^2 ||u_q||^2.
--
-- This file closes the matching transport side.  On the exact rational C3
-- carrier, multiplication by -i preserves modulus squared and the complex
-- BILINEAR dot is Cauchy-controlled by conjugating the first argument and
-- reusing the already-proved Hermitian Cauchy identity:
--
--   Q_tau = |u_p dot q|^2 <= ||u_p||^2 ||q||^2.
--
-- Thus neither Q nor W is an arbitrary factorization coordinate anymore.
-- Remaining theorem-4 work is summing/normalizing these SAME per-incidence
-- masses on the selected physical subfibre and identifying the resulting
-- charge with the globally budgeted trajectory quantity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as RationalL2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3HermitianCauchyRound74Exact as Hermitian
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOrderedInteractionSourceFactorizationRound73Exact as Source
import DASHI.Physics.Closure.NSTriadKNOrderedInteractionTwoChannelMassIdentityRound74Exact as Mass

F : C3.RealField _
F = RationalL2.rationalRealField

massModulusAgreesWithL2 : ∀ z →
  Mass.complexModulusSquared {F = F} z
  ≡ L2.complexModulusSquared {F = F} z
massModulusAgreesWithL2 (C3.complex real imaginary) = refl

complexModulusSquaredConjugate : ∀ z →
  L2.complexModulusSquared {F = F} (C3.complexConjugate z)
  ≡ L2.complexModulusSquared {F = F} z
complexModulusSquaredConjugate (C3.complex real imaginary) =
  solve (real ∷ imaginary ∷ [])

complex3NormSquaredConjugate : ∀ value →
  L2.complex3NormSquared {F = F} (C3.complex3Conjugate value)
  ≡ L2.complex3NormSquared {F = F} value
complex3NormSquaredConjugate
  (C3.complex3
    (C3.complex xr xi)
    (C3.complex yr yi)
    (C3.complex zr zi)) =
  solve (xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

bilinearDotAsHermitianConjugate : ∀ left right →
  C3.bilinearDot3 {F = F} left right
  ≡ C3.hermitianPairing3 (C3.complex3Conjugate left) right
bilinearDotAsHermitianConjugate left right =
  sym
    (cong
      (λ selected → C3.bilinearDot3 selected right)
      (C3.complex3ConjugateInvolutive left))

rationalComplex3BilinearCauchy : ∀ left right →
  L2.complexModulusSquared (C3.bilinearDot3 {F = F} left right)
  ≤ L2.complex3NormSquared left * L2.complex3NormSquared right
rationalComplex3BilinearCauchy left right =
  let
    conjugatedLeft = C3.complex3Conjugate left
    hermitianBound = Hermitian.rationalComplex3HermitianCauchy conjugatedLeft right
    pairingEquality = bilinearDotAsHermitianConjugate left right
    conjugateNorm = complex3NormSquaredConjugate left
    transportedPairing :
      L2.complexModulusSquared (C3.bilinearDot3 left right)
      ≤ L2.complex3NormSquared conjugatedLeft * L2.complex3NormSquared right
    transportedPairing =
      subst
        (λ selected →
          L2.complexModulusSquared selected
          ≤ L2.complex3NormSquared conjugatedLeft
            * L2.complex3NormSquared right)
        (sym pairingEquality)
        hermitianBound
  in
  subst
    (λ leftMass →
      L2.complexModulusSquared (C3.bilinearDot3 left right)
      ≤ leftMass * L2.complex3NormSquared right)
    conjugateNorm
    transportedPairing

minusIMultiplyPreservesModulusSquared : ∀ z →
  L2.complexModulusSquared
    (C3.complexMultiply
      (C3.complexNegate (C3.complexI F)) z)
  ≡ L2.complexModulusSquared z
minusIMultiplyPreservesModulusSquared (C3.complex real imaginary) =
  solve (real ∷ imaginary ∷ [])

transportScalarModulusSquaredExact :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  L2.complexModulusSquared (Source.transportScalar system incidence)
  ≡ L2.complexModulusSquared (Source.interactionScalar system incidence)
transportScalarModulusSquaredExact system incidence =
  minusIMultiplyPreservesModulusSquared (Source.interactionScalar system incidence)

interactionScalarEnergyBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  L2.complexModulusSquared (Source.interactionScalar system incidence)
  ≤
  L2.complex3NormSquared
    (Audit.velocityAt system (Physical.p incidence))
  * L2.complex3NormSquared
    (C3.modeVector (Audit.integerEmbedding system) (Physical.q incidence))
interactionScalarEnergyBound system incidence =
  rationalComplex3BilinearCauchy
    (Audit.velocityAt system (Physical.p incidence))
    (C3.modeVector (Audit.integerEmbedding system) (Physical.q incidence))

orderedInteractionCanonicalQBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  Mass.leftChannelSquaredMass
    (DASHI.Physics.Closure.NSTriadKNOrderedInteractionRealImaginaryTwoChannelRound74Exact.orderedInteractionChannels
      system incidence (Audit.velocityAt system (Physical.k incidence)))
  ≤
  L2.complex3NormSquared
    (Audit.velocityAt system (Physical.p incidence))
  * L2.complex3NormSquared
    (C3.modeVector (Audit.integerEmbedding system) (Physical.q incidence))
orderedInteractionCanonicalQBound system incidence =
  let
    testK = Audit.velocityAt system (Physical.k incidence)
    qIdentity = Mass.orderedInteractionLeftMassExact system incidence testK
    modulusBridge = massModulusAgreesWithL2 (Source.transportScalar system incidence)
    transportExact = transportScalarModulusSquaredExact system incidence
    interactionBound = interactionScalarEnergyBound system incidence
  in
  subst
    (λ qMass → qMass ≤
      L2.complex3NormSquared
        (Audit.velocityAt system (Physical.p incidence))
      * L2.complex3NormSquared
        (C3.modeVector (Audit.integerEmbedding system) (Physical.q incidence)))
    (trans qIdentity (trans modulusBridge transportExact))
    interactionBound

orderedInteractionCanonicalWBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (nonzeroOutput : Z3.NonZeroMode (Physical.k incidence))
    (testK : C3.Complex3 F) →
  Mass.rightChannelSquaredMass
    (DASHI.Physics.Closure.NSTriadKNOrderedInteractionRealImaginaryTwoChannelRound74Exact.orderedInteractionChannels
      system incidence testK)
  ≤
  L2.complex3NormSquared testK
  * L2.complex3NormSquared
      (Audit.velocityAt system (Physical.q incidence))
orderedInteractionCanonicalWBound O system incidence nonzeroOutput testK =
  let
    wIdentity = Mass.orderedInteractionRightMassExact system incidence testK
    modulusBridge = massModulusAgreesWithL2 (Source.testedHighResponse system incidence testK)
    responseBound =
      Hermitian.rationalTestedLerayResponseBound
        (Audit.integerEmbedding system)
        (Audit.inverseSquare system)
        O
        (Physical.k incidence)
        testK
        (Audit.velocityAt system (Physical.q incidence))
        nonzeroOutput
  in
  subst
    (λ wMass → wMass ≤
      L2.complex3NormSquared testK
      * L2.complex3NormSquared (Audit.velocityAt system (Physical.q incidence)))
    (trans wIdentity modulusBridge)
    responseBound

round75CanonicalQPerTriadEnergyBoundConstructed : Bool
round75CanonicalQPerTriadEnergyBoundConstructed = true

round75CanonicalWPerTriadEnergyBoundConstructed : Bool
round75CanonicalWPerTriadEnergyBoundConstructed = true

round75TwoChannelPerTriadMassesBothPhysicalNormControlled : Bool
round75TwoChannelPerTriadMassesBothPhysicalNormControlled = true

round75SummedPhysicalFrameNormalizationAndChargeIdentityConstructed : Bool
round75SummedPhysicalFrameNormalizationAndChargeIdentityConstructed = false

round75TwoChannelPerTriadMassesBothPhysicalNormControlledIsTrue :
  round75TwoChannelPerTriadMassesBothPhysicalNormControlled ≡ true
round75TwoChannelPerTriadMassesBothPhysicalNormControlledIsTrue = refl
