module DASHI.Physics.Closure.NSTriadKNPressureHessianOrderedTermRationalBoundRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite-dimensional Cauchy--Schwarz inequality; DOI not applicable.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- ROUND85 / LITERAL ORDERED HESSIAN TERM SOURCE MAJORANT
--
-- On the exact rational C3 carrier, for an ordered physical interaction
-- k=p+q, the pressure-Hessian part is
--
--   P_k [ H(q) u_p ].
--
-- The same-mode pressure source satisfies
--
--   h_q = |q|^2 pHat_q,
--
-- and the rank-one Hessian action obeys
--
--   ||H(q)u_p||^2 <= |h_q|^2 ||u_p||^2.
--
-- Combining this with sharp rational Hermitian Cauchy and exact Leray
-- contraction gives, for every test v_k,
--
--   |<v_k, P_k[H(q)u_p]>|^2
--     <= ||v_k||^2 |h_q|^2 ||u_p||^2.
--
-- This is the exact termwise convolution majorant needed by the C4 pressure
-- Hessian share.  The remaining theorem is the cutoff-uniform shell summation,
-- not a local matrix estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as RationalL2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRationalComplex3HermitianCauchyRound74Exact as Cauchy
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3EuclideanSelfPairing as Self
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayOut
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPressurePotentialGradientHessianSameModeRound85Exact as Potential
import DASHI.Physics.Closure.NSTriadKNPressureTransportPoissonSplitRound85Exact as Transport
import DASHI.Physics.Closure.NSTriadKNDNPressureHessianTransportSplitRound85Exact as HessianSplit

F : C3.RealField _
F = RationalL2.rationalRealField

complexModulusMultiply : ∀ left right →
  L2.complexModulusSquared {F = F} (C3.complexMultiply left right)
  ≡ L2.complexModulusSquared left * L2.complexModulusSquared right
complexModulusMultiply
    (C3.complex lr li) (C3.complex rr ri) =
  solve (lr ∷ li ∷ rr ∷ ri ∷ [])

complexModulusNegate : ∀ value →
  L2.complexModulusSquared {F = F} (C3.complexNegate value)
  ≡ L2.complexModulusSquared value
complexModulusNegate (C3.complex real imaginary) =
  solve (real ∷ imaginary ∷ [])

complex3ScaleNormSquared : ∀ scalar value →
  L2.complex3NormSquared {F = F} (C3.complex3Scale scalar value)
  ≡ L2.complexModulusSquared scalar * L2.complex3NormSquared value
complex3ScaleNormSquared
    (C3.complex sr si)
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (sr ∷ si ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

complex3ConjugateNormInvariant : ∀ value →
  L2.complex3NormSquared {F = F} (C3.complex3Conjugate value)
  ≡ L2.complex3NormSquared value
complex3ConjugateNormInvariant
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

hermitianConjugateLeftIsBilinear : ∀ left right →
  C3.hermitianPairing3 (C3.complex3Conjugate left) right
  ≡ C3.bilinearDot3 left right
hermitianConjugateLeftIsBilinear left right =
  cong (λ first → C3.bilinearDot3 first right)
    (C3.complex3ConjugateInvolutive left)

modeVectorNormSquaredExact :
  ∀ (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    mode →
  L2.complex3NormSquared (C3.modeVector E mode)
  ≡ C3.normSquared I mode
modeVectorNormSquaredExact E I mode =
  trans
    (sym (Self.complex3SelfPairingRealPartIsNormSquared (C3.modeVector E mode)))
    (trans
      (cong C3.real
        (Hermitian.realModePairingIsBilinear E mode (C3.modeVector E mode)))
      (trans
        (cong C3.real (LerayOut.modeSelfDotIsEmbeddedNormSquared E I mode))
        refl))

bilinearDotModeCauchy :
  ∀ (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    mode value →
  L2.complexModulusSquared
    (C3.bilinearDot3 value (C3.modeVector E mode))
  ≤ L2.complex3NormSquared value * C3.normSquared I mode
bilinearDotModeCauchy E I mode value =
  let
    conjugateValue = C3.complex3Conjugate value
    modeValue = C3.modeVector E mode
    base = Cauchy.rationalComplex3HermitianCauchy conjugateValue modeValue
    lowerExact =
      cong L2.complexModulusSquared
        (hermitianConjugateLeftIsBilinear value modeValue)
    upperExact = cong₂ _*_
      (complex3ConjugateNormInvariant value)
      (modeVectorNormSquaredExact E I mode)
  in
  subst
    (λ upper →
      L2.complexModulusSquared
        (C3.bilinearDot3 value modeValue) ≤ upper)
    upperExact
    (subst
      (λ lower →
        lower ≤
          L2.complex3NormSquared conjugateValue
          * L2.complex3NormSquared modeValue)
      lowerExact base)

sourceModulusSquaredMeaning :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    mode →
  L2.complexModulusSquared
    (Transport.pressurePoissonSourceCoefficient system mode)
  ≡ L2.complexModulusSquared (Potential.pressurePotential system mode)
      * RationalL2.square (C3.normSquared I mode)
sourceModulusSquaredMeaning {I = I} system mode =
  let
    pHat = Potential.pressurePotential system mode
    norm = C3.normSquared I mode
  in
  trans
    (complexModulusMultiply pHat (C3.realEmbed F norm))
    (cong
      (λ normSquare → L2.complexModulusSquared pHat * normSquare)
      (solve (norm ∷ [])))

pressureHessianActionNormSquaredBound :
  ∀ (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    mode value →
  L2.complex3NormSquared
    (HessianSplit.pressureHessianAction E mode
      (Potential.pressurePotential system mode) value)
  ≤ L2.complexModulusSquared
      (Transport.pressurePoissonSourceCoefficient system mode)
      * L2.complex3NormSquared value
pressureHessianActionNormSquaredBound E I system mode value =
  let
    pHat = Potential.pressurePotential system mode
    dot = C3.bilinearDot3 value (C3.modeVector E mode)
    scalar = C3.complexNegate (C3.complexMultiply pHat dot)
    normMode = C3.normSquared I mode
    pMass = L2.complexModulusSquared pHat
    dotMass = L2.complexModulusSquared dot
    valueMass = L2.complex3NormSquared value

    actionExact :
      L2.complex3NormSquared
        (HessianSplit.pressureHessianAction E mode pHat value)
      ≡ pMass * dotMass * normMode
    actionExact =
      trans
        (complex3ScaleNormSquared scalar (C3.modeVector E mode))
        (trans
          (cong
            (λ scalarMass →
              scalarMass * L2.complex3NormSquared (C3.modeVector E mode))
            (trans
              (complexModulusNegate (C3.complexMultiply pHat dot))
              (complexModulusMultiply pHat dot)))
          (cong
            (λ modeMass → pMass * dotMass * modeMass)
            (modeVectorNormSquaredExact E I mode)))

    cauchy = bilinearDotModeCauchy E I mode value
    modeNN : 0ℚ ≤ normMode
    modeNN =
      subst
        (λ x → 0ℚ ≤ x)
        (modeVectorNormSquaredExact E I mode)
        (Separation.complex3NormSquaredNonnegative (C3.modeVector E mode))
    pMassNN = Separation.complexModulusSquaredNonnegative pHat
    leftFactor = pMass * normMode
    leftFactorNN : 0ℚ ≤ leftFactor
    leftFactorNN =
      let
        instance
          pNN = nonNegative pMassNN
          nNN = nonNegative modeNN
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg pMass normMode
      in
      ℚP.nonNegative⁻¹ leftFactor
    instance leftFactorNNI = nonNegative leftFactorNN

    scaled :
      leftFactor * dotMass
      ≤ leftFactor * (valueMass * normMode)
    scaled = ℚP.*-monoˡ-≤-nonNeg leftFactor cauchy

    scaledReordered :
      pMass * dotMass * normMode
      ≤ (pMass * RationalL2.square normMode) * valueMass
    scaledReordered =
      subst
        (λ lower → lower ≤ (pMass * RationalL2.square normMode) * valueMass)
        (solve (pMass ∷ dotMass ∷ normMode ∷ []))
        (subst
          (λ upper → leftFactor * dotMass ≤ upper)
          (solve (pMass ∷ normMode ∷ valueMass ∷ []))
          scaled)

    sourceExact = sourceModulusSquaredMeaning system mode
  in
  subst
    (λ upper →
      L2.complex3NormSquared
        (HessianSplit.pressureHessianAction E mode pHat value) ≤ upper)
    (cong (λ sourceMass → sourceMass * valueMass) (sym sourceExact))
    (subst
      (λ lower → lower ≤ (pMass * RationalL2.square normMode) * valueMass)
      actionExact
      scaledReordered)

orderedPressureHessianPairingSquaredBound :
  ∀ (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (test : C3.Complex3 F) →
  Z3.NonZeroMode (Physical.k incidence) →
  L2.complexModulusSquared
    (C3.hermitianPairing3 test
      (HessianSplit.hessianOrderedTerm system incidence))
  ≤ L2.complex3NormSquared test
      * (L2.complexModulusSquared
          (Transport.pressurePoissonSourceCoefficient
            system (Physical.q incidence))
        * L2.complex3NormSquared
            (Audit.velocity system (Physical.p incidence)))
orderedPressureHessianPairingSquaredBound E I O system incidence test nonzeroK =
  let
    k = Physical.k incidence
    p = Physical.p incidence
    q = Physical.q incidence
    uP = Audit.velocity system p
    action = HessianSplit.pressureHessianAction E q
      (Potential.pressurePotential system q) uP

    tested = Cauchy.rationalTestedLerayResponseBound
      E I O k test action nonzeroK

    actionBound = pressureHessianActionNormSquaredBound E I system q uP
    testNN = Separation.complex3NormSquaredNonnegative test
    instance testNNI = nonNegative testNN
    scaled = ℚP.*-monoˡ-≤-nonNeg (L2.complex3NormSquared test) actionBound
  in
  ℚP.≤-trans tested scaled

round85PressureHessianActionSourceMajorantConstructed : Bool
round85PressureHessianActionSourceMajorantConstructed = true

round85OrderedPressureHessianPairingSourceMajorantConstructed : Bool
round85OrderedPressureHessianPairingSourceMajorantConstructed = true

round85CutoffUniformPacketHessianConvolutionSummed : Bool
round85CutoffUniformPacketHessianConvolutionSummed = false

round85OrderedPressureHessianPairingSourceMajorantConstructedIsTrue :
  round85OrderedPressureHessianPairingSourceMajorantConstructed ≡ true
round85OrderedPressureHessianPairingSourceMajorantConstructedIsTrue = refl
