module DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeEnergyProductRound105Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result: finite-dimensional Cauchy--Schwarz inequality.
-- DOI: not applicable to the original nineteenth-century results.
--
-- ROUND105 / WALEFFE AMPLITUDE ENERGY PRODUCT
--
-- The literal Waleffe carrier uses
--
--   A = Re <u_k , u_p x u_q>.
--
-- The repository already proves sharp Hermitian Cauchy on rational Complex3.
-- The only missing finite identity is the complex Lagrange identity
--
--   ||u x v||^2 + |<u,v>|^2 = ||u||^2 ||v||^2.
--
-- Consequently
--
--   A^2
--     <= |<u_k,u_p x u_q>|^2
--     <= ||u_k||^2 ||u_p x u_q||^2
--     <= ||u_k||^2 ||u_p||^2 ||u_q||^2.
--
-- This is radical-free and exact.  It supplies the amplitude/energy comparison
-- needed by the Round94--96 residence/excess programme without a statistical
-- closure or a new norm receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRationalComplex3HermitianCauchyRound74Exact as HC
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as Transfer

F : C3.RealField _
F = Rational.rationalRealField

crossLagrangeIdentity : (u v : C3.Complex3 F) →
  L2.complex3NormSquared (Cross.complex3Cross u v)
    + L2.complexModulusSquared (C3.hermitianPairing3 u v)
  ≡ L2.complex3NormSquared u * L2.complex3NormSquared v
crossLagrangeIdentity
  (C3.complex3
    (C3.complex ur1 ui1) (C3.complex ur2 ui2) (C3.complex ur3 ui3))
  (C3.complex3
    (C3.complex vr1 vi1) (C3.complex vr2 vi2) (C3.complex vr3 vi3)) =
  solve
    ( ur1 ∷ ui1 ∷ ur2 ∷ ui2 ∷ ur3 ∷ ui3
    ∷ vr1 ∷ vi1 ∷ vr2 ∷ vi2 ∷ vr3 ∷ vi3 ∷ [])

crossNormSquaredBelowProduct : (u v : C3.Complex3 F) →
  L2.complex3NormSquared (Cross.complex3Cross u v)
  ≤ L2.complex3NormSquared u * L2.complex3NormSquared v
crossNormSquaredBelowProduct u v =
  let
    crossMass = L2.complex3NormSquared (Cross.complex3Cross u v)
    pairingMass = L2.complexModulusSquared (C3.hermitianPairing3 u v)
    pairingNN = Separation.complexModulusSquaredNonnegative
      (C3.hermitianPairing3 u v)
    addPairing : crossMass ≤ crossMass + pairingMass
    addPairing =
      subst
        (λ lower → lower ≤ crossMass + pairingMass)
        (ℚP.+-identityʳ crossMass)
        (ℚP.+-monoʳ-≤ crossMass pairingNN)
  in
  subst
    (λ upper → crossMass ≤ upper)
    (crossLagrangeIdentity u v)
    addPairing

waleffeComplexAmplitude :
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
waleffeComplexAmplitude uK uP uQ =
  C3.hermitianPairing3 uK (Cross.complex3Cross uP uQ)

waleffeRealAmplitude :
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → ℚ
waleffeRealAmplitude uK uP uQ = C3.real (waleffeComplexAmplitude uK uP uQ)

waleffeAmplitudeSquaredBelowEnergyProduct :
  (uK uP uQ : C3.Complex3 F) →
  waleffeRealAmplitude uK uP uQ * waleffeRealAmplitude uK uP uQ
  ≤ L2.complex3NormSquared uK
      * L2.complex3NormSquared uP
      * L2.complex3NormSquared uQ
waleffeAmplitudeSquaredBelowEnergyProduct uK uP uQ =
  let
    cross = Cross.complex3Cross uP uQ
    z = waleffeComplexAmplitude uK uP uQ

    realBelowModulus :
      C3.real z * C3.real z ≤ L2.complexModulusSquared z
    realBelowModulus = Transfer.realCoordinateSquareBelowModulus z

    cauchy :
      L2.complexModulusSquared z
      ≤ L2.complex3NormSquared uK * L2.complex3NormSquared cross
    cauchy = HC.rationalComplex3HermitianCauchy uK cross

    crossBound :
      L2.complex3NormSquared cross
      ≤ L2.complex3NormSquared uP * L2.complex3NormSquared uQ
    crossBound = crossNormSquaredBelowProduct uP uQ

    uKNN = Separation.complex3NormSquaredNonnegative uK
    scaledCross :
      L2.complex3NormSquared uK * L2.complex3NormSquared cross
      ≤ L2.complex3NormSquared uK
          * (L2.complex3NormSquared uP * L2.complex3NormSquared uQ)
    scaledCross =
      let instance kNN = nonNegative uKNN
      in ℚP.*-monoˡ-≤-nonNeg (L2.complex3NormSquared uK) crossBound

    reassociate :
      L2.complex3NormSquared uK
        * (L2.complex3NormSquared uP * L2.complex3NormSquared uQ)
      ≡ L2.complex3NormSquared uK
          * L2.complex3NormSquared uP
          * L2.complex3NormSquared uQ
    reassociate = solve
      ( L2.complex3NormSquared uK
      ∷ L2.complex3NormSquared uP
      ∷ L2.complex3NormSquared uQ ∷ [])
  in
  ℚP.≤-trans realBelowModulus
    (ℚP.≤-trans cauchy
      (subst
        (λ upper →
          L2.complex3NormSquared uK * L2.complex3NormSquared cross ≤ upper)
        reassociate scaledCross))

round105ComplexCrossLagrangeIdentityClosed : Bool
round105ComplexCrossLagrangeIdentityClosed = true

round105WaleffeAmplitudeEnergyProductBoundClosed : Bool
round105WaleffeAmplitudeEnergyProductBoundClosed = true

round105ComplexCrossLagrangeIdentityClosedIsTrue :
  round105ComplexCrossLagrangeIdentityClosed ≡ true
round105ComplexCrossLagrangeIdentityClosedIsTrue = refl

round105WaleffeAmplitudeEnergyProductBoundClosedIsTrue :
  round105WaleffeAmplitudeEnergyProductBoundClosed ≡ true
round105WaleffeAmplitudeEnergyProductBoundClosedIsTrue = refl
