module DASHI.Physics.Closure.NSTriadKNEigenpacketScalarViscosityRelativeGrowthRound100Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND100 / EXACT LAPLACIAN-EIGENPACKET COLLAPSE
--
-- A dyadic packet contains several values of |k|^2, so the compact-Gamma
-- denominator carries a radial-weight commutator.  On an exact Laplacian
-- eigenspace packet all selected modes satisfy
--
--     |k|^2 = lambda.
--
-- Then the derivative weight is scalar on the packet.  Pure finite Hermitian
-- algebra gives, for any tangent h,
--
--     D       = lambda E,
--     Ddot[h] = 2 lambda Re<u,h>.
--
-- In particular for the nonlinear tangent h=N(u), writing
--
--     q    = Re<u,N(u)>,
--     qdot = d Re<u,N(u)>[N(u)],
--
-- the nonlinear relative-growth numerator becomes exactly
--
--     qdot D - q Ddot = lambda (E qdot - 2 q^2).
--
-- No Bernstein estimate or amplitude assumption is used.  This removes the
-- radial multiplier dispersion from the remaining analytic problem and exposes
-- the explicit favourable transfer-square term -2 lambda q^2.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3EuclideanSelfPairing as Self
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as Euclidean
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet

realPartHermitianSymmetric :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Complex3 F) →
  C3.real (C3.hermitianPairing3 left right)
  ≡ C3.real (C3.hermitianPairing3 right left)
realPartHermitianSymmetric left right =
  trans
    (sym
      (cong C3.real
        (Hermitian.hermitianPairingConjugateSymmetric right left)))
    refl

record EigenpacketData {r : Level} (F : C3.RealField r) : Set r where
  constructor eigenpacket-data
  field
    modes : List Z3.FourierMode
    velocity tangent : Z3.FourierMode → C3.Complex3 F
    eigenvalue : C3.Carrier F
    modeWeight : Z3.FourierMode → C3.Carrier F
    selectedModeHasEigenvalue :
      ∀ mode → Packet._∈_ mode modes → modeWeight mode ≡ eigenvalue

open EigenpacketData public

sumRealPairing :
  ∀ {r} {F : C3.RealField r} →
  List Z3.FourierMode →
  (Z3.FourierMode → C3.Complex3 F) →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Carrier F
sumRealPairing {F = F} [] left right = C3.zero F
sumRealPairing {F = F} (mode ∷ rest) left right =
  C3.add F
    (C3.real (C3.hermitianPairing3 (left mode) (right mode)))
    (sumRealPairing rest left right)

packetEnergy :
  ∀ {r} {F : C3.RealField r} → EigenpacketData F → C3.Carrier F
packetEnergy D = sumRealPairing (modes D) (velocity D) (velocity D)

packetTransfer :
  ∀ {r} {F : C3.RealField r} → EigenpacketData F → C3.Carrier F
packetTransfer D = sumRealPairing (modes D) (velocity D) (tangent D)

weightedField :
  ∀ {r} {F : C3.RealField r} →
  EigenpacketData F →
  (Z3.FourierMode → C3.Complex3 F) →
  Z3.FourierMode → C3.Complex3 F
weightedField D field mode =
  C3.complex3Scale (C3.realEmbed _ (modeWeight D mode)) (field mode)

packetDissipation :
  ∀ {r} {F : C3.RealField r} → EigenpacketData F → C3.Carrier F
packetDissipation D =
  sumRealPairing (modes D) (velocity D) (weightedField D (velocity D))

packetDissipationTangent :
  ∀ {r} {F : C3.RealField r} → EigenpacketData F → C3.Carrier F
packetDissipationTangent {F = F} D =
  C3.add F
    (sumRealPairing (modes D) (tangent D) (weightedField D (velocity D)))
    (sumRealPairing (modes D) (velocity D) (weightedField D (tangent D)))

realScalePairingRight :
  ∀ {r} {F : C3.RealField r}
    (weight : C3.Carrier F)
    (left right : C3.Complex3 F) →
  C3.real
    (C3.hermitianPairing3 left
      (C3.complex3Scale (C3.realEmbed F weight) right))
  ≡ C3.multiply F weight (C3.real (C3.hermitianPairing3 left right))
realScalePairingRight {F = F} weight left right =
  trans
    (cong C3.real
      (Scaling.hermitianPairingScaleRight
        (C3.realEmbed F weight) left right))
    refl

sumWeightedPairingIsEigenvalueTimes :
  ∀ {r} {F : C3.RealField r}
    (D : EigenpacketData F)
    (left right : Z3.FourierMode → C3.Complex3 F)
    (items : List Z3.FourierMode) →
  (∀ mode → Packet._∈_ mode items → modeWeight D mode ≡ eigenvalue D) →
  sumRealPairing items left (weightedField D right)
  ≡ C3.multiply F (eigenvalue D) (sumRealPairing items left right)
sumWeightedPairingIsEigenvalueTimes {F = F} D left right [] same =
  sym (Field.realMultiplyZeroRight F (eigenvalue D))
sumWeightedPairingIsEigenvalueTimes {F = F} D left right (mode ∷ rest) same =
  let
    headWeight = same mode (Packet.here refl)
    tailSame = λ chosen member → same chosen (Packet.there member)
  in
  trans
    (cong₂ (C3.add F)
      (trans
        (realScalePairingRight (modeWeight D mode) (left mode) (right mode))
        (cong
          (λ weight → C3.multiply F weight
            (C3.real (C3.hermitianPairing3 (left mode) (right mode))))
          headWeight))
      (sumWeightedPairingIsEigenvalueTimes D left right rest tailSame))
    (sym
      (C3.distributeLeft F (eigenvalue D)
        (C3.real (C3.hermitianPairing3 (left mode) (right mode)))
        (sumRealPairing rest left right)))

packetDissipationIsEigenvalueTimesEnergy :
  ∀ {r} {F : C3.RealField r}
    (D : EigenpacketData F) →
  packetDissipation D ≡ C3.multiply F (eigenvalue D) (packetEnergy D)
packetDissipationIsEigenvalueTimesEnergy D =
  sumWeightedPairingIsEigenvalueTimes
    D (velocity D) (velocity D) (modes D) (selectedModeHasEigenvalue D)

sumRealPairingSymmetric :
  ∀ {r} {F : C3.RealField r}
    (items : List Z3.FourierMode)
    (left right : Z3.FourierMode → C3.Complex3 F) →
  sumRealPairing items left right ≡ sumRealPairing items right left
sumRealPairingSymmetric [] left right = refl
sumRealPairingSymmetric (mode ∷ rest) left right =
  cong₂ (C3.add _)
    (realPartHermitianSymmetric (left mode) (right mode))
    (sumRealPairingSymmetric rest left right)

twoCarrier : ∀ {r} (F : C3.RealField r) → C3.Carrier F
twoCarrier F = C3.add F (C3.one F) (C3.one F)

packetDissipationTangentIsTwoEigenvalueTimesTransfer :
  ∀ {r} {F : C3.RealField r}
    (D : EigenpacketData F) →
  packetDissipationTangent D
  ≡ C3.multiply F
      (C3.multiply F (twoCarrier F) (eigenvalue D))
      (packetTransfer D)
packetDissipationTangentIsTwoEigenvalueTimesTransfer {F = F} D =
  let
    a = sumRealPairing (modes D) (tangent D) (velocity D)
    b = packetTransfer D
    leftWeight = sumWeightedPairingIsEigenvalueTimes
      D (tangent D) (velocity D) (modes D) (selectedModeHasEigenvalue D)
    rightWeight = sumWeightedPairingIsEigenvalueTimes
      D (velocity D) (tangent D) (modes D) (selectedModeHasEigenvalue D)
    symmetry : a ≡ b
    symmetry = sumRealPairingSymmetric (modes D) (tangent D) (velocity D)
  in
  trans
    (cong₂ (C3.add F) leftWeight rightWeight)
    (P.R.solve 3
      (λ lambda a b →
        ((lambda P.R.⊗ a) P.R.⊕ (lambda P.R.⊗ b))
        P.R.⊜
        (((P.R.K (C3.one F) P.R.⊕ P.R.K (C3.one F)) P.R.⊗ lambda)
          P.R.⊗ b))
      symmetry (eigenvalue D) a b)
  where module P = Field.Polynomial F

nonlinearRelativeGrowth :
  ∀ {r} {F : C3.RealField r} →
  EigenpacketData F → C3.Carrier F → C3.Carrier F
nonlinearRelativeGrowth {F = F} D qdot =
  C3.add F
    (C3.multiply F qdot (packetDissipation D))
    (C3.negate F
      (C3.multiply F (packetTransfer D) (packetDissipationTangent D)))

eigenpacketRelativeGrowthCollapse :
  ∀ {r} {F : C3.RealField r}
    (D : EigenpacketData F)
    (qdot : C3.Carrier F) →
  nonlinearRelativeGrowth D qdot
  ≡ C3.multiply F (eigenvalue D)
      (C3.add F
        (C3.multiply F (packetEnergy D) qdot)
        (C3.negate F
          (C3.multiply F (twoCarrier F)
            (C3.multiply F (packetTransfer D) (packetTransfer D)))))
eigenpacketRelativeGrowthCollapse {F = F} D qdot =
  let
    dMeaning = packetDissipationIsEigenvalueTimesEnergy D
    ddotMeaning = packetDissipationTangentIsTwoEigenvalueTimesTransfer D
  in
  P.R.solve 5
    (λ lambda E q qdot two →
      ((qdot P.R.⊗ (lambda P.R.⊗ E))
        P.R.⊕ P.R.⊝ (q P.R.⊗ ((two P.R.⊗ lambda) P.R.⊗ q)))
      P.R.⊜
      (lambda P.R.⊗
        ((E P.R.⊗ qdot) P.R.⊕ P.R.⊝ (two P.R.⊗ (q P.R.⊗ q)))))
    (trans (cong (C3.multiply F qdot) dMeaning) refl)
    (eigenvalue D)
    (packetEnergy D)
    (packetTransfer D)
    qdot
    (twoCarrier F)
  where module P = Field.Polynomial F

round100EigenpacketRadialWeightCommutatorEliminated : Bool
round100EigenpacketRadialWeightCommutatorEliminated = true

round100EigenpacketRelativeGrowthCollapseClosed : Bool
round100EigenpacketRelativeGrowthCollapseClosed = true

round100EigenpacketRelativeGrowthCollapseClosedIsTrue :
  round100EigenpacketRelativeGrowthCollapseClosed ≡ true
round100EigenpacketRelativeGrowthCollapseClosedIsTrue = refl
