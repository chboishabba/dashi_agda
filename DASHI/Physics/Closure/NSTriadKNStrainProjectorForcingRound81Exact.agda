module DASHI.Physics.Closure.NSTriadKNStrainProjectorForcingRound81Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Dhawal Buaria; Alain Pumir,
-- "Role of pressure in the dynamics of intense velocity gradients in
-- turbulent flows", Journal of Fluid Mechanics 973 (2023), A23.
-- DOI: 10.1017/jfm.2023.786.
--
-- Their strain equation is
--
--   D_t S_ij
--     = - S_ik S_kj
--       - 1/4 (omega_i omega_j - |omega|^2 delta_ij)
--       - H_ij
--       + nu Delta S_ij.
--
-- ROUND81 / PHYSICAL C4 SOURCE SHAPE
--
-- In the instantaneous eigenbasis of S, S^2 is diagonal.  On an off-diagonal
-- cluster-complement coordinate i != j, delta_ij=0 as well.  Therefore the
-- material strain derivative entering the spectral-projector Sylvester equation
-- has the exact reduced form
--
--   (D_t S)_ij = - 1/4 omega_i omega_j - H_ij + nu (Delta S)_ij.
--
-- Thus the separated-projector problem does not need to fund the strain
-- self-square or isotropic vorticity term: they vanish from the off-block
-- forcing exactly.
--
-- The local vorticity-feedback part has an additional exact cluster identity.
-- For one distinguished line coordinate w and the two complementary
-- coordinates v,z,
--
--   (1/4 w v)^2 + (1/4 w z)^2
--     = (1/16) w^2 (v^2+z^2).
--
-- If w^2 = Omega alpha and v^2+z^2 = Omega(1-alpha), this is
--
--   (Omega^2 / 16) alpha(1-alpha).
--
-- Hence the purely local vorticity contribution to projector turnover is
-- automatically small at either perfect alignment or perfect orthogonality;
-- the genuinely nonlocal pressure-Hessian and viscous off-block terms remain.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

quarter : ℚ
quarter = (+ 1) / 4

record OffDiagonalStrainEvolutionDatum : Set where
  field
    omegaI omegaJ omegaSquared : ℚ
    strainSquareOff diagonalSymbol : ℚ
    pressureHessianOff viscosity laplaceStrainOff : ℚ
    materialStrainDerivativeOff : ℚ

    strainEigenbasisKillsSelfSquareOff : strainSquareOff ≡ 0ℚ
    offDiagonalKillsKronecker : diagonalSymbol ≡ 0ℚ

    sourceStrainEquation :
      materialStrainDerivativeOff
      ≡ - strainSquareOff
        - quarter * (omegaI * omegaJ - omegaSquared * diagonalSymbol)
        - pressureHessianOff
        + viscosity * laplaceStrainOff

open OffDiagonalStrainEvolutionDatum public

offDiagonalMaterialStrainDerivativeReduced :
  (datum : OffDiagonalStrainEvolutionDatum) →
  materialStrainDerivativeOff datum
  ≡ - quarter * (omegaI datum * omegaJ datum)
    - pressureHessianOff datum
    + viscosity datum * laplaceStrainOff datum
offDiagonalMaterialStrainDerivativeReduced datum =
  trans
    (sourceStrainEquation datum)
    (subst
      (λ self →
        - self
        - quarter * (omegaI datum * omegaJ datum
          - omegaSquared datum * diagonalSymbol datum)
        - pressureHessianOff datum
        + viscosity datum * laplaceStrainOff datum
        ≡ - quarter * (omegaI datum * omegaJ datum)
          - pressureHessianOff datum
          + viscosity datum * laplaceStrainOff datum)
      (sym (strainEigenbasisKillsSelfSquareOff datum))
      (subst
        (λ diagonal →
          - 0ℚ
          - quarter * (omegaI datum * omegaJ datum
            - omegaSquared datum * diagonal)
          - pressureHessianOff datum
          + viscosity datum * laplaceStrainOff datum
          ≡ - quarter * (omegaI datum * omegaJ datum)
            - pressureHessianOff datum
            + viscosity datum * laplaceStrainOff datum)
        (sym (offDiagonalKillsKronecker datum))
        (ℚRing.solve-∀
          quarter (omegaI datum) (omegaJ datum)
          (pressureHessianOff datum) (viscosity datum)
          (laplaceStrainOff datum))))

square : ℚ → ℚ
square x = x * x

record LineVsPlaneVorticityFeedback : Set where
  field
    lineOmega transverseOmegaA transverseOmegaB : ℚ
    enstrophy alignmentWeight : ℚ

    lineSquareIsWeightedEnstrophy :
      square lineOmega ≡ enstrophy * alignmentWeight

    transverseSquareIsComplement :
      square transverseOmegaA + square transverseOmegaB
      ≡ enstrophy * (1ℚ - alignmentWeight)

open LineVsPlaneVorticityFeedback public

localVorticityOffBlockSquareEnergy : LineVsPlaneVorticityFeedback → ℚ
localVorticityOffBlockSquareEnergy datum =
  square (quarter * lineOmega datum * transverseOmegaA datum)
  + square (quarter * lineOmega datum * transverseOmegaB datum)

localVorticityOffBlockFactors :
  (datum : LineVsPlaneVorticityFeedback) →
  localVorticityOffBlockSquareEnergy datum
  ≡ square quarter
    * square (lineOmega datum)
    * (square (transverseOmegaA datum) + square (transverseOmegaB datum))
localVorticityOffBlockFactors datum =
  ℚRing.solve-∀
    quarter
    (lineOmega datum)
    (transverseOmegaA datum)
    (transverseOmegaB datum)

localVorticityOffBlockAlignmentDefectExact :
  (datum : LineVsPlaneVorticityFeedback) →
  localVorticityOffBlockSquareEnergy datum
  ≡ square quarter
    * square (enstrophy datum)
    * alignmentWeight datum
    * (1ℚ - alignmentWeight datum)
localVorticityOffBlockAlignmentDefectExact datum =
  trans
    (localVorticityOffBlockFactors datum)
    (subst
      (λ lineSq →
        square quarter * lineSq
          * (square (transverseOmegaA datum) + square (transverseOmegaB datum))
        ≡ square quarter
          * square (enstrophy datum)
          * alignmentWeight datum
          * (1ℚ - alignmentWeight datum))
      (lineSquareIsWeightedEnstrophy datum)
      (subst
        (λ transverseSq →
          square quarter * (enstrophy datum * alignmentWeight datum)
            * transverseSq
          ≡ square quarter
            * square (enstrophy datum)
            * alignmentWeight datum
            * (1ℚ - alignmentWeight datum))
        (transverseSquareIsComplement datum)
        (ℚRing.solve-∀
          quarter (enstrophy datum) (alignmentWeight datum))))

round81OffBlockStrainForcingReducedExactly : Bool
round81OffBlockStrainForcingReducedExactly = true

round81LocalVorticityProjectorForcingIsAlignmentDefect : Bool
round81LocalVorticityProjectorForcingIsAlignmentDefect = true

round81LocalVorticityProjectorForcingIsAlignmentDefectIsTrue :
  round81LocalVorticityProjectorForcingIsAlignmentDefect ≡ true
round81LocalVorticityProjectorForcingIsAlignmentDefectIsTrue = refl
