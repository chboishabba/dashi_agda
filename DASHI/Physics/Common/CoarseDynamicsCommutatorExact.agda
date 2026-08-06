module DASHI.Physics.Common.CoarseDynamicsCommutatorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Tosio Kato and Gustavo Ponce,
-- "Commutator Estimates and the Euler and Navier--Stokes Equations",
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Volker Bach, Thomas Chen, Jurg Frohlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- DASHI CONTRIBUTION
--
-- Package the exact-versus-defective commuting square used throughout the
-- repository:
--
--   observe (fineStep x)
--     = applyResidual (residual x) (coarseStep (observe x)).
--
-- The residual can later be instantiated as a dyadic transport commutator, an
-- RG effective-action remainder, a hidden-path residue, or a coarse biological
-- observation defect.  The type alone supplies no norm estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record DefectControlledSquare : Set₁ where
  constructor defectControlledSquare
  field
    FineState : Set
    CoarseState : Set
    Residual : Set
    observe : FineState → CoarseState
    fineStep : FineState → FineState
    coarseStep : CoarseState → CoarseState
    residual : FineState → Residual
    applyResidual : Residual → CoarseState → CoarseState
    neutralResidual : Residual
    neutralActs :
      (coarse : CoarseState) →
      applyResidual neutralResidual coarse ≡ coarse
    squareWithResidual :
      (fine : FineState) →
      observe (fineStep fine)
      ≡ applyResidual
          (residual fine)
          (coarseStep (observe fine))

open DefectControlledSquare public

ExactSemiconjugacy : DefectControlledSquare → Set
ExactSemiconjugacy square =
  (fine : FineState square) →
  observe square (fineStep square fine)
  ≡ coarseStep square (observe square fine)

neutralResidualImpliesExactAt :
  (square : DefectControlledSquare) →
  (fine : FineState square) →
  residual square fine ≡ neutralResidual square →
  observe square (fineStep square fine)
  ≡ coarseStep square (observe square fine)
neutralResidualImpliesExactAt square fine residualNeutral =
  trans
    (squareWithResidual square fine)
    (trans
      (cong
        (λ selected →
          applyResidual square selected
            (coarseStep square (observe square fine)))
        residualNeutral)
      (neutralActs square
        (coarseStep square (observe square fine))))

allResidualsNeutralImpliesExact :
  (square : DefectControlledSquare) →
  ((fine : FineState square) →
    residual square fine ≡ neutralResidual square) →
  ExactSemiconjugacy square
allResidualsNeutralImpliesExact square residualsNeutral fine =
  neutralResidualImpliesExactAt
    square fine (residualsNeutral fine)

------------------------------------------------------------------------
-- Complete additive rational witness: the hidden coordinate is exactly the
-- defect between evolve-then-observe and observe-then-evolve.
------------------------------------------------------------------------

rationalObserve : ℚ × ℚ → ℚ
rationalObserve = proj₁

rationalFineStep : ℚ × ℚ → ℚ × ℚ
rationalFineStep state =
  (proj₁ state + proj₂ state) , proj₂ state

rationalCoarseStep : ℚ → ℚ
rationalCoarseStep value = value

rationalResidual : ℚ × ℚ → ℚ
rationalResidual = proj₂

rationalApplyResidual : ℚ → ℚ → ℚ
rationalApplyResidual residualValue coarse = coarse + residualValue

rationalNeutralActs :
  (coarse : ℚ) →
  rationalApplyResidual 0ℚ coarse ≡ coarse
rationalNeutralActs coarse = refl

rationalSquareWithResidual :
  (state : ℚ × ℚ) →
  rationalObserve (rationalFineStep state)
  ≡ rationalApplyResidual
      (rationalResidual state)
      (rationalCoarseStep (rationalObserve state))
rationalSquareWithResidual state = refl

canonicalRationalDefectSquare : DefectControlledSquare
canonicalRationalDefectSquare =
  defectControlledSquare
    (ℚ × ℚ)
    ℚ
    ℚ
    rationalObserve
    rationalFineStep
    rationalCoarseStep
    rationalResidual
    rationalApplyResidual
    0ℚ
    rationalNeutralActs
    rationalSquareWithResidual

zeroHiddenCoordinateCommutes :
  (visible : ℚ) →
  observe canonicalRationalDefectSquare
    (fineStep canonicalRationalDefectSquare (visible , 0ℚ))
  ≡ coarseStep canonicalRationalDefectSquare
      (observe canonicalRationalDefectSquare (visible , 0ℚ))
zeroHiddenCoordinateCommutes visible =
  neutralResidualImpliesExactAt
    canonicalRationalDefectSquare
    (visible , 0ℚ)
    refl
