module DASHI.Physics.Closure.NSTriadKNRealityInvolutionEquivarianceRound27Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Treat Fourier reality as the fixed-point condition of the involution
--
--   J u (k) = conjugate (u (-k)).
--
-- We prove J^2=id pointwise, prove the generic theorem that an equivariant
-- extensional vector field preserves the fixed-point carrier, and instantiate
-- equivariance for every diagonal Complex3 multiplier whose symbol obeys the
-- correct reality law.  This closes the involution algebra used by viscosity,
-- shell and Leray multipliers.  Equivariance of the complete nonlinear
-- convolution vector field remains a separate physical producer.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling

ModeState : ∀ {r} (F : C3.RealField r) → Set r
ModeState F = Z3.FourierMode → C3.Complex3 F

StateAgreement :
  ∀ {r} {F : C3.RealField r} →
  ModeState F → ModeState F → Set r
StateAgreement left right = ∀ mode → left mode ≡ right mode

agreementRefl :
  ∀ {r} {F : C3.RealField r} (state : ModeState F) →
  StateAgreement state state
agreementRefl state mode = refl

agreementSym :
  ∀ {r} {F : C3.RealField r} {left right : ModeState F} →
  StateAgreement left right → StateAgreement right left
agreementSym proof mode = sym (proof mode)

agreementTrans :
  ∀ {r} {F : C3.RealField r}
    {first second third : ModeState F} →
  StateAgreement first second →
  StateAgreement second third →
  StateAgreement first third
agreementTrans first second mode = trans (first mode) (second mode)

realityInvolution :
  ∀ {r} {F : C3.RealField r} →
  ModeState F → ModeState F
realityInvolution state mode =
  C3.complex3Conjugate (state (Z3.negateMode mode))

realityInvolutionInvolutive :
  ∀ {r} {F : C3.RealField r} (state : ModeState F) →
  StateAgreement (realityInvolution (realityInvolution state)) state
realityInvolutionInvolutive state mode
  rewrite Symmetry.negateModeInvolutive mode
        | C3.complex3ConjugateInvolutive (state mode) = refl

RealityFixed :
  ∀ {r} {F : C3.RealField r} → ModeState F → Set r
RealityFixed state = StateAgreement (realityInvolution state) state

fourierRealityGivesFixedPoint :
  ∀ {r} {F : C3.RealField r} (state : ModeState F) →
  (∀ mode →
    state (Z3.negateMode mode)
    ≡ C3.complex3Conjugate (state mode)) →
  RealityFixed state
fourierRealityGivesFixedPoint state reality mode =
  trans
    (cong C3.complex3Conjugate (reality mode))
    (C3.complex3ConjugateInvolutive (state mode))

fixedPointGivesFourierReality :
  ∀ {r} {F : C3.RealField r} (state : ModeState F) →
  RealityFixed state →
  ∀ mode →
  state (Z3.negateMode mode)
  ≡ C3.complex3Conjugate (state mode)
fixedPointGivesFourierReality state fixed mode =
  sym
    (trans
      (sym
        (cong C3.complex3Conjugate
          (cong state (Symmetry.negateModeInvolutive mode))))
      (fixed (Z3.negateMode mode)))

record RealityEquivariantVectorField
    {r : Level} (F : C3.RealField r) : Set (lsuc r) where
  field
    vectorField : ModeState F → ModeState F

    vectorFieldCongruent :
      ∀ {left right} →
      StateAgreement left right →
      StateAgreement (vectorField left) (vectorField right)

    vectorFieldEquivariant :
      ∀ state →
      StateAgreement
        (vectorField (realityInvolution state))
        (realityInvolution (vectorField state))

open RealityEquivariantVectorField public

equivariantVectorFieldPreservesReality :
  ∀ {r} {F : C3.RealField r} →
  (field : RealityEquivariantVectorField F) →
  (state : ModeState F) →
  RealityFixed state →
  RealityFixed (vectorField field state)
equivariantVectorFieldPreservesReality field state fixed =
  agreementTrans
    (agreementSym (vectorFieldEquivariant field state))
    (vectorFieldCongruent field fixed)

------------------------------------------------------------------------
-- Concrete diagonal-multiplier equivariance.
------------------------------------------------------------------------

record RealityDiagonalSymbol
    {r : Level} (F : C3.RealField r) : Set (lsuc r) where
  field
    symbol : Z3.FourierMode → C3.Complex F
    symbolReality : ∀ mode →
      symbol (Z3.negateMode mode)
      ≡ C3.complexConjugate (symbol mode)

open RealityDiagonalSymbol public

diagonalField :
  ∀ {r} {F : C3.RealField r} →
  RealityDiagonalSymbol F → ModeState F → ModeState F
diagonalField diagonal state mode =
  C3.complex3Scale (symbol diagonal mode) (state mode)

symbolAtModeIsConjugateAtNegative :
  ∀ {r} {F : C3.RealField r}
    (diagonal : RealityDiagonalSymbol F) mode →
  symbol diagonal mode
  ≡ C3.complexConjugate (symbol diagonal (Z3.negateMode mode))
symbolAtModeIsConjugateAtNegative diagonal mode =
  trans
    (sym
      (cong (symbol diagonal)
        (Symmetry.negateModeInvolutive mode)))
    (symbolReality diagonal (Z3.negateMode mode))

diagonalFieldCongruent :
  ∀ {r} {F : C3.RealField r}
    (diagonal : RealityDiagonalSymbol F) →
  ∀ {left right} →
  StateAgreement left right →
  StateAgreement
    (diagonalField diagonal left)
    (diagonalField diagonal right)
diagonalFieldCongruent diagonal agreement mode =
  cong (C3.complex3Scale (symbol diagonal mode)) (agreement mode)

diagonalFieldEquivariant :
  ∀ {r} {F : C3.RealField r}
    (diagonal : RealityDiagonalSymbol F) →
  ∀ state →
  StateAgreement
    (diagonalField diagonal (realityInvolution state))
    (realityInvolution (diagonalField diagonal state))
diagonalFieldEquivariant diagonal state mode =
  trans
    (cong
      (λ scalar →
        C3.complex3Scale scalar
          (C3.complex3Conjugate
            (state (Z3.negateMode mode))))
      (symbolAtModeIsConjugateAtNegative diagonal mode))
    (sym
      (Scaling.complex3ConjugateScale
        (symbol diagonal (Z3.negateMode mode))
        (state (Z3.negateMode mode))))

canonicalDiagonalRealityEquivariantVectorField :
  ∀ {r} {F : C3.RealField r} →
  RealityDiagonalSymbol F → RealityEquivariantVectorField F
canonicalDiagonalRealityEquivariantVectorField diagonal = record
  { vectorField = diagonalField diagonal
  ; vectorFieldCongruent = diagonalFieldCongruent diagonal
  ; vectorFieldEquivariant = diagonalFieldEquivariant diagonal
  }

realityInvolutionAlgebraClosed : Bool
realityInvolutionAlgebraClosed = true

diagonalMultiplierEquivarianceClosed : Bool
diagonalMultiplierEquivarianceClosed = true

fullPhysicalGalerkinVectorFieldEquivarianceClosed : Bool
fullPhysicalGalerkinVectorFieldEquivarianceClosed = false
