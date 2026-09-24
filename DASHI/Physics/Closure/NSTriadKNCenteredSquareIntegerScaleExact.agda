module DASHI.Physics.Closure.NSTriadKNCenteredSquareIntegerScaleExact where

------------------------------------------------------------------------
-- PERIODIC B / CENTERED SQUARE -> LITERAL INTEGER LATTICE SCALE
--
-- The fixed-output covariance multiplier is
--
--   C_E(p,q) = |p-q|_E^2.
--
-- For an arbitrary additive rational integer embedding E, with
--
--   c = E(1),
--
-- the repository already proves that every Fourier-mode norm square is c^2
-- times the literal natural integer norm square.  This owner applies that
-- theorem to the centered mode p-q and proves the exact same-object identity
--
--   C_E(p,q)
--     = c^2 * natAsRational(modeNatNormSquared(p-q)).
--
-- Consequently a centered-square DIFFERENCE is exactly c^2 times a difference
-- of natural lattice square norms.  No positivity, absolute value, estimate,
-- shell count, or cutoff enters this crosswalk.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate

F : C3.RealField _
F = Rational.rationalRealField

differenceMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
differenceMode p q = Z3.addMode p (Z3.negateMode q)

centeredSquareIsDifferenceModeNorm :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (p q : Z3.FourierMode) →
  Rate.centeredSquare E p q
  ≡ C3.normSquared I (differenceMode p q)
centeredSquareIsDifferenceModeNorm E I
    (Z3.mode px py pz) (Z3.mode qx qy qz)
  rewrite C3.normSquaredMeaning I
            (differenceMode
              (Z3.mode px py pz) (Z3.mode qx qy qz))
        | C3.embedAdd E px (- qx)
        | C3.embedAdd E py (- qy)
        | C3.embedAdd E pz (- qz)
        | C3.embedNegate E qx
        | C3.embedNegate E qy
        | C3.embedNegate E qz =
  solve
    ( C3.embedInteger E px ∷ C3.embedInteger E py
    ∷ C3.embedInteger E pz ∷ C3.embedInteger E qx
    ∷ C3.embedInteger E qy ∷ C3.embedInteger E qz ∷ [])

centeredNatSquare :
  Z3.FourierMode → Z3.FourierMode → ℚ
centeredNatSquare p q =
  Scale.modeNatNormAsRational (differenceMode p q)

centeredSquareIntegerScale :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (p q : Z3.FourierMode) →
  Rate.centeredSquare E p q
  ≡ Scale.unitSquare E * centeredNatSquare p q
centeredSquareIntegerScale E I p q =
  trans
    (centeredSquareIsDifferenceModeNorm E I p q)
    (Scale.modeNormCommonSquareScale E I (differenceMode p q))

centeredSquareDifferenceIntegerScale :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (pa qa pb qb : Z3.FourierMode) →
  Rate.centeredSquare E pa qa - Rate.centeredSquare E pb qb
  ≡
  Scale.unitSquare E
    * (centeredNatSquare pa qa - centeredNatSquare pb qb)
centeredSquareDifferenceIntegerScale E I pa qa pb qb =
  trans
    (cong₂ _-_
      (centeredSquareIntegerScale E I pa qa)
      (centeredSquareIntegerScale E I pb qb))
    (solve
      ( Scale.unitSquare E
      ∷ centeredNatSquare pa qa
      ∷ centeredNatSquare pb qb
      ∷ []))

centeredSquareIntegerScaleClosed : Bool
centeredSquareIntegerScaleClosed = true

centeredSquareDifferenceIntegerScaleClosed : Bool
centeredSquareDifferenceIntegerScaleClosed = true

centeredSquareIntegerCrosswalkUsesCutoff : Bool
centeredSquareIntegerCrosswalkUsesCutoff = false

clayPromotion : Bool
clayPromotion = false
