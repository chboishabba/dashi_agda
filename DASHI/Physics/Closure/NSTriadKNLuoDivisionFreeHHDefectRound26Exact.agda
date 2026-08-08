module DASHI.Physics.Closure.NSTriadKNLuoDivisionFreeHHDefectRound26Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- DASHI CONTRIBUTION
--
-- The HH defect is normalised without introducing a quotient.  Instead of
-- defining d = sqrt(A/Z), the proof stores
--
--   A = d^2 Z,   Z M = D^2,
--
-- and derives A M = d^2 D^2 exactly.  The zero-denominator branch is explicit:
-- Z=0 forces A=0 from the first identity.  No projector or direction field is
-- differentiated and no division by a possibly vanishing quantity occurs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

record DivisionFreeHHDefectFactorisation : Set where
  constructor division-free-hh-defect-factorisation
  field
    defect AScale denominator amplitude dissipation : ℚ

    defectMeaning :
      defect ≡ AScale * AScale * denominator

    amplitudeDissipationMeaning :
      denominator * amplitude ≡ dissipation * dissipation

open DivisionFreeHHDefectFactorisation public

divisionFreeHHProductIdentity :
  (F : DivisionFreeHHDefectFactorisation) →
  defect F * amplitude F
  ≡
  AScale F * AScale F * (dissipation F * dissipation F)
divisionFreeHHProductIdentity F
  rewrite defectMeaning F =
  trans
    (solve
      ( AScale F
      ∷ denominator F
      ∷ amplitude F
      ∷ []))
    (cong
      (λ product → AScale F * AScale F * product)
      (amplitudeDissipationMeaning F))

zeroDenominatorForcesZeroDefect :
  (F : DivisionFreeHHDefectFactorisation) →
  denominator F ≡ 0ℚ →
  defect F ≡ 0ℚ
zeroDenominatorForcesZeroDefect F denominatorZero
  rewrite defectMeaning F
        | denominatorZero =
  solve (AScale F ∷ [])

record HHTransferFactorisation : Set where
  constructor hh-transfer-factorisation
  field
    transfer defectRoot amplitudeRoot remainder : ℚ
    transferMeaning :
      transfer ≡ defectRoot * amplitudeRoot + remainder

open HHTransferFactorisation public

record DivisionFreeHHClosureCell : Set where
  constructor division-free-hh-closure-cell
  field
    defectFactorisation : DivisionFreeHHDefectFactorisation
    transferFactorisation : HHTransferFactorisation

    rootsMatchDefect :
      defectRoot transferFactorisation * defectRoot transferFactorisation
      ≡ defect defectFactorisation

    rootsMatchAmplitude :
      amplitudeRoot transferFactorisation * amplitudeRoot transferFactorisation
      ≡ amplitude defectFactorisation

open DivisionFreeHHClosureCell public

------------------------------------------------------------------------
-- The exact squared product is closed here.  Turning it into the one-sided
-- analytic inequality transfer <= d D + remainder requires nonnegativity and
-- square-root/order lemmas on the selected continuum carrier; that producer
-- remains deliberately separate.
------------------------------------------------------------------------

hhSquaredProductExact :
  (C : DivisionFreeHHClosureCell) →
  (defectRoot (transferFactorisation C)
    * amplitudeRoot (transferFactorisation C))
  *
  (defectRoot (transferFactorisation C)
    * amplitudeRoot (transferFactorisation C))
  ≡
  AScale (defectFactorisation C)
  * AScale (defectFactorisation C)
  *
  (dissipation (defectFactorisation C)
    * dissipation (defectFactorisation C))
hhSquaredProductExact C =
  trans
    (solve
      ( defectRoot (transferFactorisation C)
      ∷ amplitudeRoot (transferFactorisation C)
      ∷ []))
    (trans
      (cong₂ _*_
        (rootsMatchDefect C)
        (rootsMatchAmplitude C))
      (divisionFreeHHProductIdentity (defectFactorisation C)))
