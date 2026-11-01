module DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierInversionFromResolutionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Derive normalized finite Fourier inversion from the character resolution
-- kernel.  For finite point and mode lists, assume
--
--   c sum_k chi(k,y) chi(k,x) = delta(y,x)
--
-- and that the enumerated delta kernel acts as the identity on the signal.
-- Defining
--
--   fhat(k) = c sum_y f(y) chi(k,y),
--
-- the module proves
--
--   sum_k fhat(k) chi(k,x) = f(x).
--
-- Together with FiniteFourierParsevalFromInversionExact this closes inversion
-- and Parseval once the cyclic character resolution is instantiated.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _*_) 
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierParsevalFromInversionExact as Fourier

record FiniteCharacterResolutionData (Point Mode : Set) : Set₁ where
  constructor finite-character-resolution-data
  field
    points : List Point
    modes : List Mode
    normalization : ℚ
    signal : Point → ℚ
    character : Mode → Point → ℚ
    delta : Point → Point → ℚ

    resolutionKernel :
      (left right : Point) →
      normalization
        * Fourier.sumBy modes
            (λ mode → character mode left * character mode right)
      ≡ delta left right

    deltaActsAsIdentity :
      (point : Point) →
      Fourier.sumBy points
        (λ source → signal source * delta source point)
      ≡ signal point

open FiniteCharacterResolutionData public

inversionData :
  ∀ {Point Mode : Set} →
  FiniteCharacterResolutionData Point Mode →
  Fourier.FiniteFourierInversionData Point Mode
inversionData dataSet =
  Fourier.finite-fourier-inversion-data
    (points dataSet)
    (modes dataSet)
    (normalization dataSet)
    (signal dataSet)
    (character dataSet)

finiteFourierInversion :
  ∀ {Point Mode : Set}
    (dataSet : FiniteCharacterResolutionData Point Mode)
    (point : Point) →
  Fourier.sumBy (modes dataSet)
    (λ mode →
      Fourier.coefficient (inversionData dataSet) mode
      * character dataSet mode point)
  ≡ signal dataSet point
finiteFourierInversion dataSet point =
  let
    data = inversionData dataSet

    expandMode :
      (mode : Mode) →
      Fourier.coefficient data mode
        * character dataSet mode point
      ≡ normalization dataSet
        * Fourier.sumBy (points dataSet)
            (λ source →
              signal dataSet source
              * (character dataSet mode source
                * character dataSet mode point))
    expandMode mode =
      let
        distribute =
          Fourier.sumByScaleLeft
            (character dataSet mode point)
            (points dataSet)
            (λ source →
              signal dataSet source * character dataSet mode source)
      in
      trans
        (solve
          ( normalization dataSet
          ∷ Fourier.rawCoefficient data mode
          ∷ character dataSet mode point
          ∷ []))
        (trans
          (cong (normalization dataSet *_)
            (sym distribute))
          (Fourier.sumByCong
            (points dataSet)
            (λ source →
              normalization dataSet
              * (character dataSet mode point
                * (signal dataSet source
                  * character dataSet mode source)))
            (λ source →
              normalization dataSet
              * (signal dataSet source
                * (character dataSet mode source
                  * character dataSet mode point)))
            (λ source →
              solve
                ( normalization dataSet
                ∷ signal dataSet source
                ∷ character dataSet mode source
                ∷ character dataSet mode point
                ∷ []))))

    expandAll =
      Fourier.sumByCong
        (modes dataSet)
        (λ mode →
          Fourier.coefficient data mode
          * character dataSet mode point)
        (λ mode →
          normalization dataSet
          * Fourier.sumBy (points dataSet)
              (λ source →
                signal dataSet source
                * (character dataSet mode source
                  * character dataSet mode point)))
        expandMode

    factorNormalization =
      Fourier.sumByScaleLeft
        (normalization dataSet)
        (modes dataSet)
        (λ mode →
          Fourier.sumBy (points dataSet)
            (λ source →
              signal dataSet source
              * (character dataSet mode source
                * character dataSet mode point)))

    swap =
      Fourier.sumSwap
        (modes dataSet)
        (points dataSet)
        (λ mode source →
          signal dataSet source
          * (character dataSet mode source
            * character dataSet mode point))

    factorSignal :
      (source : Point) →
      Fourier.sumBy (modes dataSet)
        (λ mode →
          signal dataSet source
          * (character dataSet mode source
            * character dataSet mode point))
      ≡ signal dataSet source
        * Fourier.sumBy (modes dataSet)
            (λ mode →
              character dataSet mode source
              * character dataSet mode point)
    factorSignal source =
      Fourier.sumByScaleLeft
        (signal dataSet source)
        (modes dataSet)
        (λ mode →
          character dataSet mode source
          * character dataSet mode point)

    factorEachSignal =
      Fourier.sumByCong
        (points dataSet)
        (λ source →
          Fourier.sumBy (modes dataSet)
            (λ mode →
              signal dataSet source
              * (character dataSet mode source
                * character dataSet mode point)))
        (λ source →
          signal dataSet source
          * Fourier.sumBy (modes dataSet)
              (λ mode →
                character dataSet mode source
                * character dataSet mode point))
        factorSignal

    distributeNormalization :
      normalization dataSet
        * Fourier.sumBy (points dataSet)
            (λ source →
              signal dataSet source
              * Fourier.sumBy (modes dataSet)
                  (λ mode →
                    character dataSet mode source
                    * character dataSet mode point))
      ≡ Fourier.sumBy (points dataSet)
          (λ source →
            signal dataSet source
            * (normalization dataSet
              * Fourier.sumBy (modes dataSet)
                  (λ mode →
                    character dataSet mode source
                    * character dataSet mode point)))
    distributeNormalization =
      trans
        (sym
          (Fourier.sumByScaleLeft
            (normalization dataSet)
            (points dataSet)
            (λ source →
              signal dataSet source
              * Fourier.sumBy (modes dataSet)
                  (λ mode →
                    character dataSet mode source
                    * character dataSet mode point))))
        (Fourier.sumByCong
          (points dataSet)
          (λ source →
            normalization dataSet
            * (signal dataSet source
              * Fourier.sumBy (modes dataSet)
                  (λ mode →
                    character dataSet mode source
                    * character dataSet mode point)))
          (λ source →
            signal dataSet source
            * (normalization dataSet
              * Fourier.sumBy (modes dataSet)
                  (λ mode →
                    character dataSet mode source
                    * character dataSet mode point)))
          (λ source →
            solve
              ( normalization dataSet
              ∷ signal dataSet source
              ∷ Fourier.sumBy (modes dataSet)
                  (λ mode →
                    character dataSet mode source
                    * character dataSet mode point)
              ∷ [])))

    applyResolution =
      Fourier.sumByCong
        (points dataSet)
        (λ source →
          signal dataSet source
          * (normalization dataSet
            * Fourier.sumBy (modes dataSet)
                (λ mode →
                  character dataSet mode source
                  * character dataSet mode point)))
        (λ source → signal dataSet source * delta dataSet source point)
        (λ source →
          cong (signal dataSet source *_)
            (resolutionKernel dataSet source point))
  in
  trans expandAll
    (trans factorNormalization
      (trans
        (cong (normalization dataSet *_) swap)
        (trans
          (cong (normalization dataSet *_) factorEachSignal)
          (trans distributeNormalization
            (trans applyResolution
              (deltaActsAsIdentity dataSet point))))))

completeFourierData :
  ∀ {Point Mode : Set} →
  FiniteCharacterResolutionData Point Mode →
  Fourier.CompleteFiniteFourierData Point Mode
completeFourierData dataSet =
  Fourier.complete-finite-fourier-data
    (inversionData dataSet)
    (finiteFourierInversion dataSet)

finiteFourierParsevalFromResolution :
  ∀ {Point Mode : Set}
    (dataSet : FiniteCharacterResolutionData Point Mode) →
  Fourier.fourierL2Squared (completeFourierData dataSet)
  ≡ Fourier.physicalL2Squared (completeFourierData dataSet)
finiteFourierParsevalFromResolution dataSet =
  Fourier.finiteParsevalFromInversion (completeFourierData dataSet)
