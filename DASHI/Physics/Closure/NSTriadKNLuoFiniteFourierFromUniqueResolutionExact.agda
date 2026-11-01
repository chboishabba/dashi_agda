module DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierFromUniqueResolutionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Remove the delta-action producer from the finite Fourier carrier.  A unique
-- enumeration of every target point makes the Kronecker kernel act as the
-- identity. Consequently a normalized character resolution kernel alone
-- constructs inversion and Parseval.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _*_)
open import Relation.Nullary using (Dec)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteKroneckerEnumerationExact as Delta
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierInversionFromResolutionExact as Inversion
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierParsevalFromInversionExact as Fourier

record FiniteUniqueCharacterResolutionData (Point Mode : Set) : Set₁ where
  constructor finite-unique-character-resolution-data
  field
    points : List Point
    modes : List Mode
    normalization : ℚ
    signal : Point → ℚ
    character : Mode → Point → ℚ
    decidePointEquality :
      (left right : Point) → Dec (left ≡ right)
    pointOccursExactlyOnce :
      (point : Point) → Delta.UniqueOccurrence point points

    resolutionKernel :
      (left right : Point) →
      normalization
        * Fourier.sumBy modes
            (λ mode → character mode left * character mode right)
      ≡ Delta.kronecker decidePointEquality left right

open FiniteUniqueCharacterResolutionData public

resolutionData :
  ∀ {Point Mode : Set} →
  FiniteUniqueCharacterResolutionData Point Mode →
  Inversion.FiniteCharacterResolutionData Point Mode
resolutionData dataSet =
  Inversion.finite-character-resolution-data
    (points dataSet)
    (modes dataSet)
    (normalization dataSet)
    (signal dataSet)
    (character dataSet)
    (Delta.kronecker (decidePointEquality dataSet))
    (resolutionKernel dataSet)
    (λ point →
      Delta.kroneckerActsAsIdentity
        (decidePointEquality dataSet)
        point
        (points dataSet)
        (pointOccursExactlyOnce dataSet point)
        (signal dataSet))

finiteUniqueFourierInversion :
  ∀ {Point Mode : Set}
    (dataSet : FiniteUniqueCharacterResolutionData Point Mode)
    (point : Point) →
  Fourier.sumBy (modes dataSet)
    (λ mode →
      Fourier.coefficient
        (Inversion.inversionData (resolutionData dataSet)) mode
      * character dataSet mode point)
  ≡ signal dataSet point
finiteUniqueFourierInversion dataSet =
  Inversion.finiteFourierInversion (resolutionData dataSet)

finiteUniqueFourierParseval :
  ∀ {Point Mode : Set}
    (dataSet : FiniteUniqueCharacterResolutionData Point Mode) →
  Fourier.fourierL2Squared
    (Inversion.completeFourierData (resolutionData dataSet))
  ≡ Fourier.physicalL2Squared
    (Inversion.completeFourierData (resolutionData dataSet))
finiteUniqueFourierParseval dataSet =
  Inversion.finiteFourierParsevalFromResolution
    (resolutionData dataSet)
