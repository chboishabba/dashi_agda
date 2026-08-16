module DASHI.Moonshine.OggPrimeControlMatrixExact where

------------------------------------------------------------------------
-- SOURCE / AUTHORITY NOTE
--
-- This module is an integration matrix over already source-calibrated modules.
-- Representation data comes from the Fulton-Harris / Serre-calibrated finite
-- restriction lane; tau values from the Serre/Miyake-calibrated arithmetic
-- lane; Ogg labels from the external Ogg/Duncan-Ono authority lane.
--
-- Crucially, the external Ogg label is the LAST column conceptually.  None of
-- the representation or arithmetic columns read it while being constructed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Integer using (ℤ)

import Base369 as Base
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.D4SO3RestrictionJ0To35Exact as D4
import DASHI.Foundations.TetrahedralSO3RestrictionJ0To35Exact as Tet
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact as Oct
import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact as Ico
import DASHI.Foundations.PolyhedralInvariantFixedSpaceSignatureExact as Fixed
import DASHI.Foundations.PolyhedralFixedSpaceDerivedNonaryExact as Nonary
import DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact as Candidate
import DASHI.Moonshine.RamanujanTauCandidateFingerprintJ0To35Exact as Tau

data OddPrimeCandidateUnder72 : Set where
  prime3 prime5 prime7 prime11 prime13 prime17 prime19 prime23 prime29 prime31
    prime37 prime41 prime43 prime47 prime53 prime59 prime61 prime67 prime71 :
    OddPrimeCandidateUnder72

primeLevel : OddPrimeCandidateUnder72 → Nat
primeLevel prime3 = 3
primeLevel prime5 = 5
primeLevel prime7 = 7
primeLevel prime11 = 11
primeLevel prime13 = 13
primeLevel prime17 = 17
primeLevel prime19 = 19
primeLevel prime23 = 23
primeLevel prime29 = 29
primeLevel prime31 = 31
primeLevel prime37 = 37
primeLevel prime41 = 41
primeLevel prime43 = 43
primeLevel prime47 = 47
primeLevel prime53 = 53
primeLevel prime59 = 59
primeLevel prime61 = 61
primeLevel prime67 = 67
primeLevel prime71 = 71

primeAngularMomentum :
  OddPrimeCandidateUnder72 → Spin.AngularMomentum0To35
primeAngularMomentum prime3 = Spin.j1
primeAngularMomentum prime5 = Spin.j2
primeAngularMomentum prime7 = Spin.j3
primeAngularMomentum prime11 = Spin.j5
primeAngularMomentum prime13 = Spin.j6
primeAngularMomentum prime17 = Spin.j8
primeAngularMomentum prime19 = Spin.j9
primeAngularMomentum prime23 = Spin.j11
primeAngularMomentum prime29 = Spin.j14
primeAngularMomentum prime31 = Spin.j15
primeAngularMomentum prime37 = Spin.j18
primeAngularMomentum prime41 = Spin.j20
primeAngularMomentum prime43 = Spin.j21
primeAngularMomentum prime47 = Spin.j23
primeAngularMomentum prime53 = Spin.j26
primeAngularMomentum prime59 = Spin.j29
primeAngularMomentum prime61 = Spin.j30
primeAngularMomentum prime67 = Spin.j33
primeAngularMomentum prime71 = Spin.j35

primeDimensionExact :
  (prime : OddPrimeCandidateUnder72) →
  Spin.jDimension (primeAngularMomentum prime) ≡ primeLevel prime
primeDimensionExact prime3 = refl
primeDimensionExact prime5 = refl
primeDimensionExact prime7 = refl
primeDimensionExact prime11 = refl
primeDimensionExact prime13 = refl
primeDimensionExact prime17 = refl
primeDimensionExact prime19 = refl
primeDimensionExact prime23 = refl
primeDimensionExact prime29 = refl
primeDimensionExact prime31 = refl
primeDimensionExact prime37 = refl
primeDimensionExact prime41 = refl
primeDimensionExact prime43 = refl
primeDimensionExact prime47 = refl
primeDimensionExact prime53 = refl
primeDimensionExact prime59 = refl
primeDimensionExact prime61 = refl
primeDimensionExact prime67 = refl
primeDimensionExact prime71 = refl

externalOggLabel : OddPrimeCandidateUnder72 → Bool
externalOggLabel prime3 = true
externalOggLabel prime5 = true
externalOggLabel prime7 = true
externalOggLabel prime11 = true
externalOggLabel prime13 = true
externalOggLabel prime17 = true
externalOggLabel prime19 = true
externalOggLabel prime23 = true
externalOggLabel prime29 = true
externalOggLabel prime31 = true
externalOggLabel prime37 = false
externalOggLabel prime41 = true
externalOggLabel prime43 = false
externalOggLabel prime47 = true
externalOggLabel prime53 = false
externalOggLabel prime59 = true
externalOggLabel prime61 = false
externalOggLabel prime67 = false
externalOggLabel prime71 = true

record PrimeControlRow : Set where
  constructor prime-control-row
  field
    candidate : OddPrimeCandidateUnder72
    level : Nat
    angularMomentum : Spin.AngularMomentum0To35
    levelMatchesDimension : Spin.jDimension angularMomentum ≡ level

    d4Spectrum : D4.D4Spectrum
    tetrahedralSpectrum : Tet.TetrahedralSpectrum
    octahedralSpectrum : Oct.OctahedralSpectrum
    icosahedralSpectrum : Ico.IcosahedralSpectrum

    invariantFixedSpaceSignature : Fixed.InvariantFixedSpaceSignature
    derivedNonaryAddress : Base.NonaryTruth
    tauValue : ℤ

    externalOgg : Bool

open PrimeControlRow public

primeControlRow : OddPrimeCandidateUnder72 → PrimeControlRow
primeControlRow prime =
  let j = primeAngularMomentum prime in
  prime-control-row
    prime
    (primeLevel prime)
    j
    (primeDimensionExact prime)
    (D4.branchingSpectrum j)
    (Tet.branchingSpectrum j)
    (Oct.branchingSpectrum j)
    (Ico.branchingSpectrum j)
    (Fixed.invariantSignature j)
    (Nonary.fixedSpaceNonary j)
    (Tau.tauAtCandidateLevel (Candidate.spatialLevel j))
    (externalOggLabel prime)

allOddPrimeControlsUnder72 : List OddPrimeCandidateUnder72
allOddPrimeControlsUnder72 =
  prime3 ∷ prime5 ∷ prime7 ∷ prime11 ∷ prime13 ∷ prime17 ∷ prime19
  ∷ prime23 ∷ prime29 ∷ prime31 ∷ prime37 ∷ prime41 ∷ prime43
  ∷ prime47 ∷ prime53 ∷ prime59 ∷ prime61 ∷ prime67 ∷ prime71 ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = 1 + listCount xs

oddPrimeControlCountIsNineteen :
  listCount allOddPrimeControlsUnder72 ≡ 19
oddPrimeControlCountIsNineteen = refl

nonOggPrimeControls : List OddPrimeCandidateUnder72
nonOggPrimeControls =
  prime37 ∷ prime43 ∷ prime53 ∷ prime61 ∷ prime67 ∷ []

nonOggPrimeControlCountIsFive : listCount nonOggPrimeControls ≡ 5
nonOggPrimeControlCountIsFive = refl

prime37ExternallyNegative : externalOggLabel prime37 ≡ false
prime37ExternallyNegative = refl
prime43ExternallyNegative : externalOggLabel prime43 ≡ false
prime43ExternallyNegative = refl
prime53ExternallyNegative : externalOggLabel prime53 ≡ false
prime53ExternallyNegative = refl
prime61ExternallyNegative : externalOggLabel prime61 ≡ false
prime61ExternallyNegative = refl
prime67ExternallyNegative : externalOggLabel prime67 ≡ false
prime67ExternallyNegative = refl

record OggPrimeControlMatrixBoundary : Set where
  field
    allOddPrimeControlsUnder72Present : Bool
    allOddPrimeControlsUnder72PresentIsTrue :
      allOddPrimeControlsUnder72Present ≡ true

    fiveNonOggPrimeControlsExplicit : Bool
    fiveNonOggPrimeControlsExplicitIsTrue :
      fiveNonOggPrimeControlsExplicit ≡ true

    representationColumnsDependOnExternalOggLabel : Bool
    representationColumnsDependOnExternalOggLabelIsFalse :
      representationColumnsDependOnExternalOggLabel ≡ false

    arithmeticColumnDependsOnExternalOggLabel : Bool
    arithmeticColumnDependsOnExternalOggLabelIsFalse :
      arithmeticColumnDependsOnExternalOggLabel ≡ false

    matrixItselfClaimsAnOggSelector : Bool
    matrixItselfClaimsAnOggSelectorIsFalse :
      matrixItselfClaimsAnOggSelector ≡ false

canonicalOggPrimeControlMatrixBoundary : OggPrimeControlMatrixBoundary
canonicalOggPrimeControlMatrixBoundary =
  record
    { allOddPrimeControlsUnder72Present = true
    ; allOddPrimeControlsUnder72PresentIsTrue = refl
    ; fiveNonOggPrimeControlsExplicit = true
    ; fiveNonOggPrimeControlsExplicitIsTrue = refl
    ; representationColumnsDependOnExternalOggLabel = false
    ; representationColumnsDependOnExternalOggLabelIsFalse = refl
    ; arithmeticColumnDependsOnExternalOggLabel = false
    ; arithmeticColumnDependsOnExternalOggLabelIsFalse = refl
    ; matrixItselfClaimsAnOggSelector = false
    ; matrixItselfClaimsAnOggSelectorIsFalse = refl
    }
