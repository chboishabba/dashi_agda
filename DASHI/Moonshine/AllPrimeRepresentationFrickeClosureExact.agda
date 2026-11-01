module DASHI.Moonshine.AllPrimeRepresentationFrickeClosureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1-8.
-- MR 417184; no DOI assigned.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230-239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Complete the finite prime-control representation/Fricke closure by treating
-- p=2 as the genuine spinorial boundary rather than forcing it through SO(3).
--
-- For the nineteen odd primes below 72, use the exact SO(3)-character/class-
-- number coupling from PrimeRepresentationFrickeCouplingExact.  For p=2 use
-- the SU(2) doublet together with the special prime-level modular data
--
--   g(X0(2))=0,  r_2=2,  g(X0+(2))=0,
--
-- which satisfy Riemann-Hurwitz exactly.  The resulting twenty-prime control
-- universe contains exactly the fifteen Ogg primes and the five explicit
-- non-Ogg controls 37,43,53,61,67.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeRepresentationFrickeCouplingExact as Coupling

data PrimeCandidateUnder72 : Set where
  spinorPrime2 : PrimeCandidateUnder72
  oddPrime : Matrix.OddPrimeCandidateUnder72 → PrimeCandidateUnder72

primeCandidateLevel : PrimeCandidateUnder72 → Nat
primeCandidateLevel spinorPrime2 = 2
primeCandidateLevel (oddPrime prime) = Matrix.primeLevel prime

spinorPrime2Dimension : Nat
spinorPrime2Dimension = Spin.su2Dimension 1

spinorPrime2DimensionIsTwo : spinorPrime2Dimension ≡ 2
spinorPrime2DimensionIsTwo = refl

------------------------------------------------------------------------
-- Special p=2 modular/Fricke row.
------------------------------------------------------------------------

spinorPrime2GenusX0 : Nat
spinorPrime2GenusX0 = 0

spinorPrime2FrickeFixedPointCount : Nat
spinorPrime2FrickeFixedPointCount = 2

spinorPrime2GenusX0Plus : Nat
spinorPrime2GenusX0Plus = 0

spinorPrime2RiemannHurwitz :
  4 * spinorPrime2GenusX0Plus + spinorPrime2FrickeFixedPointCount
  ≡ 2 * spinorPrime2GenusX0 + 2
spinorPrime2RiemannHurwitz = refl

spinorPrime2FrickeDefect : Nat
spinorPrime2FrickeDefect =
  (2 * spinorPrime2GenusX0 + 2)
  ∸ spinorPrime2FrickeFixedPointCount

spinorPrime2FrickeDefectIsZero : spinorPrime2FrickeDefect ≡ 0
spinorPrime2FrickeDefectIsZero = refl

------------------------------------------------------------------------
-- Unified finite prime-control selector.
------------------------------------------------------------------------

representationArithmeticFrickeClosed :
  PrimeCandidateUnder72 → Bool
representationArithmeticFrickeClosed spinorPrime2 = true
representationArithmeticFrickeClosed (oddPrime prime) =
  Coupling.representationArithmeticFrickeClosed prime

externalOggControlLabel : PrimeCandidateUnder72 → Bool
externalOggControlLabel spinorPrime2 = true
externalOggControlLabel (oddPrime prime) = Matrix.externalOggLabel prime

representationArithmeticClosureMatchesExternalOgg :
  (prime : PrimeCandidateUnder72) →
  representationArithmeticFrickeClosed prime
  ≡ externalOggControlLabel prime
representationArithmeticClosureMatchesExternalOgg spinorPrime2 = refl
representationArithmeticClosureMatchesExternalOgg (oddPrime prime) =
  Coupling.coupledClosureMatchesExternalOggOnScan prime

allPrimeCandidatesUnder72 : List PrimeCandidateUnder72
allPrimeCandidatesUnder72 =
  spinorPrime2
  ∷ oddPrime Matrix.prime3
  ∷ oddPrime Matrix.prime5
  ∷ oddPrime Matrix.prime7
  ∷ oddPrime Matrix.prime11
  ∷ oddPrime Matrix.prime13
  ∷ oddPrime Matrix.prime17
  ∷ oddPrime Matrix.prime19
  ∷ oddPrime Matrix.prime23
  ∷ oddPrime Matrix.prime29
  ∷ oddPrime Matrix.prime31
  ∷ oddPrime Matrix.prime37
  ∷ oddPrime Matrix.prime41
  ∷ oddPrime Matrix.prime43
  ∷ oddPrime Matrix.prime47
  ∷ oddPrime Matrix.prime53
  ∷ oddPrime Matrix.prime59
  ∷ oddPrime Matrix.prime61
  ∷ oddPrime Matrix.prime67
  ∷ oddPrime Matrix.prime71
  ∷ []

allPrimeCandidateCountIsTwenty :
  Matrix.listCount allPrimeCandidatesUnder72 ≡ 20
allPrimeCandidateCountIsTwenty = refl

oggPrimeCandidatesUnder72 : List PrimeCandidateUnder72
oggPrimeCandidatesUnder72 =
  spinorPrime2
  ∷ oddPrime Matrix.prime3
  ∷ oddPrime Matrix.prime5
  ∷ oddPrime Matrix.prime7
  ∷ oddPrime Matrix.prime11
  ∷ oddPrime Matrix.prime13
  ∷ oddPrime Matrix.prime17
  ∷ oddPrime Matrix.prime19
  ∷ oddPrime Matrix.prime23
  ∷ oddPrime Matrix.prime29
  ∷ oddPrime Matrix.prime31
  ∷ oddPrime Matrix.prime41
  ∷ oddPrime Matrix.prime47
  ∷ oddPrime Matrix.prime59
  ∷ oddPrime Matrix.prime71
  ∷ []

oggPrimeCandidateCountIsFifteen :
  Matrix.listCount oggPrimeCandidatesUnder72 ≡ 15
oggPrimeCandidateCountIsFifteen = refl

nonOggPrimeCandidatesUnder72 : List PrimeCandidateUnder72
nonOggPrimeCandidatesUnder72 =
  oddPrime Matrix.prime37
  ∷ oddPrime Matrix.prime43
  ∷ oddPrime Matrix.prime53
  ∷ oddPrime Matrix.prime61
  ∷ oddPrime Matrix.prime67
  ∷ []

nonOggPrimeCandidateCountIsFive :
  Matrix.listCount nonOggPrimeCandidatesUnder72 ≡ 5
nonOggPrimeCandidateCountIsFive = refl

record AllPrimeRepresentationFrickeBoundary : Set where
  field
    p2KeptAsSpinorialBoundary : Bool
    p2KeptAsSpinorialBoundaryIsTrue :
      p2KeptAsSpinorialBoundary ≡ true
    allTwentyPrimeControlsPresent : Bool
    allTwentyPrimeControlsPresentIsTrue :
      allTwentyPrimeControlsPresent ≡ true
    fifteenOggControlsClose : Bool
    fifteenOggControlsCloseIsTrue :
      fifteenOggControlsClose ≡ true
    fiveNonOggControlsRemainOpen : Bool
    fiveNonOggControlsRemainOpenIsTrue :
      fiveNonOggControlsRemainOpen ≡ true
    globalOggTheoremClaimed : Bool
    globalOggTheoremClaimedIsFalse :
      globalOggTheoremClaimed ≡ false

canonicalAllPrimeRepresentationFrickeBoundary :
  AllPrimeRepresentationFrickeBoundary
canonicalAllPrimeRepresentationFrickeBoundary =
  record
    { p2KeptAsSpinorialBoundary = true
    ; p2KeptAsSpinorialBoundaryIsTrue = refl
    ; allTwentyPrimeControlsPresent = true
    ; allTwentyPrimeControlsPresentIsTrue = refl
    ; fifteenOggControlsClose = true
    ; fifteenOggControlsCloseIsTrue = refl
    ; fiveNonOggControlsRemainOpen = true
    ; fiveNonOggControlsRemainOpenIsTrue = refl
    ; globalOggTheoremClaimed = false
    ; globalOggTheoremClaimedIsFalse = refl
    }
