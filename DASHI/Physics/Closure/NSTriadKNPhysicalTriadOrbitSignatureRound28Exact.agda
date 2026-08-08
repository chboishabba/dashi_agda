module DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitSignatureRound28Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hermann Grassmann.
-- Title: "Die lineale Ausdehnungslehre" (1844).
-- DOI: not applicable; historical source.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Make the finite swap/conjugation symmetry orbit explicit.  Squared Plucker
-- area is invariant under all four orbit actions, while each oriented Plucker
-- coordinate transforms by the exact parity character: swap reverses
-- orientation, simultaneous conjugation preserves it, and swap-after-
-- conjugation reverses it.  This separates true invariants from signed
-- pseudoinvariants before finite certificate reduction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact as Plucker
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadConjugationOrbitRound28Exact as Conjugation

data TriadOrbitAction : Set where
  identity swap conjugate swapConjugate : TriadOrbitAction

act :
  TriadOrbitAction →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence
act identity triad = triad
act swap triad = Symmetry.swapTriad triad
act conjugate triad = Symmetry.conjugateTriad triad
act swapConjugate triad =
  Symmetry.swapTriad (Symmetry.conjugateTriad triad)

data OrientationParity : Set where
  preserves reverses : OrientationParity

orientationParity : TriadOrbitAction → OrientationParity
orientationParity identity = preserves
orientationParity swap = reverses
orientationParity conjugate = preserves
orientationParity swapConjugate = reverses

applyParity : OrientationParity → ℤ → ℤ
applyParity preserves value = value
applyParity reverses value = - value

orbitPluckerXSignature :
  (action : TriadOrbitAction) →
  (triad : Physical.PhysicalTriadIncidence) →
  Plucker.pluckerX
    (Physical.p (act action triad))
    (Physical.q (act action triad))
  ≡
  applyParity (orientationParity action)
    (Plucker.pluckerX (Physical.p triad) (Physical.q triad))
orbitPluckerXSignature identity triad = refl
orbitPluckerXSignature swap triad =
  Plucker.pluckerSwapX (Physical.p triad) (Physical.q triad)
orbitPluckerXSignature conjugate triad =
  Conjugation.pluckerConjugateX
    (Physical.p triad) (Physical.q triad)
orbitPluckerXSignature swapConjugate triad =
  trans
    (Plucker.pluckerSwapX
      (Physical.p (Symmetry.conjugateTriad triad))
      (Physical.q (Symmetry.conjugateTriad triad)))
    (cong -_
      (Conjugation.pluckerConjugateX
        (Physical.p triad) (Physical.q triad)))

orbitPluckerYSignature :
  (action : TriadOrbitAction) →
  (triad : Physical.PhysicalTriadIncidence) →
  Plucker.pluckerY
    (Physical.p (act action triad))
    (Physical.q (act action triad))
  ≡
  applyParity (orientationParity action)
    (Plucker.pluckerY (Physical.p triad) (Physical.q triad))
orbitPluckerYSignature identity triad = refl
orbitPluckerYSignature swap triad =
  Plucker.pluckerSwapY (Physical.p triad) (Physical.q triad)
orbitPluckerYSignature conjugate triad =
  Conjugation.pluckerConjugateY
    (Physical.p triad) (Physical.q triad)
orbitPluckerYSignature swapConjugate triad =
  trans
    (Plucker.pluckerSwapY
      (Physical.p (Symmetry.conjugateTriad triad))
      (Physical.q (Symmetry.conjugateTriad triad)))
    (cong -_
      (Conjugation.pluckerConjugateY
        (Physical.p triad) (Physical.q triad)))

orbitPluckerZSignature :
  (action : TriadOrbitAction) →
  (triad : Physical.PhysicalTriadIncidence) →
  Plucker.pluckerZ
    (Physical.p (act action triad))
    (Physical.q (act action triad))
  ≡
  applyParity (orientationParity action)
    (Plucker.pluckerZ (Physical.p triad) (Physical.q triad))
orbitPluckerZSignature identity triad = refl
orbitPluckerZSignature swap triad =
  Plucker.pluckerSwapZ (Physical.p triad) (Physical.q triad)
orbitPluckerZSignature conjugate triad =
  Conjugation.pluckerConjugateZ
    (Physical.p triad) (Physical.q triad)
orbitPluckerZSignature swapConjugate triad =
  trans
    (Plucker.pluckerSwapZ
      (Physical.p (Symmetry.conjugateTriad triad))
      (Physical.q (Symmetry.conjugateTriad triad)))
    (cong -_
      (Conjugation.pluckerConjugateZ
        (Physical.p triad) (Physical.q triad)))

orbitSquaredAreaInvariant :
  (action : TriadOrbitAction) →
  (triad : Physical.PhysicalTriadIncidence) →
  Plucker.pluckerNormSquared
    (Physical.p (act action triad))
    (Physical.q (act action triad))
  ≡
  Plucker.pluckerNormSquared
    (Physical.p triad) (Physical.q triad)
orbitSquaredAreaInvariant identity triad = refl
orbitSquaredAreaInvariant swap triad =
  Plucker.pluckerSwapPreservesSquaredArea
    (Physical.p triad) (Physical.q triad)
orbitSquaredAreaInvariant conjugate triad =
  Conjugation.physicalTriadConjugationPreservesSquaredArea triad
orbitSquaredAreaInvariant swapConjugate triad =
  trans
    (Plucker.pluckerSwapPreservesSquaredArea
      (Physical.p (Symmetry.conjugateTriad triad))
      (Physical.q (Symmetry.conjugateTriad triad)))
    (Conjugation.physicalTriadConjugationPreservesSquaredArea triad)

physicalTriadOrbitSignatureClosed : Bool
physicalTriadOrbitSignatureClosed = true

orientationCharacterClosed : Bool
orientationCharacterClosed = true

orbitRepresentativeCertificateReductionImplemented : Bool
orbitRepresentativeCertificateReductionImplemented = false

physicalTriadOrbitSignatureClosedIsTrue :
  physicalTriadOrbitSignatureClosed ≡ true
physicalTriadOrbitSignatureClosedIsTrue = refl
