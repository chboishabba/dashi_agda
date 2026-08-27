module DASHI.Moonshine.C3RiemannConjugationBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Bernhard Riemann,
-- "Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse" (1859).
-- No DOI was assigned to the original publication.
--
-- Enrico Bombieri,
-- "Problems of the Millennium: The Riemann Hypothesis",
-- Clay Mathematics Institute problem description.
-- No DOI assigned.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Close the exact part of the C3/Riemann conjugation comparison without
-- identifying Monster/Ogg lanes with zeta zeros.  In the symbolic C3 phase
-- carrier, inversion/conjugation has exactly one fixed phase, the trivial
-- phase.  In the repository's exact rational completed-zeta coordinate model,
-- functional reflection s |-> 1-s equals complex conjugation exactly on the
-- critical line Re(s)=1/2.
--
-- This is a shared involution/fixed-locus grammar.  It is not a proof of RH
-- and supplies no map from SSP15 or Monster states to nontrivial zeta zeros.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact as Xi
import DASHI.Moonshine.C3FourierConjugationExact as Fourier

------------------------------------------------------------------------
-- C3 conjugation fixed locus.

zetaIsNotFixedByConjugation :
  Fourier.inversePhase Fourier.zeta ≡ Fourier.zeta → ⊥
zetaIsNotFixedByConjugation ()

zetaSquaredIsNotFixedByConjugation :
  Fourier.inversePhase Fourier.zetaSquared ≡ Fourier.zetaSquared → ⊥
zetaSquaredIsNotFixedByConjugation ()

conjugationFixedPhaseIsTrivial :
  (phase : C3.C3Phase) →
  Fourier.inversePhase phase ≡ phase →
  phase ≡ Fourier.one
conjugationFixedPhaseIsTrivial C3.phase0 refl = refl
conjugationFixedPhaseIsTrivial C3.phase1 ()
conjugationFixedPhaseIsTrivial C3.phase2 ()

trivialPhaseIsConjugationFixed :
  Fourier.inversePhase Fourier.one ≡ Fourier.one
trivialPhaseIsConjugationFixed = refl

------------------------------------------------------------------------
-- Exact completed-zeta coordinate theorem:
--
--   Re(s)=1/2  <=>  functionalReflection(s)=conjugateCoordinate(s).
--
-- The existing owner already proves that criticalReflection fixes exactly the
-- critical line and that conjugation after functional reflection is precisely
-- criticalReflection.  We transport through those proved involutions rather
-- than reproving the rational algebra.

criticalLineImpliesFunctionalEqualsConjugate :
  (point : Xi.ComplexCoordinate) →
  Xi.CriticalLine point →
  Xi.functionalReflection point ≡ Xi.conjugateCoordinate point
criticalLineImpliesFunctionalEqualsConjugate point onLine =
  let
    criticalFixed : Xi.criticalReflection point ≡ point
    criticalFixed = Xi.criticalLineFixedByReflection point onLine

    conjugatedFunctionalEqualsConjugatedCritical :
      Xi.conjugateCoordinate (Xi.conjugateCoordinate (Xi.functionalReflection point))
      ≡ Xi.conjugateCoordinate (Xi.criticalReflection point)
    conjugatedFunctionalEqualsConjugatedCritical =
      cong Xi.conjugateCoordinate (Xi.functionalThenConjugateIsCritical point)

    functionalEqualsConjugatedCritical :
      Xi.functionalReflection point
      ≡ Xi.conjugateCoordinate (Xi.criticalReflection point)
    functionalEqualsConjugatedCritical =
      trans
        (sym (Xi.conjugationInvolutive (Xi.functionalReflection point)))
        conjugatedFunctionalEqualsConjugatedCritical
  in
  trans
    functionalEqualsConjugatedCritical
    (cong Xi.conjugateCoordinate criticalFixed)

functionalEqualsConjugateImpliesCriticalLine :
  (point : Xi.ComplexCoordinate) →
  Xi.functionalReflection point ≡ Xi.conjugateCoordinate point →
  Xi.CriticalLine point
functionalEqualsConjugateImpliesCriticalLine point reflectionEqualsConjugate =
  Xi.reflectionFixedImpliesCriticalLine point criticalFixed
  where
    conjugatedEquality :
      Xi.conjugateCoordinate (Xi.functionalReflection point)
      ≡ Xi.conjugateCoordinate (Xi.conjugateCoordinate point)
    conjugatedEquality = cong Xi.conjugateCoordinate reflectionEqualsConjugate

    criticalFixed : Xi.criticalReflection point ≡ point
    criticalFixed =
      trans
        (sym (Xi.functionalThenConjugateIsCritical point))
        (trans
          conjugatedEquality
          (Xi.conjugationInvolutive point))

------------------------------------------------------------------------
-- Both directions exposed together without introducing an additional iff
-- encoding or a speculative map between the two domains.

record ReflectionConjugationCoincidence (point : Xi.ComplexCoordinate) : Set where
  constructor reflectionConjugationCoincidence
  field
    onCriticalLine : Xi.CriticalLine point
    reflectionEqualsConjugation :
      Xi.functionalReflection point ≡ Xi.conjugateCoordinate point

open ReflectionConjugationCoincidence public

criticalLineCoincidence :
  (point : Xi.ComplexCoordinate) →
  Xi.CriticalLine point →
  ReflectionConjugationCoincidence point
criticalLineCoincidence point onLine =
  reflectionConjugationCoincidence
    onLine
    (criticalLineImpliesFunctionalEqualsConjugate point onLine)
