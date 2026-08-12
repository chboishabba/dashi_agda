module DASHI.Core.C3OrbitProvenanceQuotientExact where

------------------------------------------------------------------------
-- C3 ORBIT QUOTIENT + REOPENING RECEIPT
--
-- This is the first honest finite group-action specialization of the generic
-- ProvenanceBearingQuotient.  The regular C3 action has a single orbit; the
-- coarse orbit label therefore forgets all three point positions.  A retained
-- point receipt reopens the exact fine state.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as PBQ
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3

orbitCore : Fibre.FibreRestrictionCore
orbitCore =
  Fibre.fibreRestrictionCore
    C3.C3
    ⊤
    ⊤
    (λ _ → tt)
    (λ _ → C3.C3)
    (λ _ _ → C3.C3)
    false
    false

orbitReceipt : C3.C3 → C3.C3
orbitReceipt x = x

reopenOrbit : ⊤ → C3.C3 → C3.C3
reopenOrbit _ receipt = receipt

reopenOrbitExact : ∀ x → reopenOrbit (Fibre.project orbitCore x) (orbitReceipt x) ≡ x
reopenOrbitExact x = refl

c3OrbitProvenanceBearingQuotient : PBQ.ProvenanceBearingQuotient orbitCore
c3OrbitProvenanceBearingQuotient =
  PBQ.provenanceBearingQuotient
    C3.C3
    orbitReceipt
    reopenOrbit
    reopenOrbitExact

------------------------------------------------------------------------
-- The coarse quotient really does identify all three phase points.
------------------------------------------------------------------------

allOrbitPointsCoarsenTogether01 :
  Fibre.project orbitCore C3.c0 ≡ Fibre.project orbitCore C3.c1
allOrbitPointsCoarsenTogether01 = refl

allOrbitPointsCoarsenTogether12 :
  Fibre.project orbitCore C3.c1 ≡ Fibre.project orbitCore C3.c2
allOrbitPointsCoarsenTogether12 = refl

------------------------------------------------------------------------
-- Yet the quotient receipt keeps their distinct fine coordinates available.
------------------------------------------------------------------------

reopenC0 : reopenOrbit tt (orbitReceipt C3.c0) ≡ C3.c0
reopenC0 = refl

reopenC1 : reopenOrbit tt (orbitReceipt C3.c1) ≡ C3.c1
reopenC1 = refl

reopenC2 : reopenOrbit tt (orbitReceipt C3.c2) ≡ C3.c2
reopenC2 = refl
