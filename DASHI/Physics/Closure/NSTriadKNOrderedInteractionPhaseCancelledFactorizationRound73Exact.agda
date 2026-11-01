module DASHI.Physics.Closure.NSTriadKNOrderedInteractionPhaseCancelledFactorizationRound73Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- ROUND73 / LITERAL ORDERED INTERACTION -> REAL AMPLITUDE PRODUCT
--
-- The previous Round73 files construct, on the SAME physical triad,
--
--   transportScalar = -i (u_p dot q),
--   testedHighResponse = <test_k, P_k u_q>,
--
-- and prove the signed coefficient is
--
--   realPart(transportScalar * testedHighResponse).
--
-- The phase-cancellation compiler proves that if these two concrete source
-- factors admit the physically aligned form
--
--   transportScalar    = x theta,
--   testedHighResponse = y conjugate(theta),
--   theta conjugate(theta) = 1,
--
-- then the signed coefficient is exactly the real amplitude product x*y.
--
-- This file composes those statements.  It therefore isolates the remaining
-- LH/HL source theorem to construction of ONE phase-alignment witness on the
-- literal velocity/projector/test data.  No rational factor may be chosen after
-- inspecting the resulting scalar coefficient.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOrderedInteractionSourceFactorizationRound73Exact as Source
import DASHI.Physics.Closure.NSTriadKNPhaseCancelledComplexProductRound73Exact as Phase

record PhysicalOrderedInteractionPhaseAlignment
    {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (testK : C3.Complex3 F) : Set r where
  field
    phaseCancelled :
      Phase.PhaseCancelledProduct
        (Source.transportScalar system incidence)
        (Source.testedHighResponse system incidence testK)

open PhysicalOrderedInteractionPhaseAlignment public

phaseAlignedSignedCoefficientExact :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {incidence : Physical.PhysicalTriadIncidence}
    {testK : C3.Complex3 F} →
  (alignment : PhysicalOrderedInteractionPhaseAlignment
    system incidence testK) →
  Signed.testedSignedCoefficient
    (Audit.galerkinLaws system)
    (Physical.k incidence)
    (Physical.p incidence)
    (Physical.q incidence)
    (Audit.velocityAt system (Physical.p incidence))
    (Audit.velocityAt system (Physical.q incidence))
    testK
  ≡ C3.realEmbed F
      (C3.multiply F
        (Phase.leftAmplitude (phaseCancelled alignment))
        (Phase.rightAmplitude (phaseCancelled alignment)))
phaseAlignedSignedCoefficientExact {system = system}
    {incidence = incidence} {testK = testK} alignment =
  trans
    (Source.signedCoefficientIsRealPartOfSourceProduct
      system incidence testK)
    (Phase.phaseCancelledRealPartExact (phaseCancelled alignment))

round73PhaseAlignmentCompilesLiteralSignedCoefficientToAmplitudeProduct : Bool
round73PhaseAlignmentCompilesLiteralSignedCoefficientToAmplitudeProduct = true

round73PhysicalOrderedInteractionPhaseAlignmentConstructed : Bool
round73PhysicalOrderedInteractionPhaseAlignmentConstructed = false

round73PhaseAlignmentCompilesLiteralSignedCoefficientToAmplitudeProductIsTrue :
  round73PhaseAlignmentCompilesLiteralSignedCoefficientToAmplitudeProduct ≡ true
round73PhaseAlignmentCompilesLiteralSignedCoefficientToAmplitudeProductIsTrue = refl

round73PhysicalOrderedInteractionPhaseAlignmentConstructedIsFalse :
  round73PhysicalOrderedInteractionPhaseAlignmentConstructed ≡ false
round73PhysicalOrderedInteractionPhaseAlignmentConstructedIsFalse = refl
