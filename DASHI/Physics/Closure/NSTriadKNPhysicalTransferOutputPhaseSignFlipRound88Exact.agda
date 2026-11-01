module DASHI.Physics.Closure.NSTriadKNPhysicalTransferOutputPhaseSignFlipRound88Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Finite time blowup for an averaged three-dimensional Navier-Stokes
-- equation".
-- DOI: 10.1090/jams/838.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- ROUND88 / LITERAL SIGN-FLIP OBSTRUCTION TO GEOMETRY-ONLY COERCIVITY
--
-- The exact ordered Fourier transfer coefficient is linear in the tested
-- output velocity through the Hermitian pairing.  Negating only that output
-- velocity therefore reverses the coefficient exactly while leaving the
-- frequency triad (k,p,q), resonance, shell separation and the two input
-- velocities unchanged:
--
--   T(k,p,q; u_p,u_q,-u_k) = - T(k,p,q; u_p,u_q,u_k).
--
-- This is stronger than a numerical HH->low example.  Any nonzero literal
-- transfer carried by fixed HH->low geometry automatically has an opposite-sign
-- realization on the SAME geometry by an output phase flip of pi.  Thus no
-- theorem depending only on p,q,k shell/angle geometry can force the sign of
-- the individual transfer atom.  A successful viscous-margin theorem must
-- retain a signed/coherence observable on the velocity phases/polarisations or
-- prove an equivalent aggregate cancellation theorem.
--
-- Tao's averaged-NS theorem is cited only as external context for why such fine
-- nonlinear structure cannot be discarded.  The sign-flip theorem below is a
-- direct exact consequence of the repository's literal Complex3 coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Hermitian
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed

complexRealPartNegate :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex F) →
  C3.complexRealPart (C3.complexNegate value)
  ≡ C3.complexNegate (C3.complexRealPart value)
complexRealPartNegate {F = F} (C3.complex real imaginary)
  rewrite C3.negateZero F = refl

testedSignedCoefficientOutputNegate :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (uP uQ testK : C3.Complex3 F) →
  Signed.testedSignedCoefficient
    (C3.complex3VelocityGalerkinLaws F E I)
    k p q uP uQ (C3.complex3Negate testK)
  ≡ C3.complexNegate
      (Signed.testedSignedCoefficient
        (C3.complex3VelocityGalerkinLaws F E I)
        k p q uP uQ testK)
testedSignedCoefficientOutputNegate {F = F} E I k p q uP uQ testK =
  let
    interaction =
      Signed.orderedVelocityInteraction
        (C3.complex3VelocityGalerkinLaws F E I)
        k p q uP uQ
  in
  trans
    (cong C3.complexRealPart
      (Hermitian.hermitianPairingNegateLeft testK interaction))
    (complexRealPartNegate (C3.hermitianPairing3 testK interaction))

record FixedGeometryTransferPair {r}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) : Set r where
  constructor fixed-geometry-transfer-pair
  field
    k p q : Z3.FourierMode
    uP uQ outputVelocity : C3.Complex3 F

open FixedGeometryTransferPair public

forwardTransfer :
  ∀ {r F E I} → FixedGeometryTransferPair {r} F E I → C3.Complex F
forwardTransfer {F = F} {E = E} {I = I} pair =
  Signed.testedSignedCoefficient
    (C3.complex3VelocityGalerkinLaws F E I)
    (k pair) (p pair) (q pair)
    (uP pair) (uQ pair) (outputVelocity pair)

phaseFlippedTransfer :
  ∀ {r F E I} → FixedGeometryTransferPair {r} F E I → C3.Complex F
phaseFlippedTransfer {F = F} {E = E} {I = I} pair =
  Signed.testedSignedCoefficient
    (C3.complex3VelocityGalerkinLaws F E I)
    (k pair) (p pair) (q pair)
    (uP pair) (uQ pair) (C3.complex3Negate (outputVelocity pair))

fixedGeometryOutputPhaseFlipReversesTransfer :
  ∀ {r F E I} (pair : FixedGeometryTransferPair {r} F E I) →
  phaseFlippedTransfer pair ≡ C3.complexNegate (forwardTransfer pair)
fixedGeometryOutputPhaseFlipReversesTransfer {F = F} {E = E} {I = I} pair =
  testedSignedCoefficientOutputNegate
    E I (k pair) (p pair) (q pair)
    (uP pair) (uQ pair) (outputVelocity pair)

round88FixedFrequencyGeometryCannotDetermineLiteralTransferSign : Bool
round88FixedFrequencyGeometryCannotDetermineLiteralTransferSign = true

round88HHViscousMarginNeedsSignedCoherenceOrEquivalent : Bool
round88HHViscousMarginNeedsSignedCoherenceOrEquivalent = true

round88FixedFrequencyGeometryCannotDetermineLiteralTransferSignIsTrue :
  round88FixedFrequencyGeometryCannotDetermineLiteralTransferSign ≡ true
round88FixedFrequencyGeometryCannotDetermineLiteralTransferSignIsTrue = refl

round88HHViscousMarginNeedsSignedCoherenceOrEquivalentIsTrue :
  round88HHViscousMarginNeedsSignedCoherenceOrEquivalent ≡ true
round88HHViscousMarginNeedsSignedCoherenceOrEquivalentIsTrue = refl
