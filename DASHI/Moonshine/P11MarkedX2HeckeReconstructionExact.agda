module DASHI.Moonshine.P11MarkedX2HeckeReconstructionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapter 41, "Brandt matrices",
-- DOI: 10.1007/978-3-030-56694-4_41.
-- Chapter 42, "Supersingular elliptic curves",
-- DOI: 10.1007/978-3-030-56694-4_42.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Prime-to-level isogenies transport full level structures.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- Reconstruct the ACTUAL marked full-level-2 p=11 T3 and T5 from:
--
--   * the source-verified coarse Brandt matrices,
--   * deck-S3 orbital rigidity, and
--   * the quaternion identity-mod-2 marked-loop counts from
--     P11MarkedQuaternionThetaExact.
--
-- In the six-orbital basis
--
--   (AA_id, AA_off, A->B, B->A, BB_id, BB_off)
--
-- the corrected coefficients are
--
--   T3^X(2) = (1,0,1,1,0,1),
--   T5^X(2) = (0,3,1,1,2,1).
--
-- These replace the old hand-built fingerprints
--
--   R3 = (0,1,1,1,0,1),
--   R5 = (0,3,1,1,0,2)
--
-- in the SOURCE-NATIVE lane.  The old files remain as explicit falsifier
-- history and are not rewritten retroactively.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11PositiveBrandtNeighbourSystemsExact as Brandt
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck
import DASHI.Moonshine.P11Level2DoubleCosetHeckeBasisExact as Orbital
import DASHI.Moonshine.P11MarkedQuaternionThetaExact as Theta

------------------------------------------------------------------------
-- Corrected orbital coefficients.
------------------------------------------------------------------------

markedT3OrbitalCoefficients : Orbital.OrbitalCoefficients
markedT3OrbitalCoefficients = Orbital.orbitalCoefficients 1 0 1 1 0 1

markedT5OrbitalCoefficients : Orbital.OrbitalCoefficients
markedT5OrbitalCoefficients = Orbital.orbitalCoefficients 0 3 1 1 2 1

markedT3IdentityCountsAreThetaCounts :
  Orbital.aaId markedT3OrbitalCoefficients ≡ Theta.j0MarkedT3LoopCount
  × Orbital.bbId markedT3OrbitalCoefficients ≡ Theta.j1728MarkedT3LoopCount
markedT3IdentityCountsAreThetaCounts = refl , refl

markedT5IdentityCountsAreThetaCounts :
  Orbital.aaId markedT5OrbitalCoefficients ≡ Theta.j0MarkedT5LoopCount
  × Orbital.bbId markedT5OrbitalCoefficients ≡ Theta.j1728MarkedT5LoopCount
markedT5IdentityCountsAreThetaCounts = refl , refl

------------------------------------------------------------------------
-- Literal positive marked T3 neighbour system, arity 4.
------------------------------------------------------------------------

markedT3Neighbour : Fine.P11Fine5 → Fin 4 → Fine.P11Fine5
markedT3Neighbour Fine.a0 zero = Fine.a0
markedT3Neighbour Fine.a0 (suc zero) = Fine.b0
markedT3Neighbour Fine.a0 (suc (suc zero)) = Fine.b1
markedT3Neighbour Fine.a0 (suc (suc (suc zero))) = Fine.b2
markedT3Neighbour Fine.a1 zero = Fine.a1
markedT3Neighbour Fine.a1 (suc zero) = Fine.b0
markedT3Neighbour Fine.a1 (suc (suc zero)) = Fine.b1
markedT3Neighbour Fine.a1 (suc (suc (suc zero))) = Fine.b2
markedT3Neighbour Fine.b0 zero = Fine.a0
markedT3Neighbour Fine.b0 (suc zero) = Fine.a1
markedT3Neighbour Fine.b0 (suc (suc zero)) = Fine.b1
markedT3Neighbour Fine.b0 (suc (suc (suc zero))) = Fine.b2
markedT3Neighbour Fine.b1 zero = Fine.a0
markedT3Neighbour Fine.b1 (suc zero) = Fine.a1
markedT3Neighbour Fine.b1 (suc (suc zero)) = Fine.b0
markedT3Neighbour Fine.b1 (suc (suc (suc zero))) = Fine.b2
markedT3Neighbour Fine.b2 zero = Fine.a0
markedT3Neighbour Fine.b2 (suc zero) = Fine.a1
markedT3Neighbour Fine.b2 (suc (suc zero)) = Fine.b0
markedT3Neighbour Fine.b2 (suc (suc (suc zero))) = Fine.b1

MarkedT3Positive : Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5
MarkedT3Positive = record
  { Positive.arity = 4
  ; Positive.neighbour = markedT3Neighbour
  }

------------------------------------------------------------------------
-- Literal positive marked T5 neighbour system, arity 6.
------------------------------------------------------------------------

markedT5Neighbour : Fine.P11Fine5 → Fin 6 → Fine.P11Fine5
markedT5Neighbour Fine.a0 zero = Fine.a1
markedT5Neighbour Fine.a0 (suc zero) = Fine.a1
markedT5Neighbour Fine.a0 (suc (suc zero)) = Fine.a1
markedT5Neighbour Fine.a0 (suc (suc (suc zero))) = Fine.b0
markedT5Neighbour Fine.a0 (suc (suc (suc (suc zero)))) = Fine.b1
markedT5Neighbour Fine.a0 (suc (suc (suc (suc (suc zero))))) = Fine.b2
markedT5Neighbour Fine.a1 zero = Fine.a0
markedT5Neighbour Fine.a1 (suc zero) = Fine.a0
markedT5Neighbour Fine.a1 (suc (suc zero)) = Fine.a0
markedT5Neighbour Fine.a1 (suc (suc (suc zero))) = Fine.b0
markedT5Neighbour Fine.a1 (suc (suc (suc (suc zero)))) = Fine.b1
markedT5Neighbour Fine.a1 (suc (suc (suc (suc (suc zero))))) = Fine.b2
markedT5Neighbour Fine.b0 zero = Fine.a0
markedT5Neighbour Fine.b0 (suc zero) = Fine.a1
markedT5Neighbour Fine.b0 (suc (suc zero)) = Fine.b0
markedT5Neighbour Fine.b0 (suc (suc (suc zero))) = Fine.b0
markedT5Neighbour Fine.b0 (suc (suc (suc (suc zero)))) = Fine.b1
markedT5Neighbour Fine.b0 (suc (suc (suc (suc (suc zero))))) = Fine.b2
markedT5Neighbour Fine.b1 zero = Fine.a0
markedT5Neighbour Fine.b1 (suc zero) = Fine.a1
markedT5Neighbour Fine.b1 (suc (suc zero)) = Fine.b1
markedT5Neighbour Fine.b1 (suc (suc (suc zero))) = Fine.b1
markedT5Neighbour Fine.b1 (suc (suc (suc (suc zero)))) = Fine.b0
markedT5Neighbour Fine.b1 (suc (suc (suc (suc (suc zero))))) = Fine.b2
markedT5Neighbour Fine.b2 zero = Fine.a0
markedT5Neighbour Fine.b2 (suc zero) = Fine.a1
markedT5Neighbour Fine.b2 (suc (suc zero)) = Fine.b2
markedT5Neighbour Fine.b2 (suc (suc (suc zero))) = Fine.b2
markedT5Neighbour Fine.b2 (suc (suc (suc (suc zero)))) = Fine.b0
markedT5Neighbour Fine.b2 (suc (suc (suc (suc (suc zero))))) = Fine.b1

MarkedT5Positive : Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5
MarkedT5Positive = record
  { Positive.arity = 6
  ; Positive.neighbour = markedT5Neighbour
  }

------------------------------------------------------------------------
-- Exact coarse projection to the independently verified Brandt neighbours.
------------------------------------------------------------------------

markedT3ProjectsToBrandt :
  (x : Fine.P11Fine5) → (edge : Fin 4) →
  Fine.projectFine5 (markedT3Neighbour x edge)
  ≡ Brandt.ell3Neighbour (Fine.projectFine5 x) edge
markedT3ProjectsToBrandt Fine.a0 zero = refl
markedT3ProjectsToBrandt Fine.a0 (suc zero) = refl
markedT3ProjectsToBrandt Fine.a0 (suc (suc zero)) = refl
markedT3ProjectsToBrandt Fine.a0 (suc (suc (suc zero))) = refl
markedT3ProjectsToBrandt Fine.a1 zero = refl
markedT3ProjectsToBrandt Fine.a1 (suc zero) = refl
markedT3ProjectsToBrandt Fine.a1 (suc (suc zero)) = refl
markedT3ProjectsToBrandt Fine.a1 (suc (suc (suc zero))) = refl
markedT3ProjectsToBrandt Fine.b0 zero = refl
markedT3ProjectsToBrandt Fine.b0 (suc zero) = refl
markedT3ProjectsToBrandt Fine.b0 (suc (suc zero)) = refl
markedT3ProjectsToBrandt Fine.b0 (suc (suc (suc zero))) = refl
markedT3ProjectsToBrandt Fine.b1 zero = refl
markedT3ProjectsToBrandt Fine.b1 (suc zero) = refl
markedT3ProjectsToBrandt Fine.b1 (suc (suc zero)) = refl
markedT3ProjectsToBrandt Fine.b1 (suc (suc (suc zero))) = refl
markedT3ProjectsToBrandt Fine.b2 zero = refl
markedT3ProjectsToBrandt Fine.b2 (suc zero) = refl
markedT3ProjectsToBrandt Fine.b2 (suc (suc zero)) = refl
markedT3ProjectsToBrandt Fine.b2 (suc (suc (suc zero))) = refl

markedT5ProjectsToBrandt :
  (x : Fine.P11Fine5) → (edge : Fin 6) →
  Fine.projectFine5 (markedT5Neighbour x edge)
  ≡ Brandt.ell5Neighbour (Fine.projectFine5 x) edge
markedT5ProjectsToBrandt Fine.a0 zero = refl
markedT5ProjectsToBrandt Fine.a0 (suc zero) = refl
markedT5ProjectsToBrandt Fine.a0 (suc (suc zero)) = refl
markedT5ProjectsToBrandt Fine.a0 (suc (suc (suc zero))) = refl
markedT5ProjectsToBrandt Fine.a0 (suc (suc (suc (suc zero)))) = refl
markedT5ProjectsToBrandt Fine.a0 (suc (suc (suc (suc (suc zero))))) = refl
markedT5ProjectsToBrandt Fine.a1 zero = refl
markedT5ProjectsToBrandt Fine.a1 (suc zero) = refl
markedT5ProjectsToBrandt Fine.a1 (suc (suc zero)) = refl
markedT5ProjectsToBrandt Fine.a1 (suc (suc (suc zero))) = refl
markedT5ProjectsToBrandt Fine.a1 (suc (suc (suc (suc zero)))) = refl
markedT5ProjectsToBrandt Fine.a1 (suc (suc (suc (suc (suc zero))))) = refl
markedT5ProjectsToBrandt Fine.b0 zero = refl
markedT5ProjectsToBrandt Fine.b0 (suc zero) = refl
markedT5ProjectsToBrandt Fine.b0 (suc (suc zero)) = refl
markedT5ProjectsToBrandt Fine.b0 (suc (suc (suc zero))) = refl
markedT5ProjectsToBrandt Fine.b0 (suc (suc (suc (suc zero)))) = refl
markedT5ProjectsToBrandt Fine.b0 (suc (suc (suc (suc (suc zero))))) = refl
markedT5ProjectsToBrandt Fine.b1 zero = refl
markedT5ProjectsToBrandt Fine.b1 (suc zero) = refl
markedT5ProjectsToBrandt Fine.b1 (suc (suc zero)) = refl
markedT5ProjectsToBrandt Fine.b1 (suc (suc (suc zero))) = refl
markedT5ProjectsToBrandt Fine.b1 (suc (suc (suc (suc zero)))) = refl
markedT5ProjectsToBrandt Fine.b1 (suc (suc (suc (suc (suc zero))))) = refl
markedT5ProjectsToBrandt Fine.b2 zero = refl
markedT5ProjectsToBrandt Fine.b2 (suc zero) = refl
markedT5ProjectsToBrandt Fine.b2 (suc (suc zero)) = refl
markedT5ProjectsToBrandt Fine.b2 (suc (suc (suc zero))) = refl
markedT5ProjectsToBrandt Fine.b2 (suc (suc (suc (suc zero)))) = refl
markedT5ProjectsToBrandt Fine.b2 (suc (suc (suc (suc (suc zero))))) = refl

------------------------------------------------------------------------
-- Exact agreement with the corrected orbital multiplicity functions.
------------------------------------------------------------------------

markedT3IsOrbitalReconstruction :
  (x y : Fine.P11Fine5) →
  Deck.edgeMultiplicity MarkedT3Positive x y
  ≡ Orbital.orbitalMultiplicity markedT3OrbitalCoefficients x y
markedT3IsOrbitalReconstruction Fine.a0 Fine.a0 = refl
markedT3IsOrbitalReconstruction Fine.a0 Fine.a1 = refl
markedT3IsOrbitalReconstruction Fine.a0 Fine.b0 = refl
markedT3IsOrbitalReconstruction Fine.a0 Fine.b1 = refl
markedT3IsOrbitalReconstruction Fine.a0 Fine.b2 = refl
markedT3IsOrbitalReconstruction Fine.a1 Fine.a0 = refl
markedT3IsOrbitalReconstruction Fine.a1 Fine.a1 = refl
markedT3IsOrbitalReconstruction Fine.a1 Fine.b0 = refl
markedT3IsOrbitalReconstruction Fine.a1 Fine.b1 = refl
markedT3IsOrbitalReconstruction Fine.a1 Fine.b2 = refl
markedT3IsOrbitalReconstruction Fine.b0 Fine.a0 = refl
markedT3IsOrbitalReconstruction Fine.b0 Fine.a1 = refl
markedT3IsOrbitalReconstruction Fine.b0 Fine.b0 = refl
markedT3IsOrbitalReconstruction Fine.b0 Fine.b1 = refl
markedT3IsOrbitalReconstruction Fine.b0 Fine.b2 = refl
markedT3IsOrbitalReconstruction Fine.b1 Fine.a0 = refl
markedT3IsOrbitalReconstruction Fine.b1 Fine.a1 = refl
markedT3IsOrbitalReconstruction Fine.b1 Fine.b0 = refl
markedT3IsOrbitalReconstruction Fine.b1 Fine.b1 = refl
markedT3IsOrbitalReconstruction Fine.b1 Fine.b2 = refl
markedT3IsOrbitalReconstruction Fine.b2 Fine.a0 = refl
markedT3IsOrbitalReconstruction Fine.b2 Fine.a1 = refl
markedT3IsOrbitalReconstruction Fine.b2 Fine.b0 = refl
markedT3IsOrbitalReconstruction Fine.b2 Fine.b1 = refl
markedT3IsOrbitalReconstruction Fine.b2 Fine.b2 = refl

markedT5IsOrbitalReconstruction :
  (x y : Fine.P11Fine5) →
  Deck.edgeMultiplicity MarkedT5Positive x y
  ≡ Orbital.orbitalMultiplicity markedT5OrbitalCoefficients x y
markedT5IsOrbitalReconstruction Fine.a0 Fine.a0 = refl
markedT5IsOrbitalReconstruction Fine.a0 Fine.a1 = refl
markedT5IsOrbitalReconstruction Fine.a0 Fine.b0 = refl
markedT5IsOrbitalReconstruction Fine.a0 Fine.b1 = refl
markedT5IsOrbitalReconstruction Fine.a0 Fine.b2 = refl
markedT5IsOrbitalReconstruction Fine.a1 Fine.a0 = refl
markedT5IsOrbitalReconstruction Fine.a1 Fine.a1 = refl
markedT5IsOrbitalReconstruction Fine.a1 Fine.b0 = refl
markedT5IsOrbitalReconstruction Fine.a1 Fine.b1 = refl
markedT5IsOrbitalReconstruction Fine.a1 Fine.b2 = refl
markedT5IsOrbitalReconstruction Fine.b0 Fine.a0 = refl
markedT5IsOrbitalReconstruction Fine.b0 Fine.a1 = refl
markedT5IsOrbitalReconstruction Fine.b0 Fine.b0 = refl
markedT5IsOrbitalReconstruction Fine.b0 Fine.b1 = refl
markedT5IsOrbitalReconstruction Fine.b0 Fine.b2 = refl
markedT5IsOrbitalReconstruction Fine.b1 Fine.a0 = refl
markedT5IsOrbitalReconstruction Fine.b1 Fine.a1 = refl
markedT5IsOrbitalReconstruction Fine.b1 Fine.b0 = refl
markedT5IsOrbitalReconstruction Fine.b1 Fine.b1 = refl
markedT5IsOrbitalReconstruction Fine.b1 Fine.b2 = refl
markedT5IsOrbitalReconstruction Fine.b2 Fine.a0 = refl
markedT5IsOrbitalReconstruction Fine.b2 Fine.a1 = refl
markedT5IsOrbitalReconstruction Fine.b2 Fine.b0 = refl
markedT5IsOrbitalReconstruction Fine.b2 Fine.b1 = refl
markedT5IsOrbitalReconstruction Fine.b2 Fine.b2 = refl

record P11MarkedX2HeckeBoundary : Set where
  field
    markedT3ReconstructedFromThetaAndBrandt : Bool
    markedT3ReconstructedFromThetaAndBrandtIsTrue :
      markedT3ReconstructedFromThetaAndBrandt ≡ true

    markedT5ReconstructedFromThetaAndBrandt : Bool
    markedT5ReconstructedFromThetaAndBrandtIsTrue :
      markedT5ReconstructedFromThetaAndBrandt ≡ true

    bothOperatorsPositiveBeforeLinearization : Bool
    bothOperatorsPositiveBeforeLinearizationIsTrue :
      bothOperatorsPositiveBeforeLinearization ≡ true

    bothOperatorsProjectToVerifiedBrandt : Bool
    bothOperatorsProjectToVerifiedBrandtIsTrue :
      bothOperatorsProjectToVerifiedBrandt ≡ true

    oldHandBuiltR3R5ProtectedFromFalsification : Bool
    oldHandBuiltR3R5ProtectedFromFalsificationIsFalse :
      oldHandBuiltR3R5ProtectedFromFalsification ≡ false

canonicalP11MarkedX2HeckeBoundary : P11MarkedX2HeckeBoundary
canonicalP11MarkedX2HeckeBoundary = record
  { markedT3ReconstructedFromThetaAndBrandt = true
  ; markedT3ReconstructedFromThetaAndBrandtIsTrue = refl
  ; markedT5ReconstructedFromThetaAndBrandt = true
  ; markedT5ReconstructedFromThetaAndBrandtIsTrue = refl
  ; bothOperatorsPositiveBeforeLinearization = true
  ; bothOperatorsPositiveBeforeLinearizationIsTrue = refl
  ; bothOperatorsProjectToVerifiedBrandt = true
  ; bothOperatorsProjectToVerifiedBrandtIsTrue = refl
  ; oldHandBuiltR3R5ProtectedFromFalsification = false
  ; oldHandBuiltR3R5ProtectedFromFalsificationIsFalse = refl
  }
