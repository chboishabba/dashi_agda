module DASHI.Physics.QuantumVacuum.PerfectConductorFiniteCutoffParsevalBidiExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (map)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoTorusTrigonometricPolynomialExact as Torus
import DASHI.Physics.Closure.NSTriadKNLuoTorusTrigonometricParsevalExact as Parseval

------------------------------------------------------------------------
-- FINITE-CUTOFF PLATE PARSEVAL, BIDI
--
-- master already owns an exact finite torus trigonometric Parseval theorem.
-- A Casimir cutoff therefore does not need a second Parseval proof.  It needs
-- only an explicit map from its literal finite plate modes to the torus terms
-- on which the existing theorem acts.
--
-- This is intentionally finite.  It proves neither continuum L2 completeness
-- nor the electromagnetic TE/TM spanning theorem.
------------------------------------------------------------------------

record FiniteCutoffTorusRealisation
    {r : _}
    (F : C3.RealField r) : Set₁ where
  field
    PlateMode : Set
    plateModes : List PlateMode

    torus : Torus.TorusCharacterIntegral F
    encode : PlateMode → Torus.TorusTerm F (Torus.Mode torus)
    terms : List (Torus.TorusTerm F (Torus.Mode torus))
    termsAreEncodedPlateModes : terms ≡ map encode plateModes

    sameCutoffModeLabels : Set
    sameCoefficientNormalisation : Set
    physicalEnergyMatchesTorusEnergy : Set
    reading : String

open FiniteCutoffTorusRealisation public

finiteCutoffParseval :
  ∀ {r} {F : C3.RealField r} →
  (R : FiniteCutoffTorusRealisation F) →
  Parseval.physicalPolynomialEnergy (torus R) (terms R)
  ≡ Parseval.polynomialCoefficientEnergy (torus R) (terms R) (terms R)
finiteCutoffParseval R =
  Parseval.torusFiniteParseval (torus R) (terms R)

record ReverseFiniteCutoffParsevalObligations : Set where
  field
    literalCutoffListIdentified : Set
    torusCharacterCarrierIdentified : Set
    modeEncodingExact : Set
    coefficientNormalisationExact : Set
    physicalEnergyWeld : Set

open ReverseFiniteCutoffParsevalObligations public

data FiniteParsevalAutomaticallyProvesContinuumCompleteness : Set where
data NavierStokesParsevalApplicationAutomaticallyIsCasimirApplication : Set where

finiteParsevalDoesNotProveContinuumCompleteness :
  FiniteParsevalAutomaticallyProvesContinuumCompleteness → ⊥
finiteParsevalDoesNotProveContinuumCompleteness ()

noForeignApplicationReceiptReuse :
  NavierStokesParsevalApplicationAutomaticallyIsCasimirApplication → ⊥
noForeignApplicationReceiptReuse ()
