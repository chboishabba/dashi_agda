module DASHI.Physics.Closure.NSTriadKNOutputRelocationConcreteSobolevElevenFourths where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin;
-- Agda standard-library contributors; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; "Fourier Analysis and Nonlinear Partial Differential
-- Equations"; and "Concrete s = 11/4 output-relocation Sobolev instance".
-- Venue/year: Springer, 1985 and 2011; Dalhousie University/arXiv, 2022;
-- Agda standard library; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354;
-- 10.1007/978-3-642-16830-7; the repository instance has no DOI.
-- Uses: exact rational normalization and the unified strict rational
-- embedding supplied by the native ordered-field capability.
-- Relationship: closes the formerly open choice of a concrete Sobolev
-- exponent.  The selected value 11/4 lies strictly between 5/2 and 3 and
-- yields low decay 3 and gap decay 11/2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _<_; _+_; _-_; 1ℚ)
open import Data.Rational.Properties using (_<?_)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Data.Unit.Base using (tt)

import DASHI.Analysis.ConstructiveRealSpine as Spine
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputRelocationDerivedClosure as Derived
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOrderedFieldCapabilityAdapter as Ordered
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputDecayFromOrderedField as Decay

elevenFourths : ℚ
elevenFourths = Int.+ 11 / 4

threeRational : ℚ
threeRational = (1ℚ + 1ℚ) + 1ℚ

elevenFourthsAboveFiveHalves :
  Derived.fiveHalvesRational < elevenFourths
elevenFourthsAboveFiveHalves =
  toWitness
    {a? = Derived.fiveHalvesRational <? elevenFourths}
    tt

elevenFourthsBelowThree : elevenFourths < threeRational
elevenFourthsBelowThree =
  toWitness
    {a? = elevenFourths <? threeRational}
    tt

concreteElevenFourthsInterval : ∀ R
    (field : Ordered.ConstructiveRealSpineOrderedFieldCapability R) →
  Decay.NativeSobolevExponentInTargetInterval R field
concreteElevenFourthsInterval R field = record
  { sobolevExponent = Ordered.rationalEmbed field elevenFourths
  ; aboveFiveHalves =
      Ordered.embedStrictOrder field elevenFourthsAboveFiveHalves
  ; belowThree =
      Ordered.embedStrictOrder field elevenFourthsBelowThree
  }

concreteElevenFourthsDecayData : ∀ R
    (field : Ordered.ConstructiveRealSpineOrderedFieldCapability R)
    (power : Derived.ConstructiveRealSpineBaseTwoPowerCapability
      R (Ordered.asEnvelopeCapability R field)) →
  Derived.ConstructiveRealSpineOutputDecayData
    R (Ordered.asEnvelopeCapability R field) power
concreteElevenFourthsDecayData R field power =
  Decay.outputDecayDataFromComputedRationalEndpoint
    R field power (concreteElevenFourthsInterval R field)

concreteSobolevExponentElevenFourthsClosed : Bool
concreteSobolevExponentElevenFourthsClosed = true

concreteSobolevExponentElevenFourthsClosedIsTrue :
  concreteSobolevExponentElevenFourthsClosed ≡ true
concreteSobolevExponentElevenFourthsClosedIsTrue = refl
