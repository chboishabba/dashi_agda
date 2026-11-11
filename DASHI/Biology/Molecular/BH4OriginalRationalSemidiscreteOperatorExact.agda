module DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact where

-- Exact typed finite-volume operator for the existing 369/27 chart.
-- Geometric and chemical inputs are NOT fabricated: the matrix data
-- must come from the original 54 native bonds and original 29x12 Rhea
-- source owner before this can be called a source-paid physical model.
--
-- This is a rational semidiscrete *operator*, not a physical PNP law.
-- SG, actual compartment exchanges and original reaction-rate kinetics
-- are independent constitutive obligations. No decimal/float conversion.
--
-- Attribution: semidiscrete finite-volume algebra is standard; the
-- selected original 369 geometry/BH4 identity belongs to DASHI.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q

-- Rectangular rational matrix, with dimensions checked by Agda.
Matrix : Nat → Nat → Set
Matrix rows columns = V.Vec (V.Vec Q.ℚᵘ columns) rows

-- Finite row dot product; recursion is total at any fixed dimension.
rationalDot :
  ∀ {n} → V.Vec Q.ℚᵘ n → V.Vec Q.ℚᵘ n → Q.ℚᵘ
rationalDot V.[] V.[] = Q.0ℚᵘ
rationalDot (V._∷_ a as) (V._∷_ b bs) =
  Q._+_ (Q._*_ a b) (rationalDot as bs)

-- Column j of a rectangular finite matrix.
rationalColumn :
  ∀ {m n} → Matrix m n → F.Fin n → V.Vec Q.ℚᵘ m
rationalColumn rows j = V.map (λ row → V.lookup row j) rows

-- Native bond currents at each original species: 54 x 29.
-- The oriented incidence is site x native-bond, 27 x 54.
-- The original finite chemical stoichiometry is species x reaction,
-- 29 x 12. Site reaction rates are 27 x 12.
record Rational369SemidiscreteInputs : Set where
  constructor rational369-inputs
  field
    orientedNativeIncidence : Matrix 27 54
    signedNativeBondFluxes : Matrix 54 29
    originalFiniteStoichiometry : Matrix 29 12
    originalFiniteReactionRates : Matrix 27 12

open Rational369SemidiscreteInputs public

-- Negative divergence and reaction source are kept separate.
-- Incidence orientation is fixed by the SOURCE geometric owner;
-- using the wrong sign here would be a source-matching failure.
bondContribution :
  Rational369SemidiscreteInputs →
  F.Fin 27 → F.Fin 29 → Q.ℚᵘ
bondContribution inputs site species =
  rationalDot
    (V.lookup (orientedNativeIncidence inputs) site)
    (rationalColumn (signedNativeBondFluxes inputs) species)

reactionContribution :
  Rational369SemidiscreteInputs →
  F.Fin 27 → F.Fin 29 → Q.ℚᵘ
reactionContribution inputs site species =
  rationalDot
    (V.lookup (originalFiniteStoichiometry inputs) species)
    (V.lookup (originalFiniteReactionRates inputs) site)

-- Exact finite chemical+transport RHS with ALL 783 coordinates.
-- The signed incidence convention must be identified against the
-- existing original 54-bond geometric source before use.
rational369SemidiscreteRHS :
  Rational369SemidiscreteInputs → Matrix 27 29
rational369SemidiscreteRHS inputs =
  V.tabulate (λ site →
    V.tabulate (λ species →
      Q._+_
        (bondContribution inputs site species)
        (reactionContribution inputs site species)))

-- Extracting a coordinate agrees definitionally with the actual
-- native finite-volume formula, not a separately asserted relation.
rational369SemidiscreteAt :
  (inputs : Rational369SemidiscreteInputs)
  (site : F.Fin 27) (species : F.Fin 29) →
  V.lookup (V.lookup (rational369SemidiscreteRHS inputs) site) species
    ≡ Q._+_
        (bondContribution inputs site species)
        (reactionContribution inputs site species)
rational369SemidiscreteAt inputs site species = refl

-- The existing source-independent rational -> Bishop finite-sum lift
-- can now consume this computed RHS. The six left-kernel/edge-zero
-- witnesses remain an original-source proof obligation, NOT fields
-- silently inhabited by a synthetic or guessed matrix.
