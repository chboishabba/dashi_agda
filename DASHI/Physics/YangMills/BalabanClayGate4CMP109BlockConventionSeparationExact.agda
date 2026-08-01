module DASHI.Physics.YangMills.BalabanClayGate4CMP109BlockConventionSeparationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact separation of the source and repository block conventions.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- CMP109 writes a block point as y + n with
--
--   |n_mu| <= (L - 1) / 2,
--
-- so the displayed centred-coordinate convention has odd side L = 2r + 1.
-- The repository's current one-step parity split has side 2 and is a useful
-- dyadic corner-block carrier, but it is not definitionally the same convention.
-- The finite theorem below proves that no natural radius r satisfies 2r+1=2.
-- Any physical use of the dyadic carrier as CMP109 data must therefore provide
-- an explicit translated/partitioned convention bridge rather than marking the
-- two geometries identical by reflexivity.
------------------------------------------------------------------------

data Empty : Set where

Not : Set → Set
Not proposition = proposition → Empty

twice : Nat → Nat
twice zero = zero
twice (suc value) = suc (suc (twice value))

two : Nat
two = suc (suc zero)

centeredOddSide : Nat → Nat
centeredOddSide radius = suc (twice radius)

noCenteredNaturalRadiusHasDyadicSide :
  ∀ radius → Not (centeredOddSide radius ≡ two)
noCenteredNaturalRadiusHasDyadicSide zero ()
noCenteredNaturalRadiusHasDyadicSide (suc radius) ()

data BlockConvention : Set where
  cmp109CenteredOdd : BlockConvention
  repositoryDyadicCorner : BlockConvention

record BlockConventionBridge : Set₁ where
  field
    SourceBlock RepositoryBlock : Set
    sourceConvention repositoryConvention : BlockConvention

    translateSourceToRepository : SourceBlock → RepositoryBlock
    translateRepositoryToSource : RepositoryBlock → SourceBlock

    sourceRoundTrip : ∀ source →
      translateRepositoryToSource (translateSourceToRepository source)
      ≡ source

    repositoryRoundTrip : ∀ repository →
      translateSourceToRepository (translateRepositoryToSource repository)
      ≡ repository

    averagingWeightPreserved : Set
    endpointSupportPreserved : Set
    contourFamilyPreserved : Set

open BlockConventionBridge public

cmp109CenteredDyadicConventionSeparationLevel : ProofLevel
cmp109CenteredDyadicConventionSeparationLevel = machineChecked

physicalCMP109DyadicConventionBridgeInputsLevel : ProofLevel
physicalCMP109DyadicConventionBridgeInputsLevel = conditional
