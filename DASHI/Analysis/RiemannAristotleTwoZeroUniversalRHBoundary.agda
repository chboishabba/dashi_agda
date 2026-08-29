module DASHI.Analysis.RiemannAristotleTwoZeroUniversalRHBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BIDIRECTIONAL CORRECTION: the inhabited two-zero / three-taper theorem is
-- powerful finite-carrier infrastructure, but it is not by itself a universal
-- off-line-zero contradiction theorem.
--
-- Its Lean hypothesis requires three actual zeros with strictly ordered
-- positive horizontal heights
--
--   0 < height σ1 < height σ2 < height rho.
--
-- The assumption needed for the RH contradiction is only "there exists one
-- off-line zero".  Pure logic cannot manufacture two additional positive,
-- strictly smaller zero heights from that witness.
--
-- The finite model below makes this non-implication executable.  It is not a
-- model of zeta; it proves only that the extra ordered-zero witnesses are real
-- hypotheses and cannot be silently erased by the final compiler.
------------------------------------------------------------------------

data OneZero : Set where
  rho : OneZero

OffLine : OneZero → Set
OffLine rho = ⊤

PositiveHeight : OneZero → Set
PositiveHeight rho = ⊤

StrictHeightBelow : OneZero → OneZero → Set
StrictHeightBelow _ _ = ⊥

oneOffLineWitness : Σ OneZero OffLine
oneOffLineWitness = rho , tt

OrderedPositiveTriple : Set
OrderedPositiveTriple =
  Σ OneZero (λ σ1 →
  Σ OneZero (λ σ2 →
  Σ OneZero (λ target →
    PositiveHeight σ1 ×
    PositiveHeight σ2 ×
    PositiveHeight target ×
    StrictHeightBelow σ1 σ2 ×
    StrictHeightBelow σ2 target)))

oneOffLineDoesNotSupplyOrderedPositiveTriple : ¬ OrderedPositiveTriple
oneOffLineDoesNotSupplyOrderedPositiveTriple
  (sigma1 , sigma2 , target , h1 , h2 , h3 , below12 , below2t) = below12

record TwoZeroUniversalBoundary : Set where
  constructor two-zero-universal-boundary
  field
    inhabitedTwoZeroTheoremUsefulLocally : Bool
    inhabitedTwoZeroTheoremUsefulLocallyIsTrue :
      inhabitedTwoZeroTheoremUsefulLocally ≡ true
    oneOffLineWitnessAutomaticallySuppliesTwoSmallerPositiveZeroHeights : Bool
    oneOffLineWitnessAutomaticallySuppliesTwoSmallerPositiveZeroHeightsIsFalse :
      oneOffLineWitnessAutomaticallySuppliesTwoSmallerPositiveZeroHeights ≡ false
    twoZeroTheoremAloneClosesUniversalRHBridge : Bool
    twoZeroTheoremAloneClosesUniversalRHBridgeIsFalse :
      twoZeroTheoremAloneClosesUniversalRHBridge ≡ false
    deterministicNuisanceQuotientPreferredForUniversalLane : Bool
    deterministicNuisanceQuotientPreferredForUniversalLaneIsTrue :
      deterministicNuisanceQuotientPreferredForUniversalLane ≡ true
    boundedReading : String

open TwoZeroUniversalBoundary public

canonicalTwoZeroUniversalBoundary : TwoZeroUniversalBoundary
canonicalTwoZeroUniversalBoundary =
  two-zero-universal-boundary
    true refl
    false refl
    false refl
    true refl
    "Exact two-selected-zero elimination remains valuable whenever those zeros are actually certified. It cannot serve as the universal RH contradiction bridge from a single off-line witness. The universal lane should eliminate deterministic nuisance modes that are present for every target (notably the literal pole pair), then control the remaining literal carrier."
