module DASHI.Physics.Motors.SmithFilsingerThreeEarthElectrodeReturnIdentifiabilityExact where

-- ORIGINAL source: Filsinger Earth three-electrode reel Dfi1D7CPzyM.
-- Source review: Docs/research/FilsingerEarthThreeElectrodesZVSFrequencyPull20261110.md
-- Original meter display: ~3.8 V, ~0.4 W, ~48 V across two capacitors;
-- the graph, three pin potentials, return currents, meter terminal pair,
-- source synchrony and attribution remain UNMEASURED/UNIDENTIFIED.
--
-- Exact finite illustrative graph: 3 ordinary differential-conduction
-- contacts, NOT a reconstructed soil conductivity or the portable plates.
-- Source attribution remains with the existing DonSmithFilsingerClaimBidi
-- and the original Filsinger SelectedBoundary/SourceOwner source operators.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve; solve-∀)

import DASHI.Physics.Motors.SmithFilsingerReflectedPortBidiExact as Bidi
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Original

record OriginalEarthThreeContactCandidate
  (b : Original.SelectedBoundary) : Set where
  field
    selectedOriginalIsFilmedEarthReel :
      Original.SelectedBoundary.originalConfiguration b
        ≡ Bidi.filsingerEarthNarration

-- No inhabitant of the candidate is manufactured from a reel description.
-- The Filsinger portable source is a different original Configuration.
filmedEarthIsNotPortable :
  Bidi.filsingerEarthNarration ≡ Bidi.filsingerPortableProposal →
  Bidi.Contradiction
filmedEarthIsNotPortable = Bidi.earthNotPortable

-- The three-terminal passive, reciprocal *hypothetical* conductance graph.
-- Currents are positive INTO the graph. All common-mode voltages are gauge.
currentA : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
currentA gAB gAC a b c =
  gAB * (a - b) + gAC * (a - c)

currentB : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
currentB gAB gBC a b c =
  (- (gAB * (a - b))) + gBC * (b - c)

currentC : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
currentC gAC gBC a b c =
  (- (gAC * (a - c))) - gBC * (b - c)

threeContactKCL :
  ∀ gAB gAC gBC a b c →
  (currentA gAB gAC a b c + currentB gAB gBC a b c)
    + currentC gAC gBC a b c ≡ 0ℚ
threeContactKCL = solve-∀

terminalWork : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
terminalWork gAB gAC gBC a b c =
  (a * currentA gAB gAC a b c
    + b * currentB gAB gBC a b c)
    + c * currentC gAC gBC a b c

edgeWork : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
edgeWork gAB gAC gBC a b c =
  gAB * ((a - b) * (a - b))
    + gAC * ((a - c) * (a - c))
    + gBC * ((b - c) * (b - c))

threeContactWorkIsSumOfThreeEdges :
  ∀ gAB gAC gBC a b c →
  terminalWork gAB gAC gBC a b c
    ≡ edgeWork gAB gAC gBC a b c
threeContactWorkIsSumOfThreeEdges = solve-∀

-- Source-shaped negative control: identical A/B meter pair, unobserved
-- electrode C differing. In unit (arbitrary) conductances the *actual*
-- total passive work is respectively 2 and 3/2. The finite tag below
-- encodes those work values in half-units without making a meter claim.
data ThirdContactFixture : Set where
  thirdAtZero thirdAtHalf : ThirdContactFixture

pairDisplayHalfUnits : ThirdContactFixture → Nat
pairDisplayHalfUnits thirdAtZero = 2
pairDisplayHalfUnits thirdAtHalf = 2

networkWorkHalfUnits : ThirdContactFixture → Nat
networkWorkHalfUnits thirdAtZero = 4
networkWorkHalfUnits thirdAtHalf = 3

samePairDisplay :
  pairDisplayHalfUnits thirdAtZero
    ≡ pairDisplayHalfUnits thirdAtHalf
samePairDisplay = refl

differentTotalNetworkWork :
  networkWorkHalfUnits thirdAtZero
    ≡ networkWorkHalfUnits thirdAtHalf → ⊥
differentTotalNetworkWork ()

-- More useful general claim: any proposed lookup of *only* one pair reading
-- fails for this fixture, since the same reading would have to encode two
-- distinct three-contact works. No source attribution is inferred.
noUniqueWorkMapFromSinglePairDisplay :
  (infer : Nat → Nat) →
  ((w : ThirdContactFixture) →
      infer (pairDisplayHalfUnits w) ≡ networkWorkHalfUnits w) → ⊥
noUniqueWorkMapFromSinglePairDisplay infer agrees =
  differentTotalNetworkWork
    (trans (sym (agrees thirdAtZero)) (agrees thirdAtHalf))

-- The original Earth circuit's actual E/H field, signed V/I, material
-- conductivity, chemical storage and current returns are separate F10/F15
-- evidence roles. A hypothetical network work identity cannot fill them.
