module DASHI.Cognition.ZeroFibreContextuality where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.Base369ZeroFibre as Fibre
import DASHI.Cognition.CognitiveResearchSources as Sources

------------------------------------------------------------------------
-- Pointwise zero need not be globally trivial.
--
-- This finite triangle is a literal gluing obstruction: every edge admits a
-- local opposite-orientation section, but no two-valued global section can
-- satisfy all three edges.  It is the smallest exact model of the proposed
-- Minesweeper-like zero field.
--
-- Contextuality reference:
-- Samson Abramsky and Adam Brandenburger (2011),
-- "The sheaf-theoretic structure of non-locality and contextuality",
-- New Journal of Physics 13:113036,
-- DOI 10.1088/1367-2630/13/11/113036.
------------------------------------------------------------------------

contextualitySource : Sources.ResearchSource
contextualitySource = Sources.abramskyBrandenburgerContextuality

observeOrientation : Fibre.Orientation → BT.Trit
observeOrientation _ = BT.zero

allHiddenOrientationsObserveZero :
  (orientation : Fibre.Orientation) → observeOrientation orientation ≡ BT.zero
allHiddenOrientationsObserveZero Fibre.forward = refl
allHiddenOrientationsObserveZero Fibre.reverse = refl

flip : Fibre.Orientation → Fibre.Orientation
flip Fibre.forward = Fibre.reverse
flip Fibre.reverse = Fibre.forward

flipTwice : (orientation : Fibre.Orientation) → flip (flip orientation) ≡ orientation
flipTwice Fibre.forward = refl
flipTwice Fibre.reverse = refl

-- Three opposite transports around a triangle produce one residual flip.

loopHolonomy : Fibre.Orientation → Fibre.Orientation
loopHolonomy orientation = flip (flip (flip orientation))

loopHolonomyIsFlip : (orientation : Fibre.Orientation) →
  loopHolonomy orientation ≡ flip orientation
loopHolonomyIsFlip Fibre.forward = refl
loopHolonomyIsFlip Fibre.reverse = refl

forwardReturnsReversed : loopHolonomy Fibre.forward ≡ Fibre.reverse
forwardReturnsReversed = refl

reverseReturnsForward : loopHolonomy Fibre.reverse ≡ Fibre.forward
reverseReturnsForward = refl

------------------------------------------------------------------------
-- Local sections.
------------------------------------------------------------------------

record EdgeSection : Set where
  constructor edgeSection
  field
    source : Fibre.Orientation
    target : Fibre.Orientation
    transported : flip source ≡ target

open EdgeSection public

canonicalLocalSection : EdgeSection
canonicalLocalSection = edgeSection Fibre.forward Fibre.reverse refl

reverseLocalSection : EdgeSection
reverseLocalSection = edgeSection Fibre.reverse Fibre.forward refl

------------------------------------------------------------------------
-- Global section on the odd cycle.  The three local edge laws are jointly
-- inconsistent even though each endpoint projects to the same visible zero.
------------------------------------------------------------------------

record GlobalZeroSection : Set where
  constructor globalZeroSection
  field
    atA : Fibre.Orientation
    atB : Fibre.Orientation
    atC : Fibre.Orientation
    edgeAB : flip atA ≡ atB
    edgeBC : flip atB ≡ atC
    edgeCA : flip atC ≡ atA

open GlobalZeroSection public

noGlobalZeroSection : GlobalZeroSection → ⊥
noGlobalZeroSection
  (globalZeroSection Fibre.forward Fibre.forward c () edgeBC edgeCA)
noGlobalZeroSection
  (globalZeroSection Fibre.forward Fibre.reverse Fibre.forward edgeAB edgeBC ())
noGlobalZeroSection
  (globalZeroSection Fibre.forward Fibre.reverse Fibre.reverse edgeAB () edgeCA)
noGlobalZeroSection
  (globalZeroSection Fibre.reverse Fibre.forward Fibre.forward edgeAB () edgeCA)
noGlobalZeroSection
  (globalZeroSection Fibre.reverse Fibre.forward Fibre.reverse edgeAB edgeBC ())
noGlobalZeroSection
  (globalZeroSection Fibre.reverse Fibre.reverse c () edgeBC edgeCA)

record ContextualZeroField : Set where
  constructor contextualZeroField
  field
    edgeOne : EdgeSection
    edgeTwo : EdgeSection
    edgeThree : EdgeSection
    globalClosureImpossible : GlobalZeroSection → ⊥

canonicalContextualZeroField : ContextualZeroField
canonicalContextualZeroField = contextualZeroField
  canonicalLocalSection
  reverseLocalSection
  canonicalLocalSection
  noGlobalZeroSection

------------------------------------------------------------------------
-- Authority boundary.
--
-- The theorem above establishes a combinatorial global-section obstruction.
-- It does not yet supply measurement probabilities, a Born rule, spacelike
-- separation, no-signalling or a Bell-inequality violation.
------------------------------------------------------------------------

data NonclassicalityLevel : Set where
  nontrivialFibre
  nonfactorableConstraint
  noGlobalSection
  probabilisticBellViolation

establishedLevel : NonclassicalityLevel
establishedLevel = noGlobalSection
