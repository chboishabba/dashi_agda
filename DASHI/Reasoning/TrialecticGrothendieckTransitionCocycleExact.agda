module DASHI.Reasoning.TrialecticGrothendieckTransitionCocycleExact where

------------------------------------------------------------------------
-- CYCLIC TRIALECTIC TRANSITION COCYCLE AS AN ACTION 2-CELL
--
-- DASHI CONTRIBUTION
--
-- The concrete chart transitions are:
--
--   AB -> BC -> CA -> AB
--
-- each implemented by cyclic permutation of a T^9 CellDialectic.
-- Their threefold composite acts identically on every CellDialectic.
--
-- RelationalTransportActionTwoCellExact lets us retain that equality as a
-- proof-relevant 2-cell:
--
--   T_CA,AB o T_BC,CA o T_AB,BC  ==>  id_AB
--
-- and analogously for cycles based at BC and CA.
--
-- This is a concrete C3 transition-cocycle receipt on the three edge charts.
-- It is not a theorem that the full relational Grothendieck site already
-- carries a groupoid-valued pseudofunctor, prestack or effective stack.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.RelationalSelfDescentExact as Existing
import DASHI.Core.RelationalTransportGroupoidActionExact as Groupoid
import DASHI.Core.RelationalTransportActionTwoCellExact as TwoCell
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticGrothendieckTransportCoherenceExact as Transport

------------------------------------------------------------------------
-- 1. Three based cycle composites.
------------------------------------------------------------------------

cycleAtAB :
  Groupoid.RelTransportHom
    Cell.CellDialectic
    Existing.patchAB
    Existing.patchAB
cycleAtAB =
  Groupoid.composeHom
    Transport.transportCAtoAB
    (Groupoid.composeHom
      Transport.transportBCtoCA
      Transport.transportABtoBC)

cycleAtBC :
  Groupoid.RelTransportHom
    Cell.CellDialectic
    Existing.patchBC
    Existing.patchBC
cycleAtBC =
  Groupoid.composeHom
    Transport.transportABtoBC
    (Groupoid.composeHom
      Transport.transportCAtoAB
      Transport.transportBCtoCA)

cycleAtCA :
  Groupoid.RelTransportHom
    Cell.CellDialectic
    Existing.patchCA
    Existing.patchCA
cycleAtCA =
  Groupoid.composeHom
    Transport.transportBCtoCA
    (Groupoid.composeHom
      Transport.transportABtoBC
      Transport.transportCAtoAB)

------------------------------------------------------------------------
-- 2. Each based cycle has a 2-cell to identity.
------------------------------------------------------------------------

cycleAB2Cell :
  TwoCell.TransportAction2Cell
    cycleAtAB
    (Groupoid.identityHom Existing.patchAB)
cycleAB2Cell dialectic =
  Transport.rotateThreeIsIdentity dialectic

cycleBC2Cell :
  TwoCell.TransportAction2Cell
    cycleAtBC
    (Groupoid.identityHom Existing.patchBC)
cycleBC2Cell dialectic =
  Transport.rotateThreeIsIdentity dialectic

cycleCA2Cell :
  TwoCell.TransportAction2Cell
    cycleAtCA
    (Groupoid.identityHom Existing.patchCA)
cycleCA2Cell dialectic =
  Transport.rotateThreeIsIdentity dialectic

------------------------------------------------------------------------
-- 3. The canonical local sections satisfy the same cycles.
------------------------------------------------------------------------

canonicalABCycleCloses :
  Groupoid.forward cycleAtAB Cell.canonicalCellAB
  ≡ Cell.canonicalCellAB
canonicalABCycleCloses =
  cycleAB2Cell Cell.canonicalCellAB

canonicalBCCycleCloses :
  Groupoid.forward cycleAtBC Cell.canonicalCellBC
  ≡ Cell.canonicalCellBC
canonicalBCCycleCloses =
  cycleBC2Cell Cell.canonicalCellBC

canonicalCACycleCloses :
  Groupoid.forward cycleAtCA Cell.canonicalCellCA
  ≡ Cell.canonicalCellCA
canonicalCACycleCloses =
  cycleCA2Cell Cell.canonicalCellCA

------------------------------------------------------------------------
-- 4. Inverse orientation also closes using the explicit inverse homs.
------------------------------------------------------------------------

reverseCycleAtAB :
  Groupoid.RelTransportHom
    Cell.CellDialectic
    Existing.patchAB
    Existing.patchAB
reverseCycleAtAB =
  Groupoid.composeHom
    (Groupoid.inverseHom Transport.transportABtoBC)
    (Groupoid.composeHom
      (Groupoid.inverseHom Transport.transportBCtoCA)
      (Groupoid.inverseHom Transport.transportCAtoAB))

reverseCycleAB2Cell :
  TwoCell.TransportAction2Cell
    reverseCycleAtAB
    (Groupoid.identityHom Existing.patchAB)
reverseCycleAB2Cell
  (Cell.cell-dialectic left right synthesis) = refl

------------------------------------------------------------------------
-- 5. Higher-promotion boundary.
------------------------------------------------------------------------

data CyclicCocycleIsFullPrestackDescent : Set where
data CyclicCocycleSuppliesAllGrothendieckOverlapCoherence : Set where
data CyclicCocycleIsEffectiveStack : Set where

cyclicCocycleDoesNotAutoPromoteToPrestack :
  CyclicCocycleIsFullPrestackDescent → ⊥
cyclicCocycleDoesNotAutoPromoteToPrestack ()

cyclicCocycleDoesNotSupplyAllSiteCoherence :
  CyclicCocycleSuppliesAllGrothendieckOverlapCoherence → ⊥
cyclicCocycleDoesNotSupplyAllSiteCoherence ()

cyclicCocycleDoesNotAutoPromoteToEffectiveStack :
  CyclicCocycleIsEffectiveStack → ⊥
cyclicCocycleDoesNotAutoPromoteToEffectiveStack ()

record TrialecticGrothendieckTransitionCocycleBoundary : Set where
  constructor trialectic-grothendieck-transition-cocycle-boundary
  field
    threeBasedCycleCompositesConstructed : Bool
    actionTwoCellToIdentityAtAB : Bool
    actionTwoCellToIdentityAtBC : Bool
    actionTwoCellToIdentityAtCA : Bool
    reverseOrientationCycleConstructed : Bool
    canonicalSectionsCloseUnderCycle : Bool
    fullSitePseudofunctorCoherenceProved : Bool
    prestackDescentProved : Bool
    effectiveStackProved : Bool

canonicalTrialecticGrothendieckTransitionCocycleBoundary :
  TrialecticGrothendieckTransitionCocycleBoundary
canonicalTrialecticGrothendieckTransitionCocycleBoundary =
  trialectic-grothendieck-transition-cocycle-boundary
    true true true true true true false false false
