module DASHI.Biology.Cell.CellFejerAttractorBridge where

open import Agda.Primitive using (Level; lsuc)

import DASHI.Energy.Core as EC
import DASHI.Analysis.FejerSublevelInvariant as FSI
import DASHI.Biology.Cell.CellStateAttractor as CSA

------------------------------------------------------------------------
-- A full cell-state attractor family from environment-indexed Fejer sublevels.
--
-- Unlike the selected protein bridge, this adapter is indexed over every
-- environment and attractor admitted by the supplied family, so it constructs
-- the existing `CellStateAttractor` record directly.
------------------------------------------------------------------------

record CellFejerAttractorFamily
    {e : Level}
    (C : CSA.CoupledCellState)
    (Energy : Set e)
    (ES : EC.EnergySpace
      (CSA.CoupledCellState.CellState C)
      Energy)
    : Set (lsuc e) where
  field
    Attractor : Set

    InBasin :
      Attractor →
      CSA.CoupledCellState.CellState C →
      Set

    StableIn :
      CSA.CoupledCellState.Environment C →
      Attractor →
      Set

    basinCentre :
      CSA.CoupledCellState.Environment C →
      Attractor →
      CSA.CoupledCellState.CellState C

    radius :
      CSA.CoupledCellState.Environment C →
      Attractor →
      Energy

    fejerFamily :
      (environment : CSA.CoupledCellState.Environment C) →
      (attractor : Attractor) →
      StableIn environment attractor →
      FSI.FejerSublevelInvariant
        ES
        (CSA.CoupledCellState.step C environment)
        (basinCentre environment attractor)
        (InBasin attractor)
        (radius environment attractor)

open CellFejerAttractorFamily public

cellStateAttractorFromFejer :
  ∀ {e C Energy ES} →
  CellFejerAttractorFamily {e} C Energy ES →
  CSA.CellStateAttractor C
cellStateAttractorFromFejer F = record
  { Attractor = Attractor F
  ; InBasin = InBasin F
  ; StableIn = StableIn F
  ; forwardInvariant = λ environment attractor stable state member →
      FSI.fejerPreservesSublevel
        (fejerFamily F environment attractor stable)
        state
        member
  }
