module DASHI.Mathematics.Complexity.PNPCookSectionSeekExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Mathematics.Complexity.PNPCookFlattenedPrefixExact as F
import DASHI.Mathematics.Complexity.PNPCookPlacedWindowAffineLengthExact as P
import DASHI.Mathematics.Complexity.PNPCookEndpointOffsetsExact as O
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as C
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as R
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as D
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as E
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitFrontier as Cursor
import DASHI.Mathematics.Complexity.CanonicalVirtualFormulaBitSourceExact as Lookup
import DASHI.Mathematics.Complexity.CNFCookPrefixTokenExact as Tokens

-- Original fixed-horizon source, not a separately compiled smaller tableau.
module Actual (machine : L.ConcreteTapeMachine) (steps cols : Nat)
  (sc : C.EnumerationCoverage (L.finiteState machine))
  (ac : C.EnumerationCoverage (L.finiteSymbol machine))
  (nonempty : R.NonemptyRuleTable machine)
  (initial : CNF.Bits (D.RowBitsWidth machine cols)) where

  module Rect = P.Rectangle machine steps cols sc ac nonempty
  module Accept = O.Acceptance machine steps cols sc ac

  transition = Global.liftTransitionCNF {machine} sc ac nonempty steps cols
  initialPart = E.initialEndpointCNF {machine} {steps} {cols} initial
  acceptPart = E.acceptingEndpointCNF {machine} {steps} {cols} sc ac
  whole = Global.globalCookLevinCNF sc ac nonempty steps cols initial
  endpoints = L.append initialPart acceptPart

  split : whole ≡ L.append transition endpoints
  split = trans (F.transitionSectionSplit sc ac nonempty steps cols initial)
    (cong (L.append transition) (F.placedAppendSame initialPart acceptPart))

  tWidth = Rect.J * (Rect.a * F.tri steps + Rect.c * steps)
    + Rect.b * steps * F.tri Rect.J
  iWidth = F.tri (D.RowBitsWidth machine cols)
    + 5 * D.RowBitsWidth machine cols + P.zeroCount initial

  transWidth : F.bodyWidth transition ≡ tWidth
  transWidth = Rect.transitionAffineLength

  initWidth : F.bodyWidth initialPart ≡ iWidth
  initWidth = P.initialWidthExact {machine} {steps} {cols} initial

  prefix = L.append transition initialPart
  prefixWidth : F.bodyWidth prefix ≡ tWidth + iWidth
  prefixWidth rewrite F.bodyWidthAppend transition initialPart
    | transWidth | initWidth = refl

  acceptSplit : whole ≡ L.append prefix acceptPart
  acceptSplit = trans split (sym (F.appendAssoc transition initialPart acceptPart))

  -- Exact arbitrary bit inside the endpoint suffix at the computed offset.
  initialSectionBit : ∀ k →
    Cursor.streamedCookBit sc ac nonempty steps cols initial (3 * tWidth + k)
    ≡ Lookup.lookupBit k (Tokens.cnfTokenBits endpoints)
  initialSectionBit k rewrite sym transWidth =
    F.streamedAtSplit sc ac nonempty steps cols initial transition endpoints k split

  acceptanceSectionBit : ∀ k →
    Cursor.streamedCookBit sc ac nonempty steps cols initial
      (3 * (tWidth + iWidth) + k)
    ≡ Lookup.lookupBit k (Tokens.cnfTokenBits acceptPart)
  acceptanceSectionBit k rewrite sym prefixWidth =
    F.streamedAtSplit sc ac nonempty steps cols initial prefix acceptPart k acceptSplit

  -- Attach acceptance arithmetic to the same source prefix, including
  -- the one witness clause and the original implication enumeration.
  aWidth = (2 + (F.tri cols + (Accept.gw + 3) * cols))
    + (P.column Accept.block * F.tri cols + P.constant Accept.block * cols)

  acceptWidth : F.bodyWidth acceptPart ≡ aWidth
  acceptWidth = Accept.acceptanceWidth

  allWidth : F.bodyWidth whole ≡ (tWidth + iWidth) + aWidth
  allWidth rewrite acceptSplit | F.bodyWidthAppend prefix acceptPart
    | prefixWidth | acceptWidth = refl

  -- Only one terminal TRUE survives; no extra TRUE at a section boundary.
  appendNil : (xs : CNF.CNF (E.ExtendedGlobalWidth machine steps cols)) →
    L.append xs [] ≡ xs
  appendNil [] = refl
  appendNil (x ∷ xs) rewrite appendNil xs = refl

  empty : CNF.CNF (E.ExtendedGlobalWidth machine steps cols)
  empty = []

  terminalSuffixBit : ∀ k →
    Cursor.streamedCookBit sc ac nonempty steps cols initial
      (3 * ((tWidth + iWidth) + aWidth) + k)
    ≡ Lookup.lookupBit k (Tokens.cnfTokenBits empty)
  terminalSuffixBit k rewrite sym allWidth =
    F.streamedAtSplit sc ac nonempty steps cols initial whole [] k (sym (appendNil whole))

-- StreamCut.streamedInterior owns the analogous arbitrary transition cut.
-- This module pays original section offsets only, not the compact inverse,
-- in-clause token selection, binary frame parsing or physical tape clock.
