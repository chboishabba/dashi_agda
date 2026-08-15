module DASHI.Physics.Closure.NSTriadKNLuoFiniteParaproductRangePartitionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- This module replaces an unstructured five-source label with literal shell
-- range witnesses.  For output shell q and fixed collar c, an input shell p is
-- tagged as
--
--   strict low:   suc (p+c) <= q,
--   comparable:   p <= q+c and q <= p+c,
--   strict high:  suc (q+c) <= p.
--
-- The supported non-low-low patterns are enumerated explicitly and mapped to
-- low-high, high-low, comparable or high-high.  The differentiated filter
-- commutator remains a fifth, non-triadic constructor.  There is no generic
-- remainder constructor.
--
-- The still-open analytic interface is the Fourier-support theorem proving
-- that every actual projected Navier-Stokes convolution term inhabits one of
-- these constructors and that the excluded low-low pattern cannot reach q.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_+_; _≤_)

record StrictLowRange (input output collar : Nat) : Set where
  constructor strictLowRange
  field
    lowWitness : suc (input + collar) ≤ output

record ComparableRange (input output collar : Nat) : Set where
  constructor comparableRange
  field
    belowUpperCollar : input ≤ output + collar
    aboveLowerCollar : output ≤ input + collar

record StrictHighRange (input output collar : Nat) : Set where
  constructor strictHighRange
  field
    highWitness : suc (output + collar) ≤ input

open StrictLowRange public
open ComparableRange public
open StrictHighRange public

data TriadicInteractionClass : Set where
  highHigh lowHigh highLow comparable : TriadicInteractionClass

data SupportedTriadRange
    (collar leftInput rightInput output : Nat) : Set where
  lowComparable :
    StrictLowRange leftInput output collar →
    ComparableRange rightInput output collar →
    SupportedTriadRange collar leftInput rightInput output

  lowStrictHigh :
    StrictLowRange leftInput output collar →
    StrictHighRange rightInput output collar →
    SupportedTriadRange collar leftInput rightInput output

  comparableLow :
    ComparableRange leftInput output collar →
    StrictLowRange rightInput output collar →
    SupportedTriadRange collar leftInput rightInput output

  strictHighLow :
    StrictHighRange leftInput output collar →
    StrictLowRange rightInput output collar →
    SupportedTriadRange collar leftInput rightInput output

  comparableComparable :
    ComparableRange leftInput output collar →
    ComparableRange rightInput output collar →
    SupportedTriadRange collar leftInput rightInput output

  comparableStrictHigh :
    ComparableRange leftInput output collar →
    StrictHighRange rightInput output collar →
    SupportedTriadRange collar leftInput rightInput output

  strictHighComparable :
    StrictHighRange leftInput output collar →
    ComparableRange rightInput output collar →
    SupportedTriadRange collar leftInput rightInput output

  strictHighStrictHigh :
    StrictHighRange leftInput output collar →
    StrictHighRange rightInput output collar →
    SupportedTriadRange collar leftInput rightInput output

classifySupportedTriad :
  ∀ {collar leftInput rightInput output} →
  SupportedTriadRange collar leftInput rightInput output →
  TriadicInteractionClass
classifySupportedTriad (lowComparable _ _) = lowHigh
classifySupportedTriad (lowStrictHigh _ _) = lowHigh
classifySupportedTriad (comparableLow _ _) = highLow
classifySupportedTriad (strictHighLow _ _) = highLow
classifySupportedTriad (comparableComparable _ _) = comparable
classifySupportedTriad (comparableStrictHigh _ _) = highHigh
classifySupportedTriad (strictHighComparable _ _) = highHigh
classifySupportedTriad (strictHighStrictHigh _ _) = highHigh

data FilteredInteractionRange
    (collar leftInput rightInput output : Nat) : Set where
  triadic :
    SupportedTriadRange collar leftInput rightInput output →
    FilteredInteractionRange collar leftInput rightInput output
  differentiatedCommutator :
    FilteredInteractionRange collar leftInput rightInput output

data FiveInteractionClass : Set where
  HH LH HL CC Com : FiveInteractionClass

classifyFilteredInteraction :
  ∀ {collar leftInput rightInput output} →
  FilteredInteractionRange collar leftInput rightInput output →
  FiveInteractionClass
classifyFilteredInteraction (triadic range) with classifySupportedTriad range
... | highHigh = HH
... | lowHigh = LH
... | highLow = HL
... | comparable = CC
classifyFilteredInteraction differentiatedCommutator = Com

record ParaproductRangeAuthorityBoundary : Set₁ where
  constructor paraproductRangeAuthorityBoundary
  field
    literalLowComparableHighRangesImplemented : Set
    eightSupportedTriadPatternsEnumerated : Set
    commutatorKeptNonTriadic : Set
    noGenericRemainderConstructor : Set
    actualFourierSupportExhaustivenessProved : Set
    lowLowOutputExclusionProved : Set

canonicalParaproductRangeAuthorityBoundary :
  ParaproductRangeAuthorityBoundary
canonicalParaproductRangeAuthorityBoundary =
  paraproductRangeAuthorityBoundary ⊤ ⊤ ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
