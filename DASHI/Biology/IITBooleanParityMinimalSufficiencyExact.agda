module DASHI.Biology.IITBooleanParityMinimalSufficiencyExact where

------------------------------------------------------------------------
-- BOOLEAN MINIMAL-SUFFICIENCY SPINE
--
-- The numerical IIT experiment on the fixed recurrent fabric
--
--   A' = C,  B' = A,  C' = mu(A,B)
--
-- scans all sixteen two-input Boolean truth tables.  The executable result is
-- kept in scripts/iit_boolean_gate_minimal_sufficiency.py.  This Agda owner
-- pays the independent finite structural fact behind that observation:
-- among the sixteen Boolean laws, the only laws that are simultaneously
--
--   * balanced (two zero outputs and two one outputs), and
--   * essential in BOTH inputs,
--
-- are XOR and XNOR.
--
-- Thus the kernel theorem does not manufacture an IIT value.  It identifies
-- the exact parity class whose members the numerical scan finds to be the only
-- genuinely two-input laws with state-independent positive 2023 system-phi on
-- the selected recurrent fabric.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- 1. All sixteen two-input Boolean truth tables.
-- Constructor bits are ordered (00,01,10,11).
------------------------------------------------------------------------

data BoolGate16 : Set where
  g0000 g0001 g0010 g0011 : BoolGate16
  g0100 g0101 g0110 g0111 : BoolGate16
  g1000 g1001 g1010 g1011 : BoolGate16
  g1100 g1101 g1110 g1111 : BoolGate16

xorGate : BoolGate16
xorGate = g0110

xnorGate : BoolGate16
xnorGate = g1001

------------------------------------------------------------------------
-- 2. Exact finite classifiers.
------------------------------------------------------------------------

balanced : BoolGate16 → Bool
balanced g0000 = false
balanced g0001 = false
balanced g0010 = false
balanced g0011 = true
balanced g0100 = false
balanced g0101 = true
balanced g0110 = true
balanced g0111 = false
balanced g1000 = false
balanced g1001 = true
balanced g1010 = true
balanced g1011 = false
balanced g1100 = true
balanced g1101 = false
balanced g1110 = false
balanced g1111 = false

dependsOnLeft : BoolGate16 → Bool
dependsOnLeft g0000 = false
dependsOnLeft g0001 = true
dependsOnLeft g0010 = true
dependsOnLeft g0011 = true
dependsOnLeft g0100 = true
dependsOnLeft g0101 = false
dependsOnLeft g0110 = true
dependsOnLeft g0111 = true
dependsOnLeft g1000 = true
dependsOnLeft g1001 = true
dependsOnLeft g1010 = false
dependsOnLeft g1011 = true
dependsOnLeft g1100 = true
dependsOnLeft g1101 = true
dependsOnLeft g1110 = true
dependsOnLeft g1111 = false

dependsOnRight : BoolGate16 → Bool
dependsOnRight g0000 = false
dependsOnRight g0001 = true
dependsOnRight g0010 = true
dependsOnRight g0011 = false
dependsOnRight g0100 = true
dependsOnRight g0101 = true
dependsOnRight g0110 = true
dependsOnRight g0111 = true
dependsOnRight g1000 = true
dependsOnRight g1001 = true
dependsOnRight g1010 = true
dependsOnRight g1011 = true
dependsOnRight g1100 = false
dependsOnRight g1101 = true
dependsOnRight g1110 = true
dependsOnRight g1111 = false

------------------------------------------------------------------------
-- 3. Parity/complement is the complete essential-balanced class.
------------------------------------------------------------------------

data ParityOrComplement : BoolGate16 → Set where
  xorParity : ParityOrComplement g0110
  xnorParity : ParityOrComplement g1001

xorIsBalanced : balanced xorGate ≡ true
xorIsBalanced = refl

xorDependsOnLeft : dependsOnLeft xorGate ≡ true
xorDependsOnLeft = refl

xorDependsOnRight : dependsOnRight xorGate ≡ true
xorDependsOnRight = refl

xnorIsBalanced : balanced xnorGate ≡ true
xnorIsBalanced = refl

xnorDependsOnLeft : dependsOnLeft xnorGate ≡ true
xnorDependsOnLeft = refl

xnorDependsOnRight : dependsOnRight xnorGate ≡ true
xnorDependsOnRight = refl

essentialBalancedOnlyParity :
  (gate : BoolGate16) →
  balanced gate ≡ true →
  dependsOnLeft gate ≡ true →
  dependsOnRight gate ≡ true →
  ParityOrComplement gate
essentialBalancedOnlyParity g0000 () _ _
essentialBalancedOnlyParity g0001 () _ _
essentialBalancedOnlyParity g0010 () _ _
essentialBalancedOnlyParity g0011 _ _ ()
essentialBalancedOnlyParity g0100 () _ _
essentialBalancedOnlyParity g0101 _ () _
essentialBalancedOnlyParity g0110 _ _ _ = xorParity
essentialBalancedOnlyParity g0111 () _ _
essentialBalancedOnlyParity g1000 () _ _
essentialBalancedOnlyParity g1001 _ _ _ = xnorParity
essentialBalancedOnlyParity g1010 _ () _
essentialBalancedOnlyParity g1011 () _ _
essentialBalancedOnlyParity g1100 _ _ ()
essentialBalancedOnlyParity g1101 () _ _
essentialBalancedOnlyParity g1110 () _ _
essentialBalancedOnlyParity g1111 () _ _

------------------------------------------------------------------------
-- 4. Authority boundary.
------------------------------------------------------------------------

record BooleanParityMinimalSufficiencyBoundary : Set where
  constructor boolean-parity-minimal-sufficiency-boundary
  field
    allSixteenTruthTablesRepresented : Bool
    parityAndComplementAreEssentialBalanced : Bool
    anyOtherEssentialBalancedBooleanGateExists : Bool
    kernelClassificationIsAnIITNumericalProof : Bool
    numericalIITReceiptRequiredSeparately : Bool

canonicalBooleanParityMinimalSufficiencyBoundary :
  BooleanParityMinimalSufficiencyBoundary
canonicalBooleanParityMinimalSufficiencyBoundary =
  boolean-parity-minimal-sufficiency-boundary
    true true false false true
