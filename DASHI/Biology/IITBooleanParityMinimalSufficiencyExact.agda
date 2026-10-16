module DASHI.Biology.IITBooleanParityMinimalSufficiencyExact where

------------------------------------------------------------------------
-- BOOLEAN MINIMAL-SUFFICIENCY SPINE
--
-- On the fixed recurrent fabric A'=C, B'=A, C'=mu(A,B), the independent
-- numerical scan finds XOR/XNOR are exactly the genuinely two-input Boolean
-- laws with positive 2023 system-phi in every state.
--
-- The structural explanation is stronger than balanced+essential dependence:
-- XOR/XNOR are exactly the BIPERMUTATIVE Boolean laws.  Fix either input and
-- the remaining input is transported bijectively to the output.  AND/OR/etc.
-- lose one input on at least one slice.  This is the exact local
-- minimal-sufficiency property used by the conjecture; IIT values remain a
-- separate numerical receipt.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- 1. All sixteen truth tables, bits ordered (00,01,10,11).
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
-- 2. Coarse classifiers retained for compatibility.
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
-- 3. Bipermutativity.  leftPermutative means that for EACH fixed right input,
-- changing the left input flips output; rightPermutative is the dual property.
------------------------------------------------------------------------

leftPermutative : BoolGate16 → Bool
leftPermutative g0000 = false
leftPermutative g0001 = false
leftPermutative g0010 = false
leftPermutative g0011 = true
leftPermutative g0100 = false
leftPermutative g0101 = false
leftPermutative g0110 = true
leftPermutative g0111 = false
leftPermutative g1000 = false
leftPermutative g1001 = true
leftPermutative g1010 = false
leftPermutative g1011 = false
leftPermutative g1100 = true
leftPermutative g1101 = false
leftPermutative g1110 = false
leftPermutative g1111 = false

rightPermutative : BoolGate16 → Bool
rightPermutative g0000 = false
rightPermutative g0001 = false
rightPermutative g0010 = false
rightPermutative g0011 = false
rightPermutative g0100 = false
rightPermutative g0101 = true
rightPermutative g0110 = true
rightPermutative g0111 = false
rightPermutative g1000 = false
rightPermutative g1001 = true
rightPermutative g1010 = true
rightPermutative g1011 = false
rightPermutative g1100 = false
rightPermutative g1101 = false
rightPermutative g1110 = false
rightPermutative g1111 = false

------------------------------------------------------------------------
-- 4. Parity/complement is the complete bipermutative Boolean class.
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

xorIsLeftPermutative : leftPermutative xorGate ≡ true
xorIsLeftPermutative = refl

xorIsRightPermutative : rightPermutative xorGate ≡ true
xorIsRightPermutative = refl

xnorIsBalanced : balanced xnorGate ≡ true
xnorIsBalanced = refl

xnorDependsOnLeft : dependsOnLeft xnorGate ≡ true
xnorDependsOnLeft = refl

xnorDependsOnRight : dependsOnRight xnorGate ≡ true
xnorDependsOnRight = refl

xnorIsLeftPermutative : leftPermutative xnorGate ≡ true
xnorIsLeftPermutative = refl

xnorIsRightPermutative : rightPermutative xnorGate ≡ true
xnorIsRightPermutative = refl

bipermutativeOnlyParity :
  (gate : BoolGate16) →
  leftPermutative gate ≡ true →
  rightPermutative gate ≡ true →
  ParityOrComplement gate
bipermutativeOnlyParity g0000 () _
bipermutativeOnlyParity g0001 () _
bipermutativeOnlyParity g0010 () _
bipermutativeOnlyParity g0011 _ ()
bipermutativeOnlyParity g0100 () _
bipermutativeOnlyParity g0101 () _
bipermutativeOnlyParity g0110 _ _ = xorParity
bipermutativeOnlyParity g0111 () _
bipermutativeOnlyParity g1000 () _
bipermutativeOnlyParity g1001 _ _ = xnorParity
bipermutativeOnlyParity g1010 () _
bipermutativeOnlyParity g1011 () _
bipermutativeOnlyParity g1100 _ ()
bipermutativeOnlyParity g1101 () _
bipermutativeOnlyParity g1110 () _
bipermutativeOnlyParity g1111 () _

------------------------------------------------------------------------
-- 5. Older equivalent finite characterization: balanced + essential in both
-- inputs also isolates parity/complement on the Boolean alphabet.
------------------------------------------------------------------------

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

record BooleanParityMinimalSufficiencyBoundary : Set where
  constructor boolean-parity-minimal-sufficiency-boundary
  field
    allSixteenTruthTablesRepresented : Bool
    parityAndComplementAreBipermutative : Bool
    anyOtherBipermutativeBooleanGateExists : Bool
    parityAndComplementAreEssentialBalanced : Bool
    kernelClassificationIsAnIITNumericalProof : Bool
    numericalIITReceiptRequiredSeparately : Bool

canonicalBooleanParityMinimalSufficiencyBoundary :
  BooleanParityMinimalSufficiencyBoundary
canonicalBooleanParityMinimalSufficiencyBoundary =
  boolean-parity-minimal-sufficiency-boundary
    true true false true false true
