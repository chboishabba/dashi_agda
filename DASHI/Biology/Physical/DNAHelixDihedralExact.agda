module DASHI.Biology.Physical.DNAHelixDihedralExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
-- J. D. Watson and F. H. C. Crick,
-- "Molecular Structure of Nucleic Acids: A Structure for Deoxyribose
-- Nucleic Acid", Nature 171 (1953), 737-738.
-- DOI: 10.1038/171737a0.
--
-- DASHI CONTRIBUTION
-- A finite exact helical skeleton: axial progress + cyclic phase + paired
-- complementary strand.  Rotation and reflection obey the dihedral relation
-- s r s = r^-1.  This is not a calibrated B-DNA geometry theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.DNAChemistryCarrier as DNA

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data Phase4 : Set where
  p0 p1 p2 p3 : Phase4

rotate : Phase4 → Phase4
rotate p0 = p1
rotate p1 = p2
rotate p2 = p3
rotate p3 = p0

rotateInv : Phase4 → Phase4
rotateInv p0 = p3
rotateInv p1 = p0
rotateInv p2 = p1
rotateInv p3 = p2

reflect : Phase4 → Phase4
reflect p0 = p0
reflect p1 = p3
reflect p2 = p2
reflect p3 = p1

halfTurn : Phase4 → Phase4
halfTurn p0 = p2
halfTurn p1 = p3
halfTurn p2 = p0
halfTurn p3 = p1

rotationInverseLaw : (p : Phase4) → rotateInv (rotate p) ≡ p
rotationInverseLaw p0 = refl
rotationInverseLaw p1 = refl
rotationInverseLaw p2 = refl
rotationInverseLaw p3 = refl

reflectionInvolutive : (p : Phase4) → reflect (reflect p) ≡ p
reflectionInvolutive p0 = refl
reflectionInvolutive p1 = refl
reflectionInvolutive p2 = refl
reflectionInvolutive p3 = refl

dihedralConjugation :
  (p : Phase4) → reflect (rotate (reflect p)) ≡ rotateInv p
dihedralConjugation p0 = refl
dihedralConjugation p1 = refl
dihedralConjugation p2 = refl
dihedralConjugation p3 = refl

halfTurnInvolutive : (p : Phase4) → halfTurn (halfTurn p) ≡ p
halfTurnInvolutive p0 = refl
halfTurnInvolutive p1 = refl
halfTurnInvolutive p2 = refl
halfTurnInvolutive p3 = refl

halfTurnCommutesWithRotation :
  (p : Phase4) → halfTurn (rotate p) ≡ rotate (halfTurn p)
halfTurnCommutesWithRotation p0 = refl
halfTurnCommutesWithRotation p1 = refl
halfTurnCommutesWithRotation p2 = refl
halfTurnCommutesWithRotation p3 = refl

------------------------------------------------------------------------
-- Discrete helical site.
------------------------------------------------------------------------

data Strand : Set where
  primary complementary : Strand

toggleStrand : Strand → Strand
toggleStrand primary = complementary
toggleStrand complementary = primary

toggleStrandInvolutive : (s : Strand) → toggleStrand (toggleStrand s) ≡ s
toggleStrandInvolutive primary = refl
toggleStrandInvolutive complementary = refl

record HelixSite : Set where
  constructor helixSite
  field
    base : DNA.DNABase
    phase : Phase4
    axialIndex : Nat
    strand : Strand

open HelixSite public

advance : HelixSite → HelixSite
advance (helixSite b p z s) = helixSite b (rotate p) (suc z) s

pairedSite : HelixSite → HelixSite
pairedSite (helixSite b p z s) =
  helixSite (DNA.complement b) (halfTurn p) z (toggleStrand s)

pairedSiteInvolutive : (x : HelixSite) → pairedSite (pairedSite x) ≡ x
pairedSiteInvolutive (helixSite DNA.A p z s)
  rewrite halfTurnInvolutive p | toggleStrandInvolutive s = refl
pairedSiteInvolutive (helixSite DNA.C p z s)
  rewrite halfTurnInvolutive p | toggleStrandInvolutive s = refl
pairedSiteInvolutive (helixSite DNA.G p z s)
  rewrite halfTurnInvolutive p | toggleStrandInvolutive s = refl
pairedSiteInvolutive (helixSite DNA.T p z s)
  rewrite halfTurnInvolutive p | toggleStrandInvolutive s = refl

pairedAdvanceCommutes :
  (x : HelixSite) → pairedSite (advance x) ≡ advance (pairedSite x)
pairedAdvanceCommutes (helixSite b p z s)
  rewrite halfTurnCommutesWithRotation p = refl

------------------------------------------------------------------------
-- Existing chemistry coordinate theorem: Watson-Crick complement preserves U
-- and flips the V axis in the exact UV chart.
------------------------------------------------------------------------

uvComplementReflection :
  (b : DNA.DNABase) →
  DNA.toUV (DNA.complement b) ≡ DNA.complementUV (DNA.toUV b)
uvComplementReflection = DNA.complement-UV-equivariant

-- Thus DNA has two separate exact structures here: cyclic helical advancement
-- and involutive complement/reflection.  We do not identify the DNA carrier
-- itself with C3 or with the abstract 369 phase scaffold.
