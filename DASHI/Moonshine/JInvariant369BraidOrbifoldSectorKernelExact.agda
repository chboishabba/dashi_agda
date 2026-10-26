module DASHI.Moonshine.JInvariant369BraidOrbifoldSectorKernelExact where

-- Direct cross-pollination: native Moonshine Z/2 twisted/twining-sector
-- modular S/T, B3 Artin generators, and the exact C3 12-time braid word.
-- The reduction SL2(Z)->SL2(F2) loses the pure braid's monodromy.
-- This is a finite-sector theorem, not the analytic V^natural VOA action.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.MoonshineOrbifoldModularSectorActionExact as Orb
import DASHI.Moonshine.JInvariant369BraidModularGeneratorWeldExact as Mod
import DASHI.Biology.TriadicBraidDialecticExact as TriadicBraid

-- Orb.T(g,h)=(g,g+h) is the *lower* matrix mod 2.  The modular
-- upper shear T must be conjugated by the existing sector swap S.
sigmaOne : Orb.OrbifoldSector → Orb.OrbifoldSector
sigmaOne x = Orb.S (Orb.T (Orb.S x))

sigmaTwo : Orb.OrbifoldSector → Orb.OrbifoldSector
sigmaTwo = Orb.T

-- Over F2 each unipotent shear is involutive. This is NOT true in
-- B3 or SL2(Z); only their finite sector-action quotient is used.
sigmaOneInvolutive : (x : Orb.OrbifoldSector) →
  sigmaOne (sigmaOne x) ≡ x
sigmaOneInvolutive (Orb.sector Orb.zeroBit Orb.zeroBit) = refl
sigmaOneInvolutive (Orb.sector Orb.zeroBit Orb.oneBit) = refl
sigmaOneInvolutive (Orb.sector Orb.oneBit Orb.zeroBit) = refl
sigmaOneInvolutive (Orb.sector Orb.oneBit Orb.oneBit) = refl

sigmaTwoInvolutive : (x : Orb.OrbifoldSector) →
  sigmaTwo (sigmaTwo x) ≡ x
sigmaTwoInvolutive = Orb.TInvolutive

artinRelationOnOrbifoldSectors : (x : Orb.OrbifoldSector) →
  sigmaOne (sigmaTwo (sigmaOne x))
  ≡ sigmaTwo (sigmaOne (sigmaTwo x))
artinRelationOnOrbifoldSectors (Orb.sector Orb.zeroBit Orb.zeroBit) = refl
artinRelationOnOrbifoldSectors (Orb.sector Orb.zeroBit Orb.oneBit) = refl
artinRelationOnOrbifoldSectors (Orb.sector Orb.oneBit Orb.zeroBit) = refl
artinRelationOnOrbifoldSectors (Orb.sector Orb.oneBit Orb.oneBit) = refl

-- The two Artin shears generate the existing three-cycle on the
-- three nontrivial orbifold sectors, without creating any new fibre.
sigmaTwoAfterOneIsNativeST : (x : Orb.OrbifoldSector) →
  sigmaTwo (sigmaOne x) ≡ Orb.ST x
sigmaTwoAfterOneIsNativeST (Orb.sector Orb.zeroBit Orb.zeroBit) = refl
sigmaTwoAfterOneIsNativeST (Orb.sector Orb.zeroBit Orb.oneBit) = refl
sigmaTwoAfterOneIsNativeST (Orb.sector Orb.oneBit Orb.zeroBit) = refl
sigmaTwoAfterOneIsNativeST (Orb.sector Orb.oneBit Orb.oneBit) = refl

sigmaOneFixesFirstNonzero : sigmaOne Orb.twistedNoInsertion ≡ Orb.twistedNoInsertion
sigmaOneFixesFirstNonzero = refl

sigmaOneSwapsOtherTwo :
  sigmaOne Orb.untwistedTwining ≡ Orb.twistedTwining
sigmaOneSwapsOtherTwo = refl

sigmaTwoFixesFirstNonzero :
  sigmaTwo Orb.untwistedTwining ≡ Orb.untwistedTwining
sigmaTwoFixesFirstNonzero = refl

sigmaTwoSwapsOtherTwo :
  sigmaTwo Orb.twistedNoInsertion ≡ Orb.twistedTwining
sigmaTwoSwapsOtherTwo = refl

-- In the mod-2 quotient sigmaOne^-1=sigmaOne. Therefore the
-- previously recorded word (sigmaOne^-1 sigmaTwo)^3 has trivial
-- action on ALL four sectors, not only the three nontrivial ones.
recordedWordStep : Orb.OrbifoldSector → Orb.OrbifoldSector
recordedWordStep x = sigmaOne (sigmaTwo x)

recordedPureBraidSectorAction : Orb.OrbifoldSector → Orb.OrbifoldSector
recordedPureBraidSectorAction x =
  recordedWordStep (recordedWordStep (recordedWordStep x))

recordedPureBraidInvisibleToOrbifoldSector :
  (x : Orb.OrbifoldSector) → recordedPureBraidSectorAction x ≡ x
recordedPureBraidInvisibleToOrbifoldSector
  (Orb.sector Orb.zeroBit Orb.zeroBit) = refl
recordedPureBraidInvisibleToOrbifoldSector
  (Orb.sector Orb.zeroBit Orb.oneBit) = refl
recordedPureBraidInvisibleToOrbifoldSector
  (Orb.sector Orb.oneBit Orb.zeroBit) = refl
recordedPureBraidInvisibleToOrbifoldSector
  (Orb.sector Orb.oneBit Orb.oneBit) = refl

-- Nevertheless the native integral SL2(Z) image is nonidentity.
-- The congruence-level 3/9/27 behaviour is independently checked
-- by scripts/check_369_braid_modular_prior_art_weld.py.
sameWordHasNonidentityIntegralMonodromy :
  Mod.recordedBraidWord ≡ Mod.identity → ⊥
sameWordHasNonidentityIntegralMonodromy ()

-- NO promotion: an action on the *four labels* (g,h) is not an
-- action on constructed twisted VOA modules nor a gravity Hilbert space.


------------------------------------------------------------------------
-- 3. Generator-matched C3 strand-role / nonzero orbifold-sector codec.
--
-- This is an explicit equivariant bijection onto the three named nonzero
-- sectors; it is NOT an equivalence of the physical strands with orbifold
-- Hilbert states or modules.
------------------------------------------------------------------------

roleToNonzeroOrbifold :
  TriadicBraid.DialecticalStrandRole → Orb.OrbifoldSector
roleToNonzeroOrbifold TriadicBraid.thesisStrand =
  Orb.untwistedTwining
roleToNonzeroOrbifold TriadicBraid.mediatingStrand =
  Orb.twistedTwining
roleToNonzeroOrbifold TriadicBraid.antithesisStrand =
  Orb.twistedNoInsertion

roleSigmaOne :
  TriadicBraid.DialecticalStrandRole →
  TriadicBraid.DialecticalStrandRole
roleSigmaOne TriadicBraid.thesisStrand =
  TriadicBraid.mediatingStrand
roleSigmaOne TriadicBraid.mediatingStrand =
  TriadicBraid.thesisStrand
roleSigmaOne TriadicBraid.antithesisStrand =
  TriadicBraid.antithesisStrand

roleSigmaTwo :
  TriadicBraid.DialecticalStrandRole →
  TriadicBraid.DialecticalStrandRole
roleSigmaTwo TriadicBraid.thesisStrand =
  TriadicBraid.thesisStrand
roleSigmaTwo TriadicBraid.mediatingStrand =
  TriadicBraid.antithesisStrand
roleSigmaTwo TriadicBraid.antithesisStrand =
  TriadicBraid.mediatingStrand

roleSigmaOneIntertwines :
  (r : TriadicBraid.DialecticalStrandRole) →
  roleToNonzeroOrbifold (roleSigmaOne r)
  ≡ sigmaOne (roleToNonzeroOrbifold r)
roleSigmaOneIntertwines TriadicBraid.thesisStrand = refl
roleSigmaOneIntertwines TriadicBraid.mediatingStrand = refl
roleSigmaOneIntertwines TriadicBraid.antithesisStrand = refl

roleSigmaTwoIntertwines :
  (r : TriadicBraid.DialecticalStrandRole) →
  roleToNonzeroOrbifold (roleSigmaTwo r)
  ≡ sigmaTwo (roleToNonzeroOrbifold r)
roleSigmaTwoIntertwines TriadicBraid.thesisStrand = refl
roleSigmaTwoIntertwines TriadicBraid.mediatingStrand = refl
roleSigmaTwoIntertwines TriadicBraid.antithesisStrand = refl

roleC3 :
  TriadicBraid.DialecticalStrandRole →
  TriadicBraid.DialecticalStrandRole
roleC3 r = roleSigmaTwo (roleSigmaOne r)

roleC3IntertwinesExistingOrbifoldST :
  (r : TriadicBraid.DialecticalStrandRole) →
  roleToNonzeroOrbifold (roleC3 r)
  ≡ Orb.ST (roleToNonzeroOrbifold r)
roleC3IntertwinesExistingOrbifoldST
  TriadicBraid.thesisStrand = refl
roleC3IntertwinesExistingOrbifoldST
  TriadicBraid.mediatingStrand = refl
roleC3IntertwinesExistingOrbifoldST
  TriadicBraid.antithesisStrand = refl

-- The existing coarse observer kills the pure braid, while fine modular
-- levels retain a nontrivial matrix: the C3 strand-role codec must not be
-- promoted to the level-3/9/27 modular-curve lift without a new map.
