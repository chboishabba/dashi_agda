module DASHI.Physics.Gravity.KSW668AdS5TTModularRadialLadderConsumerExact where

------------------------------------------------------------------------
-- KSW XII: The original physical r is the 3D brane spatial radius,
-- whereas z is the EXTRA AdS5 normal coordinate. Never call the
-- eigenspectra of L3/L7/L11 a Kaluza-Klein mass spectrum.
--
-- Exterior-derivative calculus, checked independently by SymPy:
--    L_d = d_r² + (d-1)/r d_r, J=(1/r)d_r,
--    L_(d+2) J = J L_d, hence L_(d+4) J² = J² L_d.
-- In particular d=3 ->7 ->11 for ell0/2/4.
--
-- This module proves (without postulates!) how TWO genuine supplied
-- adjacent continuum intertwiners produce a nilpotent 3-channel
-- commuting SHIFT. Its two physical calculus premises are PARAMETERS.
-- This is NOT the C3 invertible label rotation (previously refuted),
-- NOT a boundary/finite-FV intertwiner, and NOT a relationship among
-- the three independent physical compact TT source amplitudes.
--
-- Distinct optional modular arithmetic: the CHOSEN Q(j)=j²/3 on Z3
-- defines Weil S=-i F/sqrt3 and T=diag(1,omega,omega), satisfying
-- S^4=1, S²=(ST)^3, T³=1 in exact SymPy. Q is not derived from the
-- original original AdS5 stress. A nontrivial 3D representation of
-- the WHOLE Monster is ruled out by minimal nontrivial degree 196883;
-- a restricted C3 subgroup is a different question.
--
-- Pinned Agda 2.9 kernel is UNRUN. No physical modular gravity weld.
------------------------------------------------------------------------
open import Agda.Builtin.Equality using (_≡_; refl)

data ThreeChannels (State : Set) : Set where
  channels : State → State → State → ThreeChannels State

module _
  {State : Set}
  (zeroState : State)
  (L3 L7 L11 J35 J711 : State → State)
  (L3zero : L3 zeroState ≡ zeroState)
  (J35zero : J35 zeroState ≡ zeroState)
  (J711zero : J711 zeroState ≡ zeroState)
  (rise35 : (f : State) → L7 (J35 f) ≡ J35 (L3 f))
  (rise711 : (f : State) → L11 (J711 f) ≡ J711 (L7 f))
  where

  originalRadialGenerator : ThreeChannels State → ThreeChannels State
  originalRadialGenerator (channels f0 f1 f2) =
    channels (L3 f0) (L7 f1) (L11 f2)

  originalDimensionRaisingShift : ThreeChannels State → ThreeChannels State
  originalDimensionRaisingShift (channels f0 f1 f2) =
    channels zeroState (J35 f0) (J711 f1)

  originalDimensionRaisingShiftCommutes :
    (u : ThreeChannels State) →
    originalRadialGenerator (originalDimensionRaisingShift u)
      ≡ originalDimensionRaisingShift (originalRadialGenerator u)
  originalDimensionRaisingShiftCommutes (channels f0 f1 f2)
    rewrite L3zero | rise35 f0 | rise711 f1 = refl

  originalDimensionRaisingShiftCubedZero :
    (u : ThreeChannels State) →
    originalDimensionRaisingShift
      (originalDimensionRaisingShift
        (originalDimensionRaisingShift u))
      ≡ channels zeroState zeroState zeroState
  originalDimensionRaisingShiftCubedZero (channels f0 f1 f2)
    rewrite J35zero | J711zero = refl

-- Source-covariant (N G) is not physical-source equivalence:
-- the original TT modal profiles S0/S2/S4 fail the generic J² map
-- on f(r)=r^10. Finite-interval/r=0 regularity, AdS Israel source,
-- dual Weyl, full Monster/VOA action and true z-KK spectral weld OPEN.
