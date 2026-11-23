module DASHI.Analysis.RHQuartic128HeisenbergPairedSixSymplecticExact where

------------------------------------------------------------------------
-- REAL NATIVE 3B HEISENBERG MODEL: PAIRED TRANSLATION/DUAL SIGN ACTORS.
-- The six RH factor-labelled generators flip BOTH x_i and xi_i in F3,
-- leaving the central phase c unchanged. This is a genuine automorphism
-- of the SOURCE Heisenberg6 compose law, preserving its symplectic form.
-- The seventh SSP sign generator is an independent exterior factor.
-- These are C2^6 model automorphisms, NOT claimed to be elements of the
-- order-3 Monster 3B subgroup or its ACTUAL Monster normalizer.
-- The ORIGINAL RH W/sampleTest/zero action still has no such realization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Analysis.RHQuartic128SevenBitFaceCechGluingExact as RH128
import DASHI.Analysis.RHQuartic128Monster3BSSPSignedC2IntertwinerExact as Native
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP

mulSignPair : (mask : Bool) (x y : Trit) →
  H._*3_ (Native.actTrit mask x) (Native.actTrit mask y)
    ≡ H._*3_ x y
mulSignPair false x y = refl
mulSignPair true neg neg = refl
mulSignPair true neg zer = refl
mulSignPair true neg pos = refl
mulSignPair true zer neg = refl
mulSignPair true zer zer = refl
mulSignPair true zer pos = refl
mulSignPair true pos neg = refl
mulSignPair true pos zer = refl
mulSignPair true pos pos = refl

addSignPair : (mask : Bool) (x y : Trit) →
  Native.actTrit mask (G._+3_ x y)
    ≡ G._+3_ (Native.actTrit mask x) (Native.actTrit mask y)
addSignPair false x y = refl
addSignPair true neg neg = refl
addSignPair true neg zer = refl
addSignPair true neg pos = refl
addSignPair true zer neg = refl
addSignPair true zer zer = refl
addSignPair true zer pos = refl
addSignPair true pos neg = refl
addSignPair true pos zer = refl
addSignPair true pos pos = refl

maskX6 : RH128.BinarySeven → G.X6 → G.X6
maskX6 mask (G.x6 x0 x1 x2 x3 x4 x5) =
  G.x6 (Native.actTrit (RH128.a0 mask) x0)
       (Native.actTrit (RH128.a1 mask) x1)
       (Native.actTrit (RH128.a2 mask) x2)
       (Native.actTrit (RH128.a3 mask) x3)
       (Native.actTrit (RH128.b0 mask) x4)
       (Native.actTrit (RH128.c0 mask) x5)

maskX6Adds : (mask : RH128.BinarySeven) (x y : G.X6) →
  maskX6 mask (H.addX6 x y) ≡
    H.addX6 (maskX6 mask x) (maskX6 mask y)
maskX6Adds (RH128.binarySeven a0 a1 a2 a3 b0 c0 c1) (G.x6 x0 x1 x2 x3 x4 x5) (G.x6 y0 y1 y2 y3 y4 y5)
  rewrite addSignPair a0 x0 y0
        | addSignPair a1 x1 y1
        | addSignPair a2 x2 y2
        | addSignPair a3 x3 y3
        | addSignPair b0 x4 y4
        | addSignPair c0 x5 y5 = refl

maskDotInvariant : (mask : RH128.BinarySeven) (x y : G.X6) →
  H.dot6 (maskX6 mask x) (maskX6 mask y) ≡ H.dot6 x y
maskDotInvariant (RH128.binarySeven a0 a1 a2 a3 b0 c0 c1) (G.x6 x0 x1 x2 x3 x4 x5) (G.x6 y0 y1 y2 y3 y4 y5)
  rewrite mulSignPair a0 x0 y0
        | mulSignPair a1 x1 y1
        | mulSignPair a2 x2 y2
        | mulSignPair a3 x3 y3
        | mulSignPair b0 x4 y4
        | mulSignPair c0 x5 y5 = refl

maskSymplectic : RH128.BinarySeven → H.Symplectic12 → H.Symplectic12
maskSymplectic mask (H.symplectic12 x xi) =
  H.symplectic12 (maskX6 mask x) (maskX6 mask xi)

maskSymplecticInvariant :
  (mask : RH128.BinarySeven) (u v : H.Symplectic12) →
  H.symplecticPair (maskSymplectic mask u) (maskSymplectic mask v)
  ≡ H.symplecticPair u v
maskSymplecticInvariant mask (H.symplectic12 x xi) (H.symplectic12 y eta)
  rewrite maskDotInvariant mask x eta | maskDotInvariant mask y xi = refl

maskHeisenberg : RH128.BinarySeven → H.Heisenberg6 → H.Heisenberg6
maskHeisenberg mask (H.heisenberg6 quotient central) =
  H.heisenberg6 (maskSymplectic mask quotient) central

maskHeisenbergCompose :
  (mask : RH128.BinarySeven) (g h : H.Heisenberg6) →
  maskHeisenberg mask (H.compose g h)
  ≡ H.compose (maskHeisenberg mask g) (maskHeisenberg mask h)
maskHeisenbergCompose mask
  (H.heisenberg6 (H.symplectic12 x xi) c)
  (H.heisenberg6 (H.symplectic12 y eta) d)
  rewrite maskX6Adds mask x y
        | maskX6Adds mask xi eta
        | maskDotInvariant mask xi y = refl

maskHeisenbergLaw : (m n : RH128.BinarySeven) (g : H.Heisenberg6) →
  maskHeisenberg m (maskHeisenberg n g)
    ≡ maskHeisenberg (Native.maskXor m n) g
maskHeisenbergLaw
  (RH128.binarySeven ma0 ma1 ma2 ma3 mb0 mc0 mc1)
  (RH128.binarySeven na0 na1 na2 na3 nb0 nc0 nc1)
  (H.heisenberg6 (H.symplectic12 (G.x6 x0 x1 x2 x3 x4 x5) (G.x6 xi0 xi1 xi2 xi3 xi4 xi5)) c)
  rewrite Native.tritActLaw ma0 na0 x0
        | Native.tritActLaw ma1 na1 x1
        | Native.tritActLaw ma2 na2 x2
        | Native.tritActLaw ma3 na3 x3
        | Native.tritActLaw mb0 nb0 x4
        | Native.tritActLaw mc0 nc0 x5
        | Native.tritActLaw ma0 na0 xi0
        | Native.tritActLaw ma1 na1 xi1
        | Native.tritActLaw ma2 na2 xi2
        | Native.tritActLaw ma3 na3 xi3
        | Native.tritActLaw mb0 nb0 xi4
        | Native.tritActLaw mc0 nc0 xi5 = refl

SignedHeisenberg : Set
SignedHeisenberg = H.Heisenberg6 × SSP.SignedMultiplicity

maskSignedHeisenberg : RH128.BinarySeven → SignedHeisenberg → SignedHeisenberg
maskSignedHeisenberg mask (h , signed) =
  maskHeisenberg mask h , Native.actSigned (RH128.c1 mask) signed

maskSignedHeisenbergLaw : (m n : RH128.BinarySeven) (state : SignedHeisenberg) →
  maskSignedHeisenberg m (maskSignedHeisenberg n state)
  ≡ maskSignedHeisenberg (Native.maskXor m n) state
maskSignedHeisenbergLaw m n (h , signed)
  rewrite maskHeisenbergLaw m n h
        | Native.signedActLaw (RH128.c1 m) (RH128.c1 n) signed = refl

-- The 128 finite generator masks act on a full native Heisenberg-group
-- model with a seventh signed SSP factor.  This is STRONGER than merely
-- mapping into six ternary coordinates, and weaker than Monster recognition.
