module DASHI.Physics.RealConeInteriorPreservedShift where

open import Agda.Builtin.Nat using (Nat; _+_)

open import UFTC_Lattice as UFTC
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP

-- Interior/boundary predicates are left abstract here; this module wires Tᵣ.
record ConeInteriorShift {m k : Nat} : Set₁ where
  field
    C : UFTC.ConeInterior {X = RTC.Carrier (m + k)}

open ConeInteriorShift public

record ConeInteriorPreservedShift {m k : Nat} (CI : ConeInteriorShift {m} {k}) : Set₁ where
  field
    preserved :
      UFTC.ConeInteriorPreserved
        (TCP.Tᵣ {m} {k})
        (ConeInteriorShift.C CI)

open ConeInteriorPreservedShift public
