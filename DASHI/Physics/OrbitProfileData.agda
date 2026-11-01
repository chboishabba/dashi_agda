module DASHI.Physics.OrbitProfileData where

open import Data.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.OrbitProfileComputedSignedPerm as OPCSP

shell1_p0_q4 : List Nat
shell1_p0_q4 = 8 ∷ []

shell2_p0_q4 : List Nat
shell2_p0_q4 = 24 ∷ []

shell1_p1_q2 : List Nat
shell1_p1_q2 = 8 ∷ 4 ∷ 2 ∷ []

shell2_p1_q2 : List Nat
shell2_p1_q2 = 4 ∷ []

shell1_p1_q3 : List Nat
shell1_p1_q3 = 24 ∷ 6 ∷ 2 ∷ []

shell2_p1_q3 : List Nat
shell2_p1_q3 = 16 ∷ 12 ∷ []

shell1_p2_q1 : List Nat
shell1_p2_q1 = 8 ∷ 4 ∷ 2 ∷ []

shell2_p2_q1 : List Nat
shell2_p2_q1 = 4 ∷ []

shell1_p2_q2 : List Nat
shell1_p2_q2 = 16 ∷ 16 ∷ 4 ∷ 4 ∷ []

shell2_p2_q2 : List Nat
shell2_p2_q2 = 4 ∷ 4 ∷ []

shell1_p3_q1 : List Nat
shell1_p3_q1 = OPCSP.shell1_p3_q1_computed

shell2_p3_q1 : List Nat
shell2_p3_q1 = OPCSP.shell2_p3_q1_computed

shell1_p4_q0 : List Nat
shell1_p4_q0 = 8 ∷ []

shell2_p4_q0 : List Nat
shell2_p4_q0 = 24 ∷ []
