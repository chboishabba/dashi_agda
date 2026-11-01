module DASHI.HME.Generated.Witnesses where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import DASHI.HME.Trace

canonicalWitnesses : List CanonicalWitness
canonicalWitnesses = (record { traceId = "trace-demo-001" ; residueVector = (0.4082482904638631 ∷ 0.0 ∷ -0.4082482904638631 ∷ 0.8164965809277261 ∷ 0.0 ∷ 0.0 ∷ 0.0 ∷ 0.0 ∷ 0.0 ∷ 0.0 ∷ 0.0 ∷ 0.0 ∷ 0.0 ∷ 0.0 ∷ 0.0 ∷ []) ; basinId = 1 ; invariants = (( "entropy" , 1.0397207678399178 ) ∷ ( "mdl_cost" , 5.039720767839918 ) ∷ ( "hot" , 3.0 ) ∷ ( "cold" , 7.0 ) ∷ ( "basin" , 1.0 ) ∷ ( "similarity" , 0.21081851067789198 ) ∷ []) ; proofSignature = "" } ∷ [])

clusterAssignments : List Float
clusterAssignments = (0.0 ∷ [])

silhouette : Float
silhouette = 0.0

invarianceScore : Float
invarianceScore = 0.9401114206128133
