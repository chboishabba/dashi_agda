module DASHI.Moonshine.OggSSP2BEquivariantResidualQuotientExact where

------------------------------------------------------------------------
-- EQUIVARIANCE DESCENDS THROUGH A SURJECTIVE QUOTIENT
--
-- The preferred Co1 norm-weld route has
--
--   pi       : M -> V24
--   residual : M -> S300
--   descended: V24 -> S300
--
-- with descended (pi x) = residual x.  Once pi and residual are equivariant,
-- descended equivariance is not another source theorem: it follows by descent.
--
-- We package surjectivity by an explicit section so the theorem remains small
-- and constructive in Agda.  Concrete Co1 actions and the actual quotient chart
-- are supplied by the same-object owner downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong; sym; trans)

record EquivariantDescentData
    (G M V S : Set) : Set₁ where
  constructor equivariant-descent-data
  field
    pi : M -> V
    residual : M -> S
    descended : V -> S

    actM : G -> M -> M
    actV : G -> V -> V
    actS : G -> S -> S

    section : V -> M
    sectionRight : (v : V) -> pi (section v) ≡ v

    descent : (x : M) -> descended (pi x) ≡ residual x
    piEquivariant : (g : G) (x : M) ->
      pi (actM g x) ≡ actV g (pi x)
    residualEquivariant : (g : G) (x : M) ->
      residual (actM g x) ≡ actS g (residual x)

open EquivariantDescentData public

-- The descended map is equivariant automatically.  This is the Agda mirror of
-- Lean's `equivariant_of_surjective_descent` theorem.
descendedEquivariant :
  {G M V S : Set} ->
  (d : EquivariantDescentData G M V S) ->
  (g : G) ->
  (v : V) ->
  descended d (actV d g v) ≡ actS d g (descended d v)
descendedEquivariant d g v =
  let x = section d v in
  trans
    (cong (descended d)
      (cong (actV d g) (sym (sectionRight d v))))
    (trans
      (cong (descended d) (sym (piEquivariant d g x)))
      (trans
        (descent d (actM d g x))
        (trans
          (residualEquivariant d g x)
          (trans
            (cong (actS d g) (sym (descent d x)))
            (cong (actS d g)
              (cong (descended d) (sectionRight d v)))))))

-- Status theorem consumed by the focused regression/frontier.
equivariantDescentCompilerPaid : Bool
equivariantDescentCompilerPaid = true
