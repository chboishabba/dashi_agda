# J30B — exact six-guard augmented shooting determinant; J31 existence target

**23 November 2026 | Filsinger mathematical source owner PR #1537.** This is a finite-dimensional analytical theorem for the nine-state six-switch synthetic source-only model, not a proof that its numerical root is an exact periodic solution. The original source identity, physical pin and measured input-output energy obligations remain separate.

## Exact elimination theorem

Use the original source period `tau=20*pi/11`, with the six already isolated ordered nominal hybrid transitions. Define a **scheduled-switch** (rather than automatically switching) continuous nine-dimensional trajectory `X(t;x0,t1,...,t6)` by integrating the **original smooth source ODE on each of its seven known mode segments** and changing branch at the six supplied time arguments `t_j`. There is no instantaneous *state* reset; spark jumps change the vector field and require saltation sensitivity.

Let the fifteen unknowns be `z=(x0,t1,...,t6)`. Define a 9-dimensional return residual `R(z)=X(tau;z)-x0` and six scalar original guard residuals

    G_j(z)=g_j(X(t_j;z)),   j=1,...,6.

Each `g_j` is the original threshold guard, in one fixed signed orientation; for example the active diode forward guards are `u-b-V_d` or `v-b-V_d`, spark OFF uses `b-V_off`, and spark ON uses `b-V_on`. Explicit time dependence of the *forcing* is retained, but these thresholds have no explicit time coordinate. Each `G_j` depends on `t_k` only for `k<=j`, so `G_t` is **lower triangular**. Its diagonal is exactly the **pre-event signed crossing slope**

    (G_t)_{jj} = Dg_j(X(t_j)) . f_j^-(t_j,X(t_j)),

where `f_j^-` is the actual pre-event smooth vector field. Its diagonal is nonzero precisely under the original six transversality hypotheses; its determinant is their product.

The exact 15-by-15 block Jacobian is

    J = [ R_x   R_t ]
        [ G_x   G_t ].

Because `G_t` is invertible, left-multiply by a block unit-triangular matrix:

    [ I   -R_t G_t^(-1) ] J
    [ 0           I    ]

     = [ R_x - R_t G_t^(-1)G_x    0 ]
       [            G_x           G_t ].

Therefore

    det J = det G_t * det(R_x - R_t G_t^(-1) G_x).

Implicit differentiation of `G(x,t(x))=0` gives `t'(x)=-G_t^(-1)G_x`. Hence the upper-left Schur complement is **exactly the derivative of the original guard-resolved hybrid return residual**,

    R_x - R_t G_t^(-1)G_x = M_tau - I_9,

and consequently

    det J = (product of the six PRE-switch signed guard slopes) * det(M_tau-I_9).

The determinant sign depends on the chosen orientation of each guard (including whether the downward sign was negated to define a positive crossing margin). The nonvanishing and equivalence of invertibility do not. At diode guards the vector field is continuous, so their saltation matrices are the identity; the scheduled-mode Jacobian still changes branch across the guard. At the two spark switches the vector field jumps; the Schur complement automatically includes the original saltation terms through event-time sensitivity. No artificial state reset is permitted.

This formula does **not** assert that `M_tau` at the present chosen rational seed has been interval validated, and an exact return map at the seed is not a periodic monodromy at a fixed point. The previous numerical estimate `sigma_min(I-M_tau)≈0.1195` suggests a well-conditioned local inverse but is not a rigorous invertibility lower bound.

## Actual local exact symbolic acceptance

[Byte-identical locally executed SymPy checker](../../scripts/check_smith_filsinger_j30_six_guard_schur_20261123.py), Git blob `e7726e5f65e9e0be1dc18787c85de24ea5594f0a`, constructs a **nontrivial exact rational** 15-dimensional block matrix with a six-by-six lower triangular event derivative, nine-by-nine return derivative, nonzero off-diagonal coupling and exact inverse. It checks exact block elimination, determinant product and inverse identity without floating-point tolerances. **PASS** for this rational algebraic witness. The proof of the general formula above is the block elimination/implicit-function argument; the finite checker is a regression, **not** an interval certificate of the original physical equations.

## Why this changes the J31 roadmap

The original J24 sixth radius-1e-4 nine-coordinate event box has not been paid by J30 (its section projection encloses only 3/9). However **membership in that particular preselected J24 numerical event box is not logically necessary to prove an exact periodic orbit** using the full 15-variable augmented shooting theorem. The necessary alternative is to validate every original mode segment and guard on the proposed augmented rational box itself. This does not waive original-source identity, exact mode order, physical current branch, absence of extra crossings or six crossing slopes.

For `F(z)=(R(z),G(z))`, make a rational centre `z0` from the existing J23 numerical root and J29 event centres, choose a nonzero rational 15-dimensional box `B`, and a rational approximate inverse `C` of the **actual source-owned** fifteen-by-fifteen Jacobian. Certify with outward-rational validated smooth-segment IVP maps and original branch guards

    K(B) = z0 - C F(z0) + (I - C [DF(B)]) (B-z0)
            strictly contained in interior(B),

together with an applicable uniqueness/contraction bound. This pays the exact existence result **in one consolidated theorem**, without first forcing a long global IVP tube at the old rational seed through the last J24 numerical box.

A practical implementation can use seven short independently centred original-mode Taylor/Lohner segments, interface event-time variables and a single direct 15-dimensional interval Newton/Krawczyk inclusion, instead of repeatedly widening original nine-coordinate intervals over the entire source period. Preserve the signed 3-valued switching event directions (including downward crossing sign), and the original exact 11-fold source-clock identity `T=11 tau` only *after* a tau-periodic fixed point has actually been proved.

**Unpaid:** original augmented map `F(z0)` interval, true source Jacobian interval `[DF(B)]`, valid state/time box, strict inclusion, uniform 5-parameter family, naturally available HF wave and physical device input-output metrology. No GitHub CI/Agda kernel, no 100% useful-load energy or antigravity assertion.
