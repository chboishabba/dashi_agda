# Clay #1499 — B1 unrestricted signed physical-payment NO-GO (classical real Fourier)

**15 November 2026. Decision:** `B1` is **RESOLVED BY REFUTATION**, not proved as a positive barrier. Under the user's explicit Python/SymPy mathematical acceptance protocol (native Agda/CI deferred), the *original unrestricted every-terminal R820/R821/R823/R824/R825 nonnegative selected signed-payment premise* has a fully specified classical real-Fourier counterexample. Therefore it is mathematically **not available** as the all-initial-data B proof lane. Other B routes (including W1, genuinely restricted hypotheses, error-controlled payments or new global continuation) remain OPEN.

## Exact source-owner theorem audit

Inspected the following original owners on the Clay #1499 work branch rather than trusting flags:

1. `NSTriadKNR650CompleteSignedW2HelicityRateRound820Exact.agda`: `At.completeFourHelicityPaymentRate margin = 2(9N_sep-Q_sep)+D_CC+6(2nu-margin)d`, and `actualR815RateIsFullR813CCTouchedViscousRate` gives the exact R815 packet equality. Its original nonnegative signed estimate flag is **false**, and stays false.
2. `NSTriadKNR650CompleteSignedFourHelicityBarrierRound821Exact.agda`: `completeFourHelicitySignedPayment cutoff terminal S = 0 <= integral_0^terminal completeFourHelicityPaymentRate(nu)`. The all-cutoff barrier compiler requires *this same signed payment at every terminal*, plus independent W1. It does not prove either.
3. `NSTriadKNR650SignedComparableReserveRound823Exact.agda`: `originalR823CompleteRateIsR853SelectedRate`, `originalR823IntegratedRateIsR853SelectedIntegral`, and `integratedReserveMinusDemand` identify the same rate/integral, with no added positive estimate. At `nu=margin=1`, `reserve=D_CC+6d`, `demand=2(Q_sep-9N_sep)`.
4. `NSTriadKNR650PhysicalCCGradedReserveRound824Exact.agda`: its *original-incidence*, not swapped-proxy, signed CC high/low decomposition is `D_CC=H_CC-L_CC`, and its complete rate is `Quadratic+High-Low`, with `Quadratic=6d`, `High=H_CC+18N_sep`, `Low=L_CC+2Q_sep`.
5. `NSTriadKNR650PhysicalReserveFeasibilityRound825Exact.agda`: the genuine `gradedReservePaysComplete`, `completePaymentRequiresGradedReserve` and `physicalReserveFalsifier` are exact same-packet implications/equivalences. Its `round825StrictPhysicalCounterexampleConstructed` remains **false** for the original `Q`-typed R408 packet.
6. `NSTriadKNR650CanonicalSelectedRateNormalFormRound853Exact.agda`: same live packet yields the selected `6(12 C_comm - P_crit + d)` at `nu=margin=1`, *not* the zero enstrophy-balance residual.

The third and sixth owners contain actual **Agda source proofs of same-packet algebraic equalities**, not a real-time `R408` inhabitant. Their identities are finite sums and algebra, and base change to physical real/complex Fourier coefficients supplies a coherent classical interpretation with genuine `sqrt(|k|²)` helical mode norms. This Python gate does **not** claim the historical rational Agda record has been constructed or kernel-checked.

## Exact finite physical counterexample and all-terminal conclusion

Use the *same* original 728-nonzero-mode, radius-four, real divergence-free R71 Galerkin solution with viscosity `nu=1` established in C1 and the literal same real-Fourier R853 rate independently reconstructed in C2. Its three positive seed modes are

```text
u_(3,0,0) = (0, 2+2i, -2-i)
u_(0,4,0) = (2+2i, 0, 2+2i)
u_(3,4,0) = (6i, -9i/2, -2+2i),
u_(-k)=conj(u_k), all other modes zero initially.
```

`check_clay_c2_r853_selected_rate_sympy_20261115.py` reconstructs the original exact 24 active projected-force components; eight complete R224 mixed and eight complete R230 commutator vectors; R692 `C(0)=-557627/125`; R847 `P(0)=0, d(0)=15834`. Thus the **actual selected** initial rate is

```text
r(0) = 6*(12*C(0)-P(0)+d(0)) = -28273644/125.
```

On the entire C1 complete-real 2,184-coordinate ball `||u||_infinity<=12`, the physical rate's source-constructed finite-product Lipschitz constant is `Lambda=618365778064115445891072` and the actual Galerkin field is bounded by `K=5032512`. Let `T=226189/3938540454339300631433585885184` be the **original** R854 time, not a replacement interval. The classical real Galerkin solution exists to `T` and for **every** `0<=t<=T`,

```text
r(t) <= r(0) + Lambda*K*t
     <= r(0) + Lambda*K*T < -19/125 < 0.
```

For **every real** `h` with `0<h<=T`, not only the exact terminal `T`, integration preserves the strict negative sign:

```text
integral_0^h r(t) dt < -(19/125)*h < 0.
```

The original R820, R823, and R825 algebraic same-packet normal forms identify the **identical real-Fourier integral**. Their unqualified universal nonnegative premise is therefore contradicted on the exact original physical Galerkin witness:

```text
NOT (forall real finite Galerkin solutions u,
     forall cutoffs N, forall h in [0,T_u]:
     0 <= completeFourHelicitySignedPaymentIntegral(u,N,h)).

For this witness and every 0<h<=T:
     integral_0^h signedRate(u(t))dt < 0,
     integratedReserve(u,h) < integratedDemand(u,h),
     quadraticIntegral(u,h)+highIntegral(u,h) < lowIntegral(u,h).
```

The R823/R825 strict reversals above are consequences of the original exact incidence decompositions, **not separate computations of sign at an invented representative**. The source note is [the B1 standalone executable](../../scripts/check_clay_b1_r820_r825_real_signed_payment_nogo_20261115.py) (Python 3, SymPy 1.14; Git blob `8efba6064c86c86fb29c5f4cbaac4a5598dfc313`). It imports the previously committed, source-reconstructed C2 checker; no arbitrary scalar `r` is supplied. It checks both of the original algebraic rate decompositions for unrestricted real symbols and exact physical initial/short-time arithmetic.

## Gate semantics, dependency and explicit exclusions

**B1 counting:** The previously open B1 **unrestricted nonnegative signed-payment candidate is terminally decided as FALSE** under the same user-approved Python/SymPy *classical physical-real* protocol used to close C1/C2. Count B1 as `CLOSED_REFUTED_UNRESTRICTED_REAL_FOURIER` **only as a resolved/falsified route**, never as a positive `round820CompleteSignedInequalityClosed` proof or universal global regularity. Existing Agda `round820CompleteSignedInequalityClosed`, `round825StrictPhysicalCounterexampleConstructed`, `round825SignedReserveProved`, `round825W1Proved`, and `round825ContinuumContinuationProved` all remain false. Historical original rational-typed R408 and globally quantified rational helical laws have no physical real-time inhabitant. Agda/Lean kernel acceptance and formal real-field base change remain **unverified**.

**B2 remains OPEN and BLOCKED on this exact route**: its W1 may be studied independently, but the original R821 nonnegative signed payment cannot be installed for every initial data/terminal. A mathematically valid replacement must either derive a different critical-energy inequality with quantitatively paid signed negative contributions, or impose a nonvacuous, physically justified restriction whose coverage is established before any all-data conclusion. A restriction excluding this initial state without proving its scope cannot yield Clay global regularity. Nothing about a finite Galerkin counterexample disproves or proves global existence for 3D NSE.

**Endpoint verdict:** 0/6 original Millennium endpoints. The 15-slot decision ledger now has P0, C1, C2 and B1 decided (B1 NEGATIVE): **4/15 resolved, 11 active**. The number of *positively proved mathematical B barriers* remains zero.
