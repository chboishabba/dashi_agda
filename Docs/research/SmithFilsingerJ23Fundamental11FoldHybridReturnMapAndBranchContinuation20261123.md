# J23 — exact 11-fold source clock, two-switch receiving orbit, and branch-aware continuation

**23 November 2026 | PR #1537, base master.** All numerical energy results below are from a **synthetic externally prescribed wave** with the controller OFF. The original source owner is the unchanged J12/J18/J19/J20/J21/J22 nine-state system; [new J23 native-source consumer](../../scripts/check_smith_filsinger_j23_fundamental_11fold_poincare_20261123.py) imports the pinned original Python files. Retain original Smith/Filsinger attribution, distinguish Duga/HAARP/SURA and Maxwell owners. No original device pin mapping or naturally supplied wave has been measured.

## Critical exact geometry: two-switch fundamental period, not 22 unrelated events

In the source-only case, driver amplitude is **zero**, the matched input quadratures and receiving-mode forcing both run at **omega=11/10** and the remaining coefficients/diode/spark thresholds are time-independent. Native J12 observation length is **T=20*pi**. Therefore

    tau=2*pi/omega=20*pi/11,     T=11*tau,     omega*T=22*pi.

SymPy checks the source quadrature equality at t and t+tau symbolically, not numerically. The hybrid flow on the extended (nine-state, on/off spark) carrier is tau-periodic; its original 20*pi stroboscopic map equals **eleven compositions** of the tau map. For an actual tau-periodic fixed point with restored mode, its differentiable return derivative satisfies **M_T=(M_tau)^11** and its work ledger sums eleven identical tau-period work packets. This is a theorem about composition **conditional on existence of a fixed point**; it is not already a rigorous existence proof. If the driver is ON, its sin(t) forcing does NOT have period tau, so do not apply this reduction to source-plus-driver or driver-only fixtures. Preserve the physical time coordinate and the distinct integer subperiod index n=0,...,10.

The numerical J22 orbit has 11 repeated off/on pairs; the corrected tau map sees **two** events, off at about 3.49129272117 and on at about 3.51534047913. Their separation is 0.02404775795; the positive direction-corrected slopes are about 0.09203613 and 0.14773999. The state/mode returns at tau to numerical tolerance, not just T.

## Independent local replay; numerical scope

The attached local J22 independent NumPy/SciPy system was actually executed, and one-period J23 reduction, two-event saltation/shooting, high-accuracy energy replay, and finite five-parameter corner continuations were newly executed. The new native-source **J23 checker was committed and inspected but has not been byte-identically executed** against original J18–J22 committed source. Do not mark that native acceptance gate as completed. No GitHub CI/Actions or Agda kernel.

| Numerical diagnostic | Independent J23 result |
| --- | ---: |
| Initial J22 corrected root -> tau-map closure | 9.56e-12 |
| After additional tau-map shooting | 1.95e-14 |
| Separate stringent tau-cycle work solver closure | 1.63e-9 |
| Original T-map event count | 22 |
| Fundamental tau-map event count | **2** |
| Relative matrix difference ||M_T-M_tau^11|| / ||M_T|| | **3.49475e-10** |
| rho(M_tau) | **0.888103794** |
| rho(M_T) | **0.271082187** |
| Smallest singular value sigma_min(I-M_tau) | **0.119506176** |
| 2-norm of inverse (I-M_tau), numerical | about **8.367768** |
| Source-only HF load / incident | **51.4619325%** |
| Source-only captured wave / incident | **65.6734455%** |

Strict independent one-tau energy ledger: incident **8.22526076576**, outgoing **2.82344861707**, net received **5.40181214869**, HF load **4.23287814040**, driver **0**. Over T=11*tau, incident **90.47786842339**, HF load **46.56165955429**. The 11-fold ledger differs in the HF-load channel by about **9.90e-9** work units due to numerical integration. Maximum discrepancy of all 22 long-window spark event times against two-event-plus-n*tau reconstruction is about **2.80e-8**. The structural composition and 11-fold scaling are mathematical identities, while those discrepancies are finite-precision diagnostics.

## Large-bite finite five-dimensional continuation

We varied **five independent native coefficients** around the J22 point while maintaining driver OFF: gamma_rad=0.015, gamma_internal=0.0002, k=0.35, kh=2.0, Gload=0.52. Both signed ends of each parameter were tested in all **32 corners** of two nested boxes. The main wider box used:

    |delta gamma_rad| <= 0.0001
    |delta gamma_internal| <= 0.00005
    |delta k| <= 0.0005
    |delta kh| <= 0.0005
    |delta Gload| <= 0.0005

**32/32 wider-box endpoints passed** a native-equation *independent* two-switch hybrid shooting map, strict standalone energy replay and ordered off/on validation. **14/32 corners needed warm quarter-step homotopy**, rather than a direct centre-seeded shoot, to recover the two-event root. A 21-point one-dimensional warm path also reached the formerly failing far corner with two events at each tested step. A four-event transient obtained by starting at the wrong seed is therefore **NOT evidence of nonexistence** of the intended periodic orbit or a proven saddle-node / switching bifurcation.

| Observed over 32 wider-cube corners | Min | Max |
| --- | ---: | ---: |
| Load / incident fraction | **0.512842882** | **0.516382587** |
| Wave capture fraction | 0.653886939 | 0.659541691 |
| Direction-corrected crossing slope | **0.083793556** | 0.099998732 |
| OFF-to-ON event separation | **0.023631027** | 0.024489962 |
| Fundamental spectral radius | 0.887229138 | **0.888982008** |
| sigma_min(I-M_tau) | **0.118725652** | 0.120286387 |
| Independent work solver state closure | 7.74e-11 | 4.70e-9 |
| Absolute signed energy residual | 3.84e-11 | 3.93e-11 |
| Absolute storage drift | 1.59e-9 maximum |  |
| Short return-map residual after shooting | 4.2e-14 | 1.404e-10 |

The *tight* box with each half-width reduced to one-tenth also passed all 32 cold-seed corners, 32/32. **Corner checks and finite sampled homotopies are NOT an interval enclosure across every point in the box.** Do not call these bounded parameter results rigorous existence/uniqueness or a certified physical optimum. The source-only loading is dimensionless model output, not measured Earth-to-device energy.

## J22 correction and negative controls

The previous J22/Gload or kh neighbour test correctly reported *different trajectories with zero, 32/34 or 44 switching events from its selected seed/convergence process*. It did **not** prove that a two-switch (22-over-T) tau-periodic root cannot coexist at those parameters. A basin-of-attraction or branch-selection failure is logically distinct from a saddle-node or loss of all admissible periodic roots. J23 explicitly exhibits this distinction for one previously failing wider-box direction. Full uniqueness, branch merging and physical switching feasibility remain open.

The earlier **positive-coil-loss bound** is unchanged: under restored nonlinear HF capacitor storage and source-only energy conservation, W_coil >= R_coil Gload W_load, giving eta_load/incident <=1/(1+R_coil Gload)<1 for positive coil resistance and nonzero load. The J23 clock/continuation result cannot promote an impossible finite-loss 100% transfer claim.

## Next rigorous interval fixed-point certificate — exact theorem shape, OPEN producer

Let P_tau(x) be the one-tau, two-event hybrid Poincare map on a fixed spark-state branch and H(x)=P_tau(x)-x. Let x0 be a rational centre, B an interval box of radius r and C a rational approximate inverse of I-DP_tau(x0). The Newton-type map N(x)=x+C H(x) has a unique fixed point in B provided **validated interval evaluations** establish both:

    sup_{x in B} || I-C(I-DP_tau(x)) || <= q < 1,
    || C H(x0) || <= (1-q) r,

with the switching itinerary and all diode active sets certified, all threshold crossings isolated and transverse with nonzero interval denominator, and the same initial and final mode. Only then is Banach inclusion/contraction a proof of a tau-periodic orbit. The current approximate sigma_min=0.119506 is a promising conditioning diagnostic, **not** a rigorous lower bound valid over B.

Proof producer still required: outward-rounded interval/Taylor integration over one tau interval; rigorous diode/max guard splits; event root isolation and saltation denominator intervals; enclosure of DP_tau(B) and H(x0); inclusion of N(B) in B and an interval norm q<1. For a five-parameter neighbourhood, repeat the validated inequalities uniformly over the parameter box. Once certified, 11-fold composition transports exact existence and energy conservation from tau to the original T, without rebuilding 22 independent event certificates.

Original Filsinger FM physical pin edges remain 0/4 verified, original empirical energy roles 0/24. No verified natural/environmental wave source power, Duga/HAARP/SURA-to-Filsinger propagation or gravity effect. Record all these as **distinct** source-admission obligations.
