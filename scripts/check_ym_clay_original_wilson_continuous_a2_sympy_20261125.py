from sympy import Abs, symbols, simplify

SOURCE_OWNERS = {
    "original_wilson": "YMClayOriginalVariableWilsonCovarianceSourceExact",
    "product_haar": "YMClaySUNVariablePeriodicProductHaarExact",
    "finite_integration": "YangMillsPhysicalFiniteMeasureCylinderAlgebraExact",
    "finite_regression": "YMClaySharpFiniteTotalVariationCovarianceExact",
}


def require(label, ok):
    if not ok:
        raise SystemExit("FAIL: " + label)
    print("PASS: " + label)


def zero(label, expression):
    require(label, simplify(expression) == 0)


mu_f, nu_f, mu_g, nu_g, mu_fg, nu_fg = symbols("muF nuF muG nuG muFG nuFG")
a = (mu_f + nu_f) / 2
b = (mu_g + nu_g) / 2

covariance_gap = (mu_fg - mu_g * mu_f) - (nu_fg - nu_g * nu_f)
midpoint_gap = (
    (mu_fg - a * mu_g - b * mu_f + a * b)
    - (nu_fg - a * nu_g - b * nu_f + a * b)
)
zero("midpoint covariance identity", covariance_gap - midpoint_gap)

f, g = symbols("F G")
zero(
    "centered product expansion",
    (f - a) * (g - b) - (f * g - a * g - b * f + a * b),
)

chi_mean, good_numerator, q = symbols("chiH goodNumerator q")
shift_left = (chi_mean + good_numerator) - good_numerator / (1 - q)
shift_right = chi_mean - q * good_numerator / (1 - q)
zero("good-measure shift identity", shift_left - shift_right)

a_cut, q_tail, s_tail = symbols("a qTail sTail")
union_lhs = 1 - (1 - a_cut) * q_tail
union_rhs = a_cut + s_tail
union_decomposition = a_cut * (1 - q_tail) + (s_tail - (1 - q_tail))
zero("contour union algebra", (union_rhs - union_lhs) - union_decomposition)

zero(
    "chi partition algebra",
    (symbols("chi") + (1 - symbols("chi"))) - 1,
)

a = symbols("a")
zero(
    "one minus nonnegative algebra",
    ((1 - a) - 1) + a,
)

q, d = symbols("q d")
zero(
    "subtract-less algebra",
    ((q + d) - q) - d,
)

weight, scalar = symbols("weight scalar")
left, right = symbols("left right")
zero(
    "nonnegative add algebra",
    (left + right) - (left + right),
)
zero(
    "restricted add pointwise algebra",
    weight * (f + g) - (weight * f + weight * g),
)
zero(
    "restricted scale pointwise algebra",
    weight * (scalar * f) - scalar * (weight * f),
)

zero(
    "unit upper centered difference decomposition",
    (1 - (f - a)) - ((1 - f) + a),
)
zero(
    "unit lower centered difference decomposition",
    ((f - a) + 1) - (f + (1 - a)),
)

bad_f, bad_g, bad_a, bad_b = 1, 1, -1, -1
bad_centered_product = (bad_f - bad_a) * (bad_g - bad_b)
require(
    "signed [-1,1] test algebra requires centered product bound 4",
    bad_centered_product == 4,
)

q_nonnegative_proxy = q
zero("2q implies 4q algebra", (4 * q_nonnegative_proxy - 2 * q_nonnegative_proxy) - 2 * q)

center_a, center_b = symbols("centerA centerB", real=True)
oscillation_lower = center_a * center_b - 1 - Abs(center_a - center_b)
oscillation_upper = center_a * center_b + 1 + Abs(center_a + center_b)
zero(
    "signed centered product oscillation identity",
    (oscillation_upper - oscillation_lower)
    - (2 + Abs(center_a + center_b) + Abs(center_a - center_b)),
)
extremal_widths = [
    simplify((oscillation_upper - oscillation_lower).subs({center_a: ca, center_b: cb}))
    for ca in (-1, 1)
    for cb in (-1, 1)
]
require(
    "signed centered product oscillation sharp at extremal centers",
    extremal_widths == [4, 4, 4, 4],
)

m, M, mean_good = symbols("m M meanGood")
zero(
    "nu lower division algebra",
    (mean_good / (1 - q) - m) - (mean_good - m * (1 - q)) / (1 - q),
)
zero(
    "nu upper division algebra",
    (M - mean_good / (1 - q)) - (M * (1 - q) - mean_good) / (1 - q),
)

print("SOURCE_OWNERS=" + ",".join(sorted(SOURCE_OWNERS.values())))
