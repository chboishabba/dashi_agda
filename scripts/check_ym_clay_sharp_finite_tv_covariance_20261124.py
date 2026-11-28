from fractions import Fraction
from itertools import product


def corners(a, b):
    return (
        (-a) * (-b),
        (-a) * (1 - b),
        (1 - a) * (-b),
        (1 - a) * (1 - b),
    )


def expectation(weights, observable):
    return sum((weights[s] * observable[s] for s in range(len(weights))), Fraction(0))


def covariance(weights, left, right):
    return (
        expectation(
            weights,
            tuple(left[s] * right[s] for s in range(len(weights))),
        )
        - expectation(weights, left) * expectation(weights, right)
    )


def total_variation(left, right):
    return sum(
        (abs(left[s] - right[s]) for s in range(len(left))),
        Fraction(0),
    ) / 2


def centered(weights, left, right, left_mean, right_mean):
    return expectation(
        weights,
        tuple(
            (left[s] - left_mean) * (right[s] - right_mean)
            for s in range(len(weights))
        ),
    )


def check_four_corner_width():
    for denominator in range(1, 9):
        for ai in range(denominator + 1):
            for bi in range(denominator + 1):
                a = Fraction(ai, denominator)
                b = Fraction(bi, denominator)
                values = corners(a, b)
                width = max(values) - min(values)
                assert width <= 1, (a, b, values, width)


def check_covariance_identity():
    weights = (
        (Fraction(1, 4), Fraction(3, 4)),
        (Fraction(2, 3), Fraction(1, 3)),
    )
    left = (Fraction(0), Fraction(1))
    right = (Fraction(1), Fraction(1, 2))
    half = Fraction(1, 2)
    left_means = [expectation(weights[i], left) for i in range(2)]
    right_means = [expectation(weights[i], right) for i in range(2)]
    gap = covariance(weights[0], left, right) - covariance(weights[1], left, right)
    centered_left_means = (
        centered(weights[0], left, right, left_means[0], right_means[0])
        - centered(weights[1], left, right, left_means[0], right_means[0])
    )
    centered_right_means = (
        centered(weights[0], left, right, left_means[1], right_means[1])
        - centered(weights[1], left, right, left_means[1], right_means[1])
    )
    identity = half * (centered_left_means + centered_right_means)
    assert gap == identity, (gap, identity)

    for left_values, right_values in product(
        ((Fraction(0), Fraction(1)), (Fraction(1, 3), Fraction(2, 3))),
        ((Fraction(1), Fraction(0)), (Fraction(1, 4), Fraction(3, 4))),
    ):
        left_means = [expectation(weights[i], left_values) for i in range(2)]
        right_means = [expectation(weights[i], right_values) for i in range(2)]
        gap = covariance(weights[0], left_values, right_values) - covariance(
            weights[1], left_values, right_values
        )
        centered_left_means = (
            centered(
                weights[0],
                left_values,
                right_values,
                left_means[0],
                right_means[0],
            )
            - centered(
                weights[1],
                left_values,
                right_values,
                left_means[0],
                right_means[0],
            )
        )
        centered_right_means = (
            centered(
                weights[0],
                left_values,
                right_values,
                left_means[1],
                right_means[1],
            )
            - centered(
                weights[1],
                left_values,
                right_values,
                left_means[1],
                right_means[1],
            )
        )
        identity = half * (centered_left_means + centered_right_means)
        assert gap == identity, (gap, identity)


def check_sharp_unit_bound():
    left = (Fraction(1, 4), Fraction(3, 4))
    right = (Fraction(3, 4), Fraction(1, 4))
    tv = total_variation(left, right)
    assert tv == Fraction(1, 2)
    for left_values, right_values in product(
        product((Fraction(0), Fraction(1, 2), Fraction(1)), repeat=2),
        product((Fraction(0), Fraction(1, 2), Fraction(1)), repeat=2),
    ):
        gap = abs(
            covariance(left, left_values, right_values)
            - covariance(right, left_values, right_values)
        )
        assert gap <= tv, (left_values, right_values, gap, tv)

    signed_left = tuple(2 * value - 1 for value in left_values)
    signed_right = tuple(2 * value - 1 for value in right_values)
    signed_gap = abs(
        covariance(left, signed_left, signed_right)
        - covariance(right, signed_left, signed_right)
    )
    assert signed_gap <= 4 * tv, (
        signed_left,
        signed_right,
        signed_gap,
        4 * tv,
    )


if __name__ == "__main__":
    check_four_corner_width()
    check_covariance_identity()
    check_sharp_unit_bound()
    print("PASS: finite sharp covariance-TV checks")
