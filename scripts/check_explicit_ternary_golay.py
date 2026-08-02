#!/usr/bin/env python3
"""Independent finite oracle for the explicit ternary-Golay/Mathieu/UBP tranche.

This script deliberately uses only Python's standard library. It checks finite
claims independently of Agda reduction, while the Agda modules keep the
external group identifications and real-backend statements fail-closed.
"""

from __future__ import annotations

from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, product

A = (
    (2, 0, 2, 1, 1, 2),
    (2, 1, 1, 2, 0, 2),
    (2, 2, 0, 2, 1, 1),
    (2, 2, 1, 1, 2, 0),
    (2, 1, 2, 0, 2, 1),
    (0, 1, 1, 1, 1, 1),
)

SOURCE_PI_CF_50 = (
    3, 7, 15, 1, 292, 1, 1, 1, 2, 1,
    3, 1, 14, 2, 1, 1, 2, 2, 2, 2,
    1, 84, 2, 1, 1, 15, 3, 13, 1, 4,
    2, 6, 6, 99, 1, 2, 2, 6, 3, 5,
    1, 1, 6, 8, 1, 7, 1, 6, 1, 99,
)

CANONICAL_PI_CF_51 = (
    3, 7, 15, 1, 292, 1, 1, 1, 2, 1,
    3, 1, 14, 2, 1, 1, 2, 2, 2, 2,
    1, 84, 2, 1, 1, 15, 3, 13, 1, 4,
    2, 6, 6, 99, 1, 2, 2, 6, 3, 5,
    1, 1, 6, 8, 1, 7, 1, 2, 3, 7,
    1,
)

PUBLISHED_S = (0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1)
PUBLISHED_T = (1, 0, 11, 4, 3, 10, 7, 6, 9, 8, 5, 2)
PUBLISHED_SEED_HEXAD = frozenset((0, 1, 2, 3, 4, 6))
COORDINATE_TRANSPORT = (0, 9, 3, 1, 5, 7, 2, 10, 8, 11, 6, 4)
S_SIGNS = (1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2)
T_SIGNS = (1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2)


def encode(message: tuple[int, ...]) -> tuple[int, ...]:
    parity = tuple(
        sum(message[row] * A[row][column] for row in range(6)) % 3
        for column in range(6)
    )
    return message + parity


def dot(left: tuple[int, ...], right: tuple[int, ...]) -> int:
    return sum(a * b for a, b in zip(left, right, strict=True)) % 3


def convergent(coefficients: tuple[int, ...]) -> Fraction:
    p_prev_prev, p_prev = 0, 1
    q_prev_prev, q_prev = 1, 0
    for coefficient in coefficients:
        p_prev_prev, p_prev = p_prev, coefficient * p_prev + p_prev_prev
        q_prev_prev, q_prev = q_prev, coefficient * q_prev + q_prev_prev
    return Fraction(p_prev, q_prev)


def observer_constant(pi_approximation: Fraction) -> Fraction:
    return pi_approximation / (pi_approximation * pi_approximation + 2)


def compose(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(left[right[index]] for index in range(len(left)))


def inverse(permutation: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * len(permutation)
    for source, target in enumerate(permutation):
        result[target] = source
    return tuple(result)


def power(permutation: tuple[int, ...], exponent: int) -> tuple[int, ...]:
    result = tuple(range(len(permutation)))
    for _ in range(exponent):
        result = compose(permutation, result)
    return result


def act_support(support: frozenset[int], permutation: tuple[int, ...]) -> frozenset[int]:
    return frozenset(permutation[index] for index in support)


def transport_permutation(permutation: tuple[int, ...], transport: tuple[int, ...]) -> tuple[int, ...]:
    return compose(transport, compose(permutation, inverse(transport)))


def support_orbit(seed: frozenset[int], generators: tuple[tuple[int, ...], ...]) -> set[frozenset[int]]:
    seen = {seed}
    queue = deque((seed,))
    while queue:
        support = queue.popleft()
        for generator in generators:
            image = act_support(support, generator)
            if image not in seen:
                seen.add(image)
                queue.append(image)
    return seen


def permutation_group(generators: tuple[tuple[int, ...], ...]) -> set[tuple[int, ...]]:
    identity = tuple(range(len(generators[0])))
    seen = {identity}
    queue = deque((identity,))
    while queue:
        element = queue.popleft()
        for generator in generators:
            image = compose(generator, element)
            if image not in seen:
                seen.add(image)
                queue.append(image)
    return seen


Monomial = tuple[tuple[int, ...], tuple[int, ...]]


def compose_monomial(left: Monomial, right: Monomial) -> Monomial:
    left_permutation, left_signs = left
    right_permutation, right_signs = right
    result_permutation = compose(left_permutation, right_permutation)
    result_signs = [1] * len(result_permutation)
    for index in range(len(result_permutation)):
        target = result_permutation[index]
        middle = right_permutation[index]
        result_signs[target] = left_signs[target] * right_signs[middle] % 3
    return result_permutation, tuple(result_signs)


def act_monomial(word: tuple[int, ...], monomial: Monomial) -> tuple[int, ...]:
    permutation, signs = monomial
    result = [0] * len(word)
    for source, value in enumerate(word):
        target = permutation[source]
        result[target] = signs[target] * value % 3
    return tuple(result)


def monomial_group(generators: tuple[Monomial, ...]) -> set[Monomial]:
    identity: Monomial = (tuple(range(12)), (1,) * 12)
    seen = {identity}
    queue = deque((identity,))
    while queue:
        element = queue.popleft()
        for generator in generators:
            image = compose_monomial(generator, element)
            if image not in seen:
                seen.add(image)
                queue.append(image)
    return seen


def row_reduce(vectors: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    matrix = [list(vector) for vector in vectors if any(vector)]
    pivot_row = 0
    for column in range(6):
        pivot = next((row for row in range(pivot_row, len(matrix)) if matrix[row][column] % 3), None)
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        inverse_pivot = 1 if matrix[pivot_row][column] == 1 else 2
        matrix[pivot_row] = [inverse_pivot * value % 3 for value in matrix[pivot_row]]
        for row in range(len(matrix)):
            if row == pivot_row:
                continue
            factor = matrix[row][column] % 3
            if factor:
                matrix[row] = [
                    (value - factor * pivot_value) % 3
                    for value, pivot_value in zip(matrix[row], matrix[pivot_row], strict=True)
                ]
        pivot_row += 1
        if pivot_row == len(matrix):
            break
    return [tuple(row) for row in matrix if any(row)]


def induced_message_matrix(monomial: Monomial) -> tuple[tuple[int, ...], ...]:
    rows = []
    for basis_index in range(6):
        message = tuple(1 if index == basis_index else 0 for index in range(6))
        transformed = act_monomial(encode(message), monomial)
        rows.append(transformed[:6])
        assert encode(transformed[:6]) == transformed
    return tuple(rows)


def apply_message_matrix(vector: tuple[int, ...], matrix: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    return tuple(
        sum(vector[row] * matrix[row][column] for row in range(6)) % 3
        for column in range(6)
    )


def cyclic_module_dimension(vector: tuple[int, ...], matrices: tuple[tuple[tuple[int, ...], ...], ...]) -> int:
    basis: list[tuple[int, ...]] = []
    queue = deque((vector,))
    while queue:
        candidate = queue.popleft()
        old_rank = len(row_reduce(basis))
        new_basis = row_reduce(basis + [candidate])
        if len(new_basis) == old_rank:
            continue
        basis = new_basis
        if len(basis) == 6:
            return 6
        for basis_vector in basis:
            for matrix in matrices:
                queue.append(apply_message_matrix(basis_vector, matrix))
    return len(basis)


def error_patterns_11_radius_2() -> list[tuple[int, ...]]:
    patterns = [(0,) * 11]
    for coordinate in range(11):
        for value in (1, 2):
            pattern = [0] * 11
            pattern[coordinate] = value
            patterns.append(tuple(pattern))
    for left, right in combinations(range(11), 2):
        for left_value, right_value in product((1, 2), repeat=2):
            pattern = [0] * 11
            pattern[left] = left_value
            pattern[right] = right_value
            patterns.append(tuple(pattern))
    return patterns


def add_words(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple((a + b) % 3 for a, b in zip(left, right, strict=True))


def main() -> None:
    messages = list(product(range(3), repeat=6))
    codewords = [encode(message) for message in messages]
    codeword_set = set(codewords)

    assert len(messages) == 729
    assert len(codeword_set) == 729
    assert all(codeword[:6] == message for message, codeword in zip(messages, codewords, strict=True))

    basis = [encode(tuple(1 if i == row else 0 for i in range(6))) for row in range(6)]
    assert all(dot(left, right) == 0 for left in basis for right in basis)
    assert all(dot(codeword, row) == 0 for codeword in codewords for row in basis)

    assert Counter(sum(value != 0 for value in word) for word in codewords) == Counter({9: 440, 6: 264, 12: 24, 0: 1})
    assert Counter((word.count(0), word.count(1), word.count(2)) for word in codewords) == Counter({
        (12, 0, 0): 1, (6, 6, 0): 22, (6, 0, 6): 22,
        (6, 3, 3): 220, (3, 6, 3): 220, (3, 3, 6): 220,
        (0, 12, 0): 1, (0, 6, 6): 22, (0, 0, 12): 1,
    })

    hexads = {
        frozenset(index for index, value in enumerate(word) if value != 0)
        for word in codewords if sum(value != 0 for value in word) == 6
    }
    assert len(hexads) == 132
    pentads = [frozenset(indices) for indices in combinations(range(12), 5)]
    assert Counter(sum(pentad <= hexad for hexad in hexads) for pentad in pentads) == Counter({1: 792})

    expected_punctured_distribution = Counter({8: 330, 5: 132, 6: 132, 9: 110, 11: 24, 0: 1})
    for punctured_coordinate in range(12):
        punctured_code = {word[:punctured_coordinate] + word[punctured_coordinate + 1:] for word in codewords}
        assert len(punctured_code) == 729
        assert Counter(sum(value != 0 for value in word) for word in punctured_code) == expected_punctured_distribution

    punctured_code = {word[:-1] for word in codewords}
    error_patterns = error_patterns_11_radius_2()
    assert len(error_patterns) == 243
    covered_words = {add_words(codeword, error) for codeword in punctured_code for error in error_patterns}
    assert len(covered_words) == 3**11
    assert len(punctured_code) * len(error_patterns) == 3**11

    derived_blocks = {frozenset(index for index in hexad if index != 11) for hexad in hexads if 11 in hexad}
    assert len(derived_blocks) == 66
    tetrads = [frozenset(indices) for indices in combinations(range(11), 4)]
    assert Counter(sum(tetrad <= block for block in derived_blocks) for tetrad in tetrads) == Counter({1: 330})

    published_hexads = support_orbit(PUBLISHED_SEED_HEXAD, (PUBLISHED_S, PUBLISHED_T))
    assert len(published_hexads) == 132
    transported_s = transport_permutation(PUBLISHED_S, COORDINATE_TRANSPORT)
    transported_t = transport_permutation(PUBLISHED_T, COORDINATE_TRANSPORT)
    transported_seed = act_support(PUBLISHED_SEED_HEXAD, COORDINATE_TRANSPORT)
    assert support_orbit(transported_seed, (transported_s, transported_t)) == hexads
    assert power(transported_s, 11) == tuple(range(12))
    assert power(transported_t, 2) == tuple(range(12))
    assert power(compose(transported_s, transported_t), 3) == tuple(range(12))

    permutation_elements = permutation_group((transported_s, transported_t))
    assert len(permutation_elements) == 95040
    assert sum(permutation[0] == 0 for permutation in permutation_elements) == 7920
    assert sum(permutation[0] == 0 and permutation[1] == 1 for permutation in permutation_elements) == 720
    assert 7920 // 12 == 660
    assert 720 != 660

    monomial_s = (transported_s, S_SIGNS)
    monomial_t = (transported_t, T_SIGNS)
    assert all(act_monomial(word, monomial_s) in codeword_set for word in codewords)
    assert all(act_monomial(word, monomial_t) in codeword_set for word in codewords)
    central_negation: Monomial = (tuple(range(12)), (2,) * 12)
    assert compose_monomial(monomial_t, monomial_t) == central_negation
    monomial_elements = monomial_group((monomial_s, monomial_t))
    assert len(monomial_elements) == 190080
    assert {permutation for permutation, _ in monomial_elements} == permutation_elements

    message_s = induced_message_matrix(monomial_s)
    message_t = induced_message_matrix(monomial_t)
    assert Counter(
        cyclic_module_dimension(vector, (message_s, message_t))
        for vector in product(range(3), repeat=6) if any(vector)
    ) == Counter({6: 728})

    canonical50 = CANONICAL_PI_CF_51[:50]
    assert SOURCE_PI_CF_50[:47] == canonical50[:47]
    assert SOURCE_PI_CF_50[47] == 6 and canonical50[47] == 2
    source_pi50 = convergent(SOURCE_PI_CF_50)
    canonical_pi50 = convergent(canonical50)
    canonical_pi51 = convergent(CANONICAL_PI_CF_51)
    assert source_pi50 == Fraction(183157143516396120473427579101, 58300729506452262642556705291)
    assert canonical_pi50 == Fraction(16397605394050964443746106649, 5219519906667074477262822481)
    assert canonical_pi51 == Fraction(18644210947563865148979297792, 5934636664705637943635533097)

    source_y = observer_constant(source_pi50)
    canonical_y = observer_constant(canonical_pi50)
    assert source_y - canonical_y == Fraction(
        2734787287797861895878337337413165344545354810381555572709194,
        1449569606998549182495542391376708973611508633517180526971395851214621946728005627560091575061157712043175668851961,
    )

    print("Exceptional ternary Golay/Mathieu/UBP oracle passed.")
    print("  code: 729 words, self-orthogonal generators, complete enumerator checked")
    print("  puncture: [11,6,5]_3 distribution and 243-sphere perfect coverage checked")
    print("  designs: S(5,6,12) and derived S(4,5,11) incidence checked")
    print("  M12: transported hexad action has order 95040; stabilizers 7920 and 720")
    print("  2.M12: signed lifts have order 190080 and irreducible 6D F3 action")
    print("  provenance: source/canonical pi and observer-constant fork checked")


if __name__ == "__main__":
    main()
