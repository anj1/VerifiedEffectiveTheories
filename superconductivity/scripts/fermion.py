"""Signed finite Fock-space matrix assembly for the superconductivity EFTs."""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations


def sector(orbitals, electrons):
    return [sum(1 << slot for slot in occupied)
            for occupied in combinations(range(2 * orbitals), electrons)]


def apply(state, operators):
    """Apply a product of (creation, slot) operators written left to right."""
    sign = 1
    for creation, slot in reversed(operators):
        bit = 1 << slot
        if bool(state & bit) == creation:
            return None
        if (state & (bit - 1)).bit_count() % 2:
            sign = -sign
        state ^= bit
    return state, sign


def one_body(entries):
    return [(value, ((True, 2*i + spin), (False, 2*j + spin)))
            for i, j, value in entries if value for spin in range(2)]


def assemble(states, terms):
    index = {state: i for i, state in enumerate(states)}
    matrix = [{} for _ in states]
    for j, state in enumerate(states):
        column = defaultdict(Fraction)
        for value, operators in terms:
            result = apply(state, operators)
            if result is not None and result[0] in index:
                column[index[result[0]]] += value * result[1]
        for i, value in column.items():
            if value:
                matrix[i][j] = value
    return matrix


def add_scaled(matrix, other, scale):
    for row, extra in zip(matrix, other, strict=True):
        for j, value in extra.items():
            result = row.get(j, 0) + scale * value
            if result:
                row[j] = result
            else:
                row.pop(j, None)


def square(matrix):
    result = []
    for row in matrix:
        out = defaultdict(Fraction)
        for k, value in row.items():
            for j, extra in matrix[k].items():
                out[j] += value * extra
        result.append({j: v for j, v in out.items() if v})
    return result


def row_norm(matrix):
    return max(sum(map(abs, row.values())) for row in matrix)


def symmetric(matrix):
    return all(matrix[j].get(i, 0) == v
               for i, row in enumerate(matrix) for j, v in row.items())


def connected_blocks(matrix):
    remaining = set(range(len(matrix)))
    while remaining:
        index = min(remaining)
        block = [index]
        remaining.remove(index)
        for i in block:
            neighbors = sorted(remaining.intersection(matrix[i]))
            remaining.difference_update(neighbors)
            block.extend(neighbors)
        yield sorted(block)


def submatrix(matrix, rows, cols):
    return [[matrix[i].get(j, 0) for j in cols] for i in rows]
