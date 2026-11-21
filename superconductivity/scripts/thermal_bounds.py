"""Rational enclosures for scalar functions and finite thermal traces."""
from fractions import Fraction as Q
from math import ceil, factorial, floor, isqrt

from fermion import connected_blocks, row_norm

GRID = 10**32
TERMS = 28
ROOT_GRID = 10**25


def rounded_bounds(lo, hi):
    return Q(floor(lo * GRID), GRID), Q(ceil(hi * GRID), GRID)


def exp_bounds(x):
    x = Q(x)
    if x <= -128:
        return Q(0), Q(1, GRID)
    if x < 0:
        lo, hi = exp_bounds(-x)
        return rounded_bounds(1 / hi, 1 / lo)
    divisor = max(1, ceil(x))
    y = x / divisor
    partial = sum(y**k / factorial(k) for k in range(TERMS + 1))
    error = 2 * y**(TERMS + 1) / factorial(TERMS + 1)
    lo, hi = rounded_bounds(partial, partial + error)
    return lo**divisor, hi**divisor


def log_near_one(x):
    y = (x - 1) / (x + 1)
    partial = 2 * sum(y**(2*k+1) / (2*k+1) for k in range(TERMS))
    tail = 2 * y**(2*TERMS+1) / ((2*TERMS+1) * (1 - y*y))
    return rounded_bounds(partial, partial + tail)


LOG_TWO = log_near_one(Q(2))


def log_bounds(x):
    if x <= 0:
        raise ValueError("a logarithm enclosure needs a positive argument")
    if x < 1:
        lo, hi = log_bounds(1 / x)
        return -hi, -lo
    shift = max(0, x.numerator.bit_length() - x.denominator.bit_length() - 1)
    scaled = x / 2**shift
    while scaled >= 2:
        shift += 1
        scaled /= 2
    lo, hi = log_near_one(scaled)
    return lo + shift * LOG_TWO[0], hi + shift * LOG_TWO[1]


def sqrt_bounds(x):
    integer = isqrt(floor(x * ROOT_GRID**2))
    lo = Q(integer, ROOT_GRID)
    return lo, lo if lo**2 == x else Q(integer+1, ROOT_GRID)


def multiply_scaled(a, b, divisor):
    """Multiply integer sparse matrices, dropping each entry's fractional part."""
    result = []
    for row in a:
        out = {}
        for k, value in row.items():
            for j, other in b[k].items():
                out[j] = out.get(j, 0) + value * other
        result.append({j: v // divisor for j, v in out.items() if v // divisor})
    return result


def block_trace(matrix, temperature):
    n = len(matrix)
    scale = 1
    while row_norm(matrix) > scale * temperature:
        scale *= 2
    x = [{j: floor(-v * GRID / (scale * temperature)) for j, v in row.items()}
         for row in matrix]
    term = [{i: GRID} for i in range(n)]
    partial = [row.copy() for row in term]
    error = Q(n, GRID)
    term_error = Q(0)
    total_error = Q(0)
    for k in range(1, TERMS+1):
        previous_norm = Q(row_norm(term), GRID)
        term = multiply_scaled(term, x, GRID*k)
        term_error = Q(ceil(GRID * ((term_error + previous_norm * error) / k + error)), GRID)
        total_error += term_error
        for row, increment in zip(partial, term, strict=True):
            for j, v in increment.items():
                row[j] = row.get(j, 0) + v
    total_error += Q(2, factorial(TERMS+1))
    while scale > 1:
        norm = Q(row_norm(partial), GRID)
        partial = multiply_scaled(partial, partial, GRID)
        total_error = Q(ceil(GRID * (total_error * (2*norm + total_error) + error)), GRID)
        scale //= 2
    trace = Q(sum(row.get(i, 0) for i, row in enumerate(partial)), GRID)
    return trace - n*total_error, trace + n*total_error


def trace_bounds(matrix, temperature):
    lo = hi = Q(0)
    for indices in connected_blocks(matrix):
        index = {i: j for j, i in enumerate(indices)}
        block = [{index[j]: v for j, v in matrix[i].items()} for i in indices]
        lower, upper = block_trace(block, temperature)
        lo += lower
        hi += upper
    if lo <= 0:
        raise ValueError("thermal trace envelope did not give a positive lower bound")
    return lo, hi


def free_energy(trace, temperature):
    return -temperature * log_bounds(trace[1])[1], -temperature * log_bounds(trace[0])[0]
