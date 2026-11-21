"""Full DFPT assembly on ordered determinants for the validation solve."""
from bisect import bisect_left
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product


def scatter(occupied, creation, annihilation):
    slots = list(occupied)
    parity = 0
    for slot in reversed(annihilation):
        position = bisect_left(slots, slot)
        if position == len(slots) or slots[position] != slot:
            return None
        slots.pop(position)
        parity += position
    for slot in reversed(creation):
        position = bisect_left(slots, slot)
        if position < len(slots) and slots[position] == slot:
            return None
        slots.insert(position, slot)
        parity += position
    return tuple(slots), (-1 if parity % 2 else 1)


def vertex_rows(orbitals, states, index, derivative):
    diagonal = [derivative.get((i, i), 0) for i in range(orbitals)]
    hops = [[] for _ in range(orbitals)]
    for (i, j), value in derivative.items():
        if i != j and value:
            hops[i].append((j, value))
            hops[j].append((i, value))

    rows = [{} for _ in states]
    for column, occupied in enumerate(states):
        value = sum(diagonal[i] for i, _ in occupied)
        if value:
            rows[column][column] = value
        for source, (i, spin) in enumerate(occupied):
            if not hops[i]:
                continue
            remaining = occupied[:source] + occupied[source+1:]
            for j, value in hops[i]:
                target = (j, spin)
                destination = bisect_left(remaining, target)
                if destination < len(remaining) and remaining[destination] == target:
                    continue
                moved = remaining[:destination] + (target,) + remaining[destination:]
                rows[index[moved]][column] = -value if (source+destination) % 2 else value
    return rows


def assemble_full_sector(case, electrons):
    """Build the normal matrix, primitive mode matrices, and instantaneous matrix."""
    orbitals = len(case.levels)
    states = list(combinations(product(range(orbitals), range(2)), electrons))
    index = {occupied: i for i, occupied in enumerate(states)}
    normal = [defaultdict(Q) for _ in states]
    for j, occupied in enumerate(states):
        normal[j][j] = (sum(case.levels[i] for i, _ in occupied) +
                        sum(value for a, b, value in case.density if a in occupied and b in occupied))
        for creation, annihilation, value in case.scattering:
            result = scatter(occupied, creation, annihilation)
            if result is not None:
                target, sign = result
                normal[index[target]][j] += sign*value
    normal = [{j: value for j, value in row.items() if value} for row in normal]

    matrix = [defaultdict(Q, row) for row in normal]
    modes = []
    if case.cartesian is not None:
        positions = set().union(*case.cartesian)
    for force, mode in case.modes:
        if case.cartesian is None:
            derivative = mode
        else:
            derivative = {key: sum(weight*axis.get(key, 0)
                                   for weight, axis in zip(mode, case.cartesian, strict=True))
                          for key in positions}
        rows = vertex_rows(orbitals, states, index, derivative)
        modes.append((force, rows))
        # The induced form is -||A x||^2/(2 force). Accumulate the Gram
        # matrix from each row of A independently of the predictor's square.
        for row in rows:
            for i, value in row.items():
                coefficient = value / (2*force)
                for j, other in row.items():
                    matrix[i][j] -= coefficient*other

    return normal, modes, [{j: value for j, value in row.items() if value} for row in matrix]
