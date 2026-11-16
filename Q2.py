"""Fast toroidal word-search generation using ONLY the Python standard library.

Run this file as a complete stdin/stdout program, or import its generate_grid
function. No installation, filesystem access, or network needed. If using a
HackerRank-provided driver, omit this file's main() and __main__ block.
Compatible with Python 3.8+.

generate_grid uses a bounded search and returns the best VALID grid found.
It may trade minimum size for speed and stops on a maximum-score solution.
solve_grid retains the optional exact solver: every grid it returns is globally
minimum-sized, but exhaustive search can take exponentially long.

The problem gives no infeasible-input convention or size/time limits. Proven
contradictions raise NoSolutionError; bounded unsuccessful searches raise
SearchLimitError instead of claiming global impossibility. Without a bound,
an infeasible instance not caught by preprocessing can run indefinitely.
Empty strings and characters outside A-Z are rejected. N is always positive.
"""

from collections import Counter
from math import isfinite, isqrt
from string import ascii_uppercase
from time import monotonic
from random import Random

# Per-call improvement budget. Increase if the judge allows more runtime.
# Preprocessing, guaranteed fallback construction, and final checking add some
# overhead; this is a cooperative search budget, not a hard process deadline.
SEARCH_SECONDS = 1.5

class NoSolutionError(ValueError):
    """The constraints have been proved inconsistent for every grid size."""


class SearchLimitError(RuntimeError):
    """A search bound was reached; this is NOT proof of global infeasibility."""


_DIRS = tuple((dr, dc) for dr in (-1, 0, 1)
              for dc in (-1, 0, 1) if dr or dc)


def _words(words, name):
    if isinstance(words, (str, bytes)):
        raise TypeError(f"{name} must be a collection of strings")
    result = list(words)
    for word in result:
        if not isinstance(word, str) or not word or any(
            ch not in ascii_uppercase for ch in word
        ):
            raise ValueError(f"{name} must contain nonempty A-Z strings")
    return result


def _reduce(words, required):
    # A word and its reversal impose exactly the same condition.
    unique = {min(w, w[::-1]) for w in words}
    ordered = sorted(unique, key=lambda w: (-len(w) if required else len(w), w))
    keep = []
    by_length = {}
    if required:
        for w in unique:
            by_length.setdefault(len(w), set()).add(w)
    redundant = set()
    for w in ordered:
        if required:
            if w in redundant:
                continue
            keep.append(w)
            # Inspect substrings of relevant lengths instead of comparing
            # every pair of words. Equal-length distinct words cannot contain
            # each other, an important saving for large word lists.
            for length, candidates in by_length.items():
                if length >= len(w):
                    continue
                for start in range(len(w)-length+1):
                    sub = w[start:start+length]
                    if sub in candidates:
                        redundant.add(sub)
                    reverse = sub[::-1]
                    if reverse in candidates:
                        redundant.add(reverse)
        else:
            contains_shorter = False
            for length, candidates in by_length.items():
                if length >= len(w):
                    continue
                for start in range(len(w)-length+1):
                    sub = w[start:start+length]
                    if sub in candidates or sub[::-1] in candidates:
                        contains_shorter = True
                        break
                if contains_shorter:
                    break
            if not contains_shorter:
                keep.append(w)
                by_length.setdefault(len(w), set()).add(w)
    return keep


def _patterns(word, n, anchored=False, check=lambda: None):
    """Distinct sets of cell/letter equalities for occurrences of word."""
    # Every allowed direction on an N x N torus has period exactly N.
    if any(word[k] != word[k % n] for k in range(n, len(word))):
        return
    word = word[:n]
    directions = ((0, 1), (1, 1)) if anchored else _DIRS
    starts = (0,) if anchored else range(n * n)
    seen = set()
    for start in starts:
        check()
        row, col = divmod(start, n)
        for dr, dc in directions:
            pattern = tuple(sorted(
                (((row + k * dr) % n) * n + (col + k * dc) % n, ch)
                for k, ch in enumerate(word)
            ))
            if pattern not in seen:
                seen.add(pattern)
                yield pattern


def _occurrences(grid, words, check=lambda: None):
    """Find all forbidden occurrences, including repeated wraps.

    Four families of N cyclic lines cover all directions when both word
    orientations are searched. Returned patterns can be blocked by SAT clauses.
    """
    n = len(grid)
    needles = set()
    for word in words:
        check()
        if all(word[k] == word[k % n] for k in range(n, len(word))):
            needles.add(word[:n])
            needles.add(word[::-1][:n])
    for dr, dc in ((0, 1), (1, 0), (1, 1), (1, -1)):
        for line in range(n):
            check()
            row, col = (line, 0) if dr == 0 else (0, line)
            cells = [((row + k * dr) % n, (col + k * dc) % n)
                     for k in range(n)]
            cycle = ''.join(grid[r][c] for r, c in cells)
            doubled = cycle + cycle[:-1]
            for word in needles:
                start = doubled.find(word)
                while 0 <= start < n:
                    yield tuple(sorted(
                        (cells[(start + k) % n][0] * n
                         + cells[(start + k) % n][1], ch)
                        for k, ch in enumerate(word)
                    ))
                    start = doubled.find(word, start + 1)


def validate_grid(grid, required_words, forbidden_words):
    """Independent, direct eight-direction verification of a submitted grid."""
    if not grid or any(not isinstance(row, str) for row in grid):
        return False
    n = len(grid)
    if any(len(row) != n or any(ch not in ascii_uppercase for ch in row)
           for row in grid):
        return False
    if any(not w or len(w) > n for w in required_words):
        return False
    if any(not w for w in forbidden_words):
        return False

    # There are only 4N distinct cyclic lines. Python's substring search runs
    # in C, avoiding a Python loop over every start, direction and character.
    lines = []
    for row in grid:
        lines.append(row + row[:-1])
    for c in range(n):
        for dc in (0, 1, -1):
            line = ''.join(grid[r][(c + r * dc) % n] for r in range(n))
            lines.append(line + line[:-1])

    def contains(word):
        if any(word[k] != word[k % n] for k in range(n, len(word))):
            return False
        forward, backward = word[:n], word[::-1][:n]
        return any(forward in line or backward in line for line in lines)

    return (all(contains(w) for w in required_words)
            and not any(contains(w) for w in forbidden_words))


def _solve_size(required, forbidden, alphabet, n, deadline, workers=1):
    def check():
        if deadline is not None and monotonic() >= deadline:
            raise SearchLimitError(f"Time budget exhausted at N={n}")

    # Cell domains and word-placement domains are Python integer bitsets.
    # Each mutation is recorded on a reversible trail, not a copied grid.
    code = {ch: 1 << i for i, ch in enumerate(alphabet)}
    cells = [(1 << len(alphabet)) - 1] * (n * n)
    placements = []
    possible = []
    supports = [{} for _ in cells]
    for i, word in enumerate(required):
        patterns = []
        # A selected occurrence can be translated to the origin and rotated /
        # reflected to east OR southeast. Both direction classes are needed.
        for pattern in _patterns(word, n, anchored=(i == 0), check=check):
            p = tuple((cell, code[ch]) for cell, ch in pattern)
            placement_bit = 1 << len(patterns)
            patterns.append(p)
            for cell, bit in p:
                key = (i, bit)
                supports[cell][key] = supports[cell].get(key, 0) | placement_bit
        if not patterns:
            return None
        placements.append(patterns)
        possible.append((1 << len(patterns)) - 1)
    grouped = []
    for support in supports:
        by_word = {}
        for (w, bit), mask in support.items():
            by_word.setdefault(w, {})[bit] = mask
        grouped.append([(w, letters, sum(letters.values()))
                        for w, letters in by_word.items()])
    # Placement masks for different letters at the same cell are disjoint.
    supports = grouped

    # A forbidden occurrence is a nogood: its cell/letter equalities may not
    # all hold at once. When only one remains undecided, remove that letter.
    nogoods = []
    incident = [[] for _ in cells]
    unique = set()
    for word in forbidden:
        for pattern in _patterns(word, n, check=check):
            p = tuple((cell, code[ch]) for cell, ch in pattern)
            if p in unique:
                continue
            unique.add(p)
            index = len(nogoods)
            nogoods.append(p)
            for cell, _ in p:
                incident[cell].append(index)
    del unique
    trail = []
    queue = []

    def narrow(cell, mask):
        old = cells[cell]
        mask &= old
        if mask == old:
            return True
        if not mask:
            return False
        trail.append((0, cell, old))
        cells[cell] = mask
        queue.append((cell, old ^ mask))
        return True

    def restrict_word(w, mask):
        old = possible[w]
        mask &= old
        if not mask:
            return False
        if mask != old:
            trail.append((1, w, old))
            possible[w] = mask
        if mask & (mask - 1) == 0:
            for cell, bit in placements[w][mask.bit_length() - 1]:
                if not narrow(cell, bit):
                    return False
        return True

    def enforce(index):
        undecided = None
        for cell, bit in nogoods[index]:
            mask = cells[cell]
            if not mask & bit:
                return True  # This occurrence is already impossible.
            if mask != bit:
                if undecided is not None:
                    return True  # At least two undecided equalities.
                undecided = (cell, bit)
        if undecided is None:
            return False  # Every letter of a forbidden occurrence is fixed.
        cell, bit = undecided
        return narrow(cell, cells[cell] & ~bit)

    def propagate():
        while queue:
            check()
            cell, removed = queue.pop()
            current = cells[cell]
            singleton = current & (current - 1) == 0
            for w, letters, touching in supports[cell]:
                if singleton:
                    mask = possible[w] & (~touching | letters.get(current, 0))
                else:
                    rejected = 0
                    for bit, placement_mask in letters.items():
                        if removed & bit:
                            rejected |= placement_mask
                    mask = possible[w] & ~rejected
                if mask != possible[w] and not restrict_word(w, mask):
                    return False
            for index in incident[cell]:
                if not enforce(index):
                    return False
        return True

    def undo(mark):
        queue.clear()
        while len(trail) > mark:
            kind, index, old = trail.pop()
            if kind == 0:
                cells[index] = old
            else:
                possible[index] = old

    # Necessary even before a required word is placed: long constant forbidden
    # words can reduce to a one-cell constraint on a small torus.
    for index in range(len(nogoods)):
        check()
        if not enforce(index):
            return None
    for w in range(len(required)):
        if not restrict_word(w, possible[w]):
            return None
    if not propagate():
        return None

    # bit_count is available on Python 3.10+. Keep 3.8/3.9 compatibility.
    count_bits = getattr(int, 'bit_count', lambda x: bin(x).count('1'))
    safe = [code[ch] for ch in alphabet
            if all(ch not in word for word in forbidden)]

    def branches():
        # Minimum remaining values selects the most constrained word first.
        remaining = [w for w, mask in enumerate(possible)
                     if mask & (mask - 1)]
        if remaining:
            w = min(remaining, key=lambda i: (count_bits(possible[i]), -len(required[i])))
            choices = []
            mask = possible[w]
            while mask:
                check()
                bit = mask & -mask
                mask -= bit
                p = placements[w][bit.bit_length() - 1]
                overlap = sum(cells[cell] == letter for cell, letter in p)
                if overlap == len(p):
                    # This word is already present; no search is needed for it.
                    return [(1, w, bit)]
                choices.append((-overlap, bit))
            choices.sort()  # Try the placements sharing most letters first.
            return [(1, w, bit) for _, bit in choices]

        unfilled = [cell for cell, mask in enumerate(cells)
                    if mask & (mask - 1)]
        if not unfilled:
            return None
        if safe:
            # Safe filler cannot create a forbidden word. Required placements
            # are all fixed, so filling their unused cells is now independent.
            bit = safe[0]
            if all(cells[cell] & bit for cell in unfilled):
                for cell in unfilled:
                    if not narrow(cell, bit):
                        raise RuntimeError('Internal error in safe filling')
                if not propagate():
                    raise RuntimeError('Internal error in safe filling')
                return None
        cell = min(unfilled, key=lambda c: (count_bits(cells[c]), -len(incident[c])))
        choices = []
        mask = cells[cell]
        while mask:
            bit = mask & -mask
            mask -= bit
            choices.append((0, cell, bit))
        return choices

    # Iterative depth-first search avoids Python's recursion-depth limit.
    stack = []
    while True:
        check()
        choices = branches()
        if choices is None:
            return [''.join(alphabet[cells[r*n+c].bit_length()-1]
                            for c in range(n)) for r in range(n)]
        stack.append((iter(choices), len(trail)))
        while stack:
            check()
            iterator, mark = stack[-1]
            undo(mark)
            choice = next(iterator, None)
            if choice is None:
                stack.pop()
                continue
            kind, index, bit = choice
            ok = restrict_word(index, bit) if kind else narrow(index, bit)
            if ok and propagate():
                break
        else:
            return None


def solve_grid(required_words, forbidden_words, *, max_n=None,
               time_limit=None, workers=1):
    """Return a globally smallest valid grid, or raise an explicit exception.

    max_n: optional inclusive size limit; never a claim of a universal bound.
    time_limit: optional overall budget in seconds, checked cooperatively;
                preprocessing/validation can slightly overrun.
    workers: retained for API compatibility; this solver is single-threaded.

    Unbounded search is complete for feasible finite inputs, but need not
    terminate on globally infeasible inputs. No arbitrary size cap is hidden.
    """
    started = monotonic()
    if max_n is not None and (type(max_n) is not int or max_n < 1):
        raise ValueError("max_n must be a positive integer or None")
    if time_limit is not None and (
        isinstance(time_limit, bool) or not isinstance(time_limit, (int, float))
        or not isfinite(time_limit) or time_limit <= 0
    ):
        raise ValueError("time_limit must be positive and finite, or None")
    if type(workers) is not int or workers < 1:
        raise ValueError("workers must be a positive integer")
    deadline = None if time_limit is None else started + time_limit
    original_r = _words(required_words, 'required_words')
    original_f = _words(forbidden_words, 'forbidden_words')
    required = _reduce(original_r, True)
    forbidden = _reduce(original_f, False)

    for r in required:
        for f in forbidden:
            if f in r or f[::-1] in r:
                raise NoSolutionError(f"Required word {r!r} contains forbidden word {f!r}")
    banned_letters = {w for w in forbidden if len(w) == 1}
    allowed = set(ascii_uppercase) - banned_letters
    if not allowed:
        raise NoSolutionError("All 26 letters are forbidden")
    # A forbidden word using a banned letter is already impossible.
    forbidden = [w for w in forbidden if len(w) > 1 and set(w) <= allowed]

    if len(allowed) == 1 and forbidden:
        raise NoSolutionError("The only permitted letter necessarily creates a forbidden word")

    # Every 2x2 block is a four-vertex clique under the eight directions.
    # If equal neighbors are all forbidden, its four letters must be distinct.
    # This catches, for example, AA/BB forbidden with only A and B permitted.
    pairs = {w for w in forbidden if len(w) == 2}
    if all(ch + ch in pairs for ch in allowed):
        def clique(candidates, needed):
            if needed == 0:
                return True
            if len(candidates) < needed:
                return False
            for i, ch in enumerate(candidates):
                remaining = [other for other in candidates[i + 1:]
                             if min(ch + other, other + ch) not in pairs]
                if clique(remaining, needed - 1):
                    return True
            return False

        if not clique(sorted(allowed), 4):
            raise NoSolutionError("Forbidden adjacent pairs make every 2x2 block impossible")

    # Letters absent from all remaining constraints are interchangeable.
    relevant = set(''.join(required + forbidden))
    spare = sorted(allowed - relevant)
    alphabet = ''.join(sorted((allowed & relevant) | set(spare[:1])))
    safe_letters = allowed - set(''.join(forbidden))
    if safe_letters:
        # Replacing every non-required letter by this safe letter preserves
        # all required words and cannot create a forbidden word.
        alphabet = ''.join(sorted(set(''.join(required)) | {min(safe_letters)}))
        active_letters = set(alphabet)
        forbidden = [w for w in forbidden if set(w) <= active_letters]

    if not required:
        # The smallest positive grid is 1x1; try every constant letter.
        for ch in alphabet:
            if not any(set(w) == {ch} for w in forbidden):
                return [ch]

    longest = max(map(len, original_r), default=1)
    counts = Counter()
    for word in required:
        counts |= Counter(word)
    # Each required word visits distinct cells because len(word) <= N.
    lower = max(longest, isqrt(max(1, sum(counts.values())) - 1) + 1)

    # A letter absent from every forbidden word gives a rigorous upper bound:
    # put required words in rows 0,2,4,... and fill everything else with it.
    # Separator rows and a trailing separator column prevent any new word.
    safe = allowed - set(''.join(forbidden))
    upper = max(longest + 1, 2 * len(required)) if safe and required else None
    stop = min(max_n, upper) if max_n is not None and upper is not None else (
        max_n if max_n is not None else upper)
    n = lower
    while stop is None or n <= stop:
        if deadline is not None and monotonic() >= deadline:
            raise SearchLimitError(f"Time budget exhausted at N={n}")
        # Cheap candidate at the current size: retain the input order in rows.
        # Validate before accepting; wrapping can create forbidden words even
        # when every required word is harmless in isolation. Trying this only
        # at the current size preserves the minimum-size guarantee.
        row_words = list(dict.fromkeys(original_r))
        if len(row_words) <= n:
            filler = next((ch for ch in alphabet if ch in safe), alphabet[0])
            candidate = [w + filler * (n - len(w)) for w in row_words]
            candidate.extend([filler * n] * (n - len(candidate)))
            if validate_grid(candidate, original_r, original_f):
                return candidate
        result = _solve_size(required, forbidden, alphabet, n, deadline, workers)
        if result is not None:
            if not validate_grid(result, original_r, original_f):
                raise RuntimeError("Internal error: independent validation failed")
            return result
        n += 1
    # If the constructive upper bound was reached, a solution must exist.
    if upper is not None and stop == upper:
        raise RuntimeError("Internal error: constructive upper bound was infeasible")
    raise SearchLimitError(f"No solution with N <= {max_n}; larger sizes were not ruled out")


def _shelf_grid(words, n, filler, separated):
    """First-fit decreasing row packing; separated rows give a safe fallback."""
    stride = 2 if separated else 1
    rows, used = [], []
    for word in sorted(words, key=len, reverse=True):
        cost = len(word) + int(separated)
        for i in range(len(rows)):
            if used[i] + cost <= n:
                rows[i] += word + (filler if separated else '')
                used[i] += cost
                break
        else:
            if cost > n or (len(rows) + 1) * stride > n:
                return None
            rows.append(word + (filler if separated else ''))
            used.append(cost)
    grid = [filler * n for _ in range(n)]
    for i, row in enumerate(rows):
        grid[i * stride] = row + filler * (n - len(row))
    return grid


def _greedy_size(words, forbidden, alphabet, safe, n, deadline, rng):
    """Randomized overlap-first packing, bounded by deadline. No invalid output."""
    def check():
        if monotonic() >= deadline:
            raise SearchLimitError('Packing time slice exhausted')

    codes = {w: tuple(ord(ch) for ch in w) for w in words}
    needles = set()
    for w in forbidden:
        if all(w[k] == w[k % n] for k in range(n, len(w))):
            needles.add(w[:n].encode('ascii'))
            needles.add(w[::-1][:n].encode('ascii'))
    directions = ((0, 1), (1, 0), (1, 1), (1, -1))
    full = (1 << (n*n)) - 1
    bands = full // ((1 << n) - 1)
    low = [((1 << (n-k)) - 1)*bands for k in range(n)]
    high = [full ^ mask for mask in low]

    def rotate(mask, k):
        # Rotate EACH N-bit cyclic line, without crossing line boundaries.
        if not k:
            return mask
        return ((mask >> k) & low[k]) | ((mask << (n-k)) & high[k])

    locations = []
    for r in range(n):
        check()
        for c in range(n):
            locations.append((r*n+c, c*n+r, ((c-r) % n)*n+r, ((c+r) % n)*n+r))

    def forbidden_present(board):
        if not needles:
            return False
        for row in range(n):
            line = bytes(board[row*n:(row+1)*n])
            doubled = line + line[:-1]
            if any(w in doubled for w in needles):
                return True
        for col in range(n):
            for dc in (0, 1, -1):
                line = bytes(board[r*n+(col+r*dc) % n] for r in range(n))
                doubled = line + line[:-1]
                if any(w in doubled for w in needles):
                    return True
        return False

    filler_order = sorted(alphabet, key=lambda c: (c not in safe,
                          sum(w.count(c) for w in forbidden), c))
    restart = 0
    while True:
        check()
        board = [0] * (n*n)
        empty = [full] * 4
        letter_masks = [{} for _ in range(4)]

        def put(cell, ch):
            board[cell] = ch
            for d, index in enumerate(locations[cell]):
                bit = 1 << index
                empty[d] &= ~bit
                letter_masks[d][ch] = letter_masks[d].get(ch, 0) | bit

        def clear(cell):
            ch = board[cell]
            board[cell] = 0
            for d, index in enumerate(locations[cell]):
                bit = 1 << index
                empty[d] |= bit
                letter_masks[d][ch] &= ~bit

        order = sorted(words, key=lambda w: -len(w) + (rng.random()*3 if restart else 0))
        restart += 1
        failed = False
        for wi, word in enumerate(order):
            check()
            letters = codes[word]
            if wi == 0:
                # Translation/rotation symmetry fixes the first word's start.
                choices = [(0 if restart % 2 else 2, letters, 1)]
            else:
                best, choices = -1, []
                variants = (letters,) if letters == letters[::-1] else (letters, letters[::-1])
                for d in range(4):
                    for variant in variants:
                        check()
                        possible = full
                        matches = []
                        for k, ch in enumerate(variant):
                            occupied = letter_masks[d].get(ch, 0)
                            possible &= rotate(empty[d] | occupied, k)
                            if not possible:
                                break
                            matches.append(rotate(occupied, k))
                        else:
                            # Bit-sliced addition scores ALL possible starts
                            # simultaneously, using O(log(word length)) planes.
                            planes = []
                            for match in matches:
                                carry, j = match & possible, 0
                                while carry:
                                    if j == len(planes):
                                        planes.append(carry)
                                        break
                                    carry, planes[j] = carry & planes[j], carry ^ planes[j]
                                    j += 1
                            overlap, winners = 0, possible
                            for j in range(len(planes)-1, -1, -1):
                                yes = winners & planes[j]
                                if yes:
                                    winners = yes
                                    overlap |= 1 << j
                            if overlap > best:
                                best, choices = overlap, [(d, variant, winners)]
                            elif overlap == best:
                                choices.append((d, variant, winners))
            accepted = False
            for _ in range(128):
                if not choices:
                    break
                check()
                group = rng.randrange(len(choices))
                d, variant, starts = choices[group]
                pivot = rng.randrange(n*n) if wi else 0
                tail = starts >> pivot
                start = pivot + (tail & -tail).bit_length()-1 if tail else (starts & -starts).bit_length()-1
                starts &= ~(1 << start)
                if starts:
                    choices[group] = (d, variant, starts)
                else:
                    choices.pop(group)
                line, pos = divmod(start, n)
                if d == 0:
                    row, col = line, pos
                elif d == 1:
                    row, col = pos, line
                else:
                    row, col = pos, (line + (pos if d == 2 else -pos)) % n
                dr, dc = directions[d]
                path = [((row+k*dr) % n)*n + (col+k*dc) % n for k in range(len(word))]
                changed = [cell for cell in path if not board[cell]]
                for cell, ch in zip(path, variant):
                    put(cell, ch)
                if not forbidden_present(board):
                    accepted = True
                    break
                for cell in changed:
                    clear(cell)
            if not accepted:
                failed = True
                break
        if failed:
            continue
        free = [cell for cell, ch in enumerate(board) if not ch]
        for filler in filler_order:
            check()
            for cell in free:
                board[cell] = ord(filler)
            if not forbidden_present(board):
                return [''.join(map(chr, board[r*n:(r+1)*n])) for r in range(n)]
        # When no uniform filler works, repair only unused cells. Required
        # word letters stay fixed. Every repair is checked again next pass.
        free_set = set(free)
        for _ in range(80):
            check()
            grid = [''.join(map(chr, board[r*n:(r+1)*n])) for r in range(n)]
            bad = next(_occurrences(grid, forbidden, check), None)
            if bad is None:
                return grid
            changeable = [cell for cell, _ in bad if cell in free_set]
            if not changeable or len(alphabet) < 2:
                break
            cell = rng.choice(changeable)
            replacement = rng.choice(alphabet)
            while ord(replacement) == board[cell]:
                replacement = rng.choice(alphabet)
            board[cell] = ord(replacement)


def generate_grid(required_words, forbidden_words):
    """Return a validated, dense grid within a bounded improvement budget.

    Easy cases remain provably optimal. On hard cases this trades optimal size
    for speed; required/forbidden-word correctness is NEVER relaxed. Use
    solve_grid for the optional exhaustive, minimum-size search.
    """
    start = monotonic()
    deadline = start + SEARCH_SECONDS
    original_r = _words(required_words, 'required_words')
    original_f = _words(forbidden_words, 'forbidden_words')
    # Lossless preprocessing and a short exact attempt also catch proven
    # contradictions. Never let proof search consume the whole runtime budget.
    try:
        return solve_grid(original_r, original_f, time_limit=min(0.08, SEARCH_SECONDS/10))
    except SearchLimitError:
        pass
    required = _reduce(original_r, True)
    forbidden = _reduce(original_f, False)
    allowed = set(ascii_uppercase) - {w for w in forbidden if len(w) == 1}
    forbidden = [w for w in forbidden if len(w) > 1 and set(w) <= allowed]
    safe = allowed - set(''.join(forbidden))
    alphabet = ''.join(sorted(allowed))
    if safe:
        alphabet = ''.join(sorted(set(''.join(required)) | {min(safe)}))
        forbidden = [w for w in forbidden if set(w) <= set(alphabet)]
    counts = Counter()
    for w in required:
        counts |= Counter(w)
    lower = max(max(map(len, original_r), default=1),
                isqrt(max(1, sum(counts.values()))-1)+1)
    total = sum(map(len, original_r))  # Original duplicates count in scoring.
    best = None

    # Construct a valid fallback BEFORE attempting hard dense packings.
    if safe:
        separated = bool(forbidden)
        load = sum(len(w)+int(separated) for w in required)
        n = max(lower + int(separated), isqrt(max(1, load)*(2 if separated else 1)))
        while best is None:
            candidate = _shelf_grid(required, n, min(safe), separated)
            if candidate is not None and validate_grid(candidate, original_r, original_f):
                best = candidate
            else:
                n += 1
    else:
        # No safe separator exists: trial layouts must be explicitly checked.
        for n in range(lower, lower+4):
            for filler in alphabet:
                candidate = _shelf_grid(required, n, filler, False)
                if candidate is not None and validate_grid(candidate, original_r, original_f):
                    best = candidate
                    break
            if best is not None or monotonic() >= deadline:
                break

    def finished(grid):
        # This is the actual capped score, not a proxy for occupied cells.
        return len(grid) == lower or 10*total >= 17*len(grid)**2

    if best is not None and finished(best):
        return best
    rng = Random(0)
    exact_tried = set()
    # Target the largest full-score size first, when full score is possible.
    # This can save substantial work compared with proving a smaller optimum.
    # Feasibility is NOT assumed monotone in N; no size is declared impossible
    # merely because a randomized attempt failed.
    goal = max(lower, isqrt(10*total//17))
    target = min(goal, len(best)-1) if best is not None else goal
    while monotonic() < deadline:
        if best is not None and len(best) <= lower:
            break
        result = None
        # A short exact search can close the last one- or two-row gap on small
        # instances. Limit both its time and approximate model size.
        if (best is not None and len(best)-target <= 2
                and len(required) <= 40 and 8*len(required)*target*target <= 80000
                and target not in exact_tried and deadline-monotonic() > 0.4):
            exact_tried.add(target)
            try:
                result = _solve_size(required, forbidden, alphabet, target,
                                     min(deadline, monotonic()+0.35))
            except SearchLimitError:
                pass
        if result is None:
            remaining = deadline - monotonic()
            allowance = min(0.25 if best is not None else 0.4, remaining)
            try:
                result = _greedy_size(required, forbidden, alphabet, safe, target,
                                      monotonic()+allowance, rng)
            except SearchLimitError:
                result = None
        if result is not None and validate_grid(result, original_r, original_f):
            if best is None or len(result) < len(best):
                best = result
            if finished(best):
                return best
            target = max(goal, (lower + len(best) - 1)//2)
            target = min(target, len(best)-1)
            continue
        if best is not None:
            target = min(len(best)-1, (target+len(best))//2)
        else:
            target += max(1, target//8)
    if best is not None:
        return best
    raise SearchLimitError('No valid grid found within the budget; increase SEARCH_SECONDS')


def main():
    """Input: required count, required words, forbidden count, forbidden words.

    Output contains exactly N rows, each with N uppercase letters. There is
    no size prefix, Python list syntax, explanatory text, or blank separator.
    """
    import sys

    tokens = sys.stdin.read().split()
    if not tokens:
        return
    position = 0

    def read_words(label):
        nonlocal position
        if position >= len(tokens):
            raise ValueError(f"Missing {label} word count")
        try:
            count = int(tokens[position])
        except ValueError:
            raise ValueError(f"Invalid {label} word count") from None
        position += 1
        if count < 0:
            raise ValueError(f"The {label} word count cannot be negative")
        end = position + count
        if end > len(tokens):
            raise ValueError(f"Expected {count} {label} words")
        words = tokens[position:end]
        position = end
        return words

    required_words = read_words('required')
    forbidden_words = read_words('forbidden')
    if position != len(tokens):
        raise ValueError('Unexpected extra input after the forbidden words')
    grid = generate_grid(required_words, forbidden_words)
    sys.stdout.write('\n'.join(grid) + '\n')


if __name__ == '__main__':
    main()
