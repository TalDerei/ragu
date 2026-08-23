"""Faithful pure-Python port of `generate_parameters_grain.sage` (Grain LFSR part).

Ported from the `daira/pasta-hadeshash` fork of the Hades/Poseidon reference
implementation, revision 5959f2684a25b372fba347e62467efb00e7e2c3f, file
`code/generate_parameters_grain.sage`.

Covers the two pieces that produce the committed tables:

* `generate_constants` - the Grain LFSR stream with rejection sampling, which
  fixes the round constants exactly; and
* `create_mds_p` - the Cauchy matrix built from the next `2*t` Grain samples.

Not ported: `algorithm_1/2/3`, the MDS security filter. Those only decide
whether a candidate matrix is *accepted*; the reference resamples until they
do, and this module emits the first candidate. The two agree exactly when the
first candidate was accepted, which is established by comparing this module's
output against the reference's pinned under `reference/` -- the script does
not report which candidate it settled on, and its printed algorithm results
are re-run on the matrix it returns, so they read `True` regardless.
"""


def _init_sequence(field, sbox, n, t, r_f, r_p):
    bits = (
        bin(field)[2:].zfill(2)
        + bin(sbox)[2:].zfill(4)
        + bin(n)[2:].zfill(12)
        + bin(t)[2:].zfill(12)
        + bin(r_f)[2:].zfill(10)
        + bin(r_p)[2:].zfill(10)
        + "1" * 30
    )
    return [int(b) for b in bits]


def _grain_sr_generator(init_sequence):
    bit_sequence = list(init_sequence)

    def step():
        new_bit = (
            bit_sequence[62]
            ^ bit_sequence[51]
            ^ bit_sequence[38]
            ^ bit_sequence[23]
            ^ bit_sequence[13]
            ^ bit_sequence[0]
        )
        bit_sequence.pop(0)
        bit_sequence.append(new_bit)
        return new_bit

    for _ in range(160):
        step()

    while True:
        new_bit = step()
        while new_bit == 0:
            step()
            new_bit = step()
        yield step()


class Grain:
    """The Grain bit stream, seeded exactly as the reference script seeds it."""

    def __init__(self, field, sbox, n, t, r_f, r_p):
        self._gen = _grain_sr_generator(_init_sequence(field, sbox, n, t, r_f, r_p))
        self._n = n

    def random_bits(self, num_bits):
        bits = [next(self._gen) for _ in range(num_bits)]
        return int("".join(str(b) for b in bits), 2)

    def random_field_bits(self):
        return self.random_bits(self._n)


def generate_constants(grain, t, r_f, r_p, p):
    """`generate_constants` for `FIELD == 1`: rejection sampling into GF(p)."""
    constants = []
    for _ in range((r_f + r_p) * t):
        value = grain.random_field_bits()
        while value >= p:
            value = grain.random_field_bits()
        constants.append(value)
    return [constants[r * t : (r + 1) * t] for r in range((r_f + r_p))]


def create_mds_candidate(grain, t, p):
    """`create_mds_p`: a Cauchy matrix over the next `2*t` Grain samples.

    Note the reference reduces mod p here rather than rejecting, and resamples
    the whole list on a duplicate.
    """
    while True:
        rand_list = [grain.random_field_bits() % p for _ in range(2 * t)]
        while len(rand_list) != len(set(rand_list)):
            rand_list = [grain.random_field_bits() % p for _ in range(2 * t)]
        xs, ys = rand_list[:t], rand_list[t:]
        if any((xs[i] + ys[j]) % p == 0 for i in range(t) for j in range(t)):
            continue
        return [[pow((xs[i] + ys[j]) % p, p - 2, p) for j in range(t)] for i in range(t)]


def generate(t, r_f, r_p, p, n=255, field=1, sbox=0):
    """Round constants and the first MDS candidate for one parameter set."""
    grain = Grain(field, sbox, n, t, r_f, r_p)
    round_constants = generate_constants(grain, t, r_f, r_p, p)
    mds = create_mds_candidate(grain, t, p)
    return round_constants, mds


PALLAS_BASE = 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001
VESTA_BASE = 0x40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001
