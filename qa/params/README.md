# Poseidon parameter provenance

The Poseidon tables in `crates/ragu_pasta/src/poseidon_f{p,q}.rs` are roughly
700 hand-transcribable field elements that no proof, fingerprint, or
differential test can validate. Every theorem and test downstream of them is
quantified over whatever the tables happen to contain: replace a constant and
nothing fails, because nothing anywhere asserts what the constants should be.
Their only external authority is the script that generated them.

`check_poseidon_params.py` regenerates the tables and compares:

```sh
python3 qa/params/check_poseidon_params.py
```

`poseidon_params.py` is a pure-Python port of the Grain LFSR part of
`generate_parameters_grain.sage`, from the
[`daira/pasta-hadeshash`](https://github.com/daira/pasta-hadeshash) fork at
revision `5959f2684a25b372fba347e62467efb00e7e2c3f`. Pure Python so the check
runs anywhere; Sage is not needed and is not in CI.

## Calibration

A reimplementation of a generator is only worth as much as its own validation,
so the port is first run against a set of constants that are already known
good: halo2's P128Pow5T3 tables, which are deployed Orchard consensus
parameters produced by the same script at `t = 3`. Point the check at a halo2
checkout to run that pass:

```sh
python3 qa/params/check_poseidon_params.py --halo2-dir path/to/halo2
```

Both fields' round constants and MDS matrices reproduce exactly, which is what
licenses the `t = 5` result. CI runs the ragu pass; the halo2 pass is a
developer-side calibration for when the port is touched.

## What is and isn't covered

Covered: the round constants exactly, including the Grain rejection sampling,
and the MDS matrix as the first Cauchy candidate.

Not covered: `algorithm_1`, `algorithm_2`, and `algorithm_3`, the reference's
MDS security filter. Those decide whether a candidate is *accepted*, and
porting them means porting vector spaces and eigenspaces over GF(p). The check
reports a match only when the committed matrix is the first candidate — which
it is for every table here, and which the reference itself records as
`Secure MDS: 0`. If a future parameter set lands on a later candidate the check
will say so rather than silently pass, and confirming it will need the Sage
script.

Also not covered, deliberately: whether these parameters are *good* — round
counts against the known attacks, MDS security. That is the reference script's
judgement and the Poseidon literature's, not this check's. This answers only
"are the committed tables what the recorded command produces".

## The other half

Parameters being genuine says nothing about the permutation consuming them
correctly. That is pinned separately, in
`crates/ragu_primitives/src/poseidon.rs`, against halo2's permutation test
vectors — see `gen_halo2_vectors.py`, which vendors them. The two checks are
complementary and neither implies the other:

| | pinned by |
| --- | --- |
| the constants ragu ships | this directory, against the generator |
| the permutation applying them | halo2's vectors, in `ragu_primitives` |
