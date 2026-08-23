# Sage reference output

Verbatim stdout of the reference parameter generator at ragu's parameters. This
is the authority the pure-Python port in `../poseidon_params.py` is measured
against, and the tables in `crates/ragu_pasta/src/poseidon_f{p,q}.rs` are
compared to it directly.

Generator: [`daira/pasta-hadeshash`](https://github.com/daira/pasta-hadeshash),
revision `5959f2684a25b372fba347e62467efb00e7e2c3f`, file
`code/generate_parameters_grain.sage`. Produced with SageMath 10.7 (2025-08-09).

| file | invocation | sha256 |
| --- | --- | --- |
| `pallas-t5.txt` | `sage generate_parameters_grain.sage 1 0 255 5 8 56 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001` | `703f71fd3138e969a74090594fb264c31982623949ec7236c64e92d588942ee1` |
| `vesta-t5.txt` | `sage generate_parameters_grain.sage 1 0 255 5 8 56 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001` | `b9db55c59b712efa0891cbdb385f6a61566bb1710e66a752e28e761e430e1bbb` |

Both runs report `Result Algorithm 1: [True, 0]`, `Result Algorithm 2:
[True, None]`, and `Result Algorithm 3: [True, None]` — the MDS security filter
accepted the first Cauchy candidate, so the port's unported filter costs nothing
at these parameters.

To reproduce, clone the fork at that revision and run the invocations above.
Nothing in CI needs Sage; these files are the checked-in result.
