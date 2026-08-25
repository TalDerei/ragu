# list all available just commands
default:
    @just --list

_nixery_meta := if arch() == "aarch64" { "arm64/shell" } else { "shell" }

build *ARGS:
  cargo build {{ARGS}}

build_release *ARGS:
  cargo build --release --workspace --all-targets {{ARGS}}

_nightly := "nightly-2026-05-23"

lint: _typos_setup _book_setup
  cargo clippy --workspace --lib --tests --benches --all-features -- -D warnings
  cargo +{{_nightly}} fmt --all -- --config-path rustfmt.nightly.toml --check
  typos
  mdbook build ./book

fix: _typos_setup
  cargo +{{_nightly}} fmt --all -- --config-path rustfmt.nightly.toml
  cargo fix --allow-dirty --allow-staged --all-features
  cargo clippy --fix --allow-dirty --allow-staged --all-features
  typos -w

_install_binstall:
  @command -v cargo-binstall > /dev/null || cargo install cargo-binstall

_book_setup: _install_binstall
  @cargo binstall --quiet --no-confirm mdbook@0.4.52 mdbook-katex@0.9.4 mdbook-mermaid@0.16.2 mdbook-linkcheck@0.7.7 mdbook-admonish@1.20.0

_typos_setup: _install_binstall
  @cargo binstall --quiet --no-confirm typos-cli

_gungraun_setup: _install_binstall
  @cargo binstall --quiet --no-confirm gungraun-runner@0.17.0

_flamegraph_setup: _install_binstall
  @cargo binstall --quiet --no-confirm flamegraph

# locally [build | serve | watch] Ragu book
book COMMAND: _book_setup
  mdbook {{COMMAND}} ./book --open

# run all tests
test *ARGS:
  cargo test --workspace --all-features {{ARGS}}

# run quicker proptests used for routine local/CI coverage
proptests_fast *ARGS:
  PROPTEST_CASES="${PROPTEST_CASES:-64}" cargo test --release -p ragu_arithmetic -p ragu_core --all-features proptest {{ARGS}}

# run slower proptests with higher default case counts
proptests_heavy *ARGS:
  PROPTEST_CASES="${PROPTEST_CASES:-256}" cargo test --release -p ragu_circuits --all-features proptest {{ARGS}}

# run benchmarks (auto-detects platform)
bench *ARGS:
    @just _bench_{{os()}} {{ARGS}}

_bench_macos *ARGS:
    #!/bin/sh
    [ -t 1 ] && tty_opt="--tty" # use tty if stdout is a tty
    container=$(docker run $tty_opt --detach --interactive --init --rm \
        -v "{{justfile_dir()}}":/workspace:ro \
        -v ragu-cargo:/.cargo \
        -v ragu-rustup:/.rustup \
        -v "{{justfile_dir()}}"/target:/workspace/target \
        -e CARGO_HOME=/.cargo \
        -e RUSTUP_HOME=/.rustup \
        -w /workspace \
        --security-opt seccomp=unconfined \
        nixery.dev/{{_nixery_meta}}/cargo-binstall/gcc/just/rustup/valgrind \
        just _bench_linux {{ARGS}})
    trap "docker kill $container > /dev/null 2>&1" EXIT HUP
    docker attach --no-stdin $container

_bench_linux *ARGS: _gungraun_setup
    cargo bench --workspace --all-features --bench gungraun {{ARGS}}

# generate flamegraph in target/*.svg
flamegraph PACKAGE GROUP TARGET *ARGS:
    @just _flamegraph_{{os()}} {{PACKAGE}} {{GROUP}} {{TARGET}} {{ARGS}}

# generate flamegraph for ragu_pcd::fuse()
flamegraph_fuse:
    @just flamegraph ragu_pcd app_proof fuse

_flamegraph_macos PACKAGE GROUP TARGET *ARGS:
    #!/bin/sh
    [ -t 1 ] && tty_opt="--tty"
    container=$(docker run $tty_opt --detach --interactive --init --rm \
        -v "{{justfile_dir()}}":/workspace \
        -v ragu-cargo:/.cargo \
        -v ragu-rustup:/.rustup \
        -v ragu-flamegraph-target:/tmp/ragu-target \
        -e CARGO_HOME=/.cargo \
        -e RUSTUP_HOME=/.rustup \
        -w /workspace \
        --privileged \
        nixery.dev/{{_nixery_meta}}/cargo-binstall/busybox/gcc/just/rustup/perf \
        just _flamegraph_linux {{PACKAGE}} {{GROUP}} {{TARGET}} {{ARGS}})
    trap "docker kill $container > /dev/null 2>&1" EXIT HUP
    docker attach --no-stdin $container

_flamegraph_linux PACKAGE GROUP TARGET *ARGS: _flamegraph_setup
    #!/bin/sh
    set -e
    bench_file="crates/{{PACKAGE}}/benches/gungraun.rs"
    if [ ! -f "$bench_file" ]; then
        echo "error: bench file not found: $bench_file" >&2; exit 1
    fi
    bench_list=$(grep -A2 "name = {{GROUP}}" "$bench_file" | grep 'benchmarks' | sed 's/.*=\s*//;s/[^a-zA-Z0-9_,]//g')
    if [ -z "$bench_list" ]; then
        echo "error: group '{{GROUP}}' not found in $bench_file" >&2; exit 1
    fi
    func_idx=0
    for fn in $(echo "$bench_list" | tr ',' ' '); do
        [ "$fn" = "{{TARGET}}" ] && break
        func_idx=$((func_idx + 1))
    done
    CARGO_TARGET_DIR=/tmp/ragu-target CARGO_PROFILE_RELEASE_DEBUG=true \
        cargo flamegraph --release -p {{PACKAGE}} --bench gungraun \
        -o "target/flamegraph-{{PACKAGE}}-{{GROUP}}-{{TARGET}}.svg" {{ARGS}} \
        -- --gungraun-run {{GROUP}} "$func_idx" 0

# backend boundary censuses (qa/backend/README.md): dependency direction,
# feature leakage, override gating, unsafe budget, Backend trait surface
backend_boundary:
  python3 qa/backend/deps.py check
  python3 qa/backend/deps.py leakage
  qa/backend/census.sh
  qa/backend/api-snapshot.sh check

# backend lane: differential, parity, liveness, harness-strength, and
# nontrivial-step tests in the serial native-msm configuration
backend_equivalence *ARGS:
  cargo test --release -p ragu_acceleration --locked --features native-msm {{ARGS}}
  PROPTEST_CASES="${PROPTEST_CASES:-4}" cargo test --release -p ragu_pcd --locked --features native-msm --lib backend_tests:: {{ARGS}}
  cargo test --release --locked -p ragu_pcd --test nontrivial {{ARGS}}
  cargo test --release --locked -p ragu_pcd --features native-msm,unstable-fuzzing --test backend_goldens {{ARGS}}
  cargo test --release --locked -p ragu_testing --lib strategies:: {{ARGS}}
  qa/backend/required-tests.sh

# backend lane: callgrind perf gate on fuse, reference vs accelerated (needs
# valgrind; on macOS this runs inside the `bench` docker wrapper)
backend_perf:
  just bench -- --callgrind-args=--cache-sim=no --save-summary=json 'gungraun::app_proof*::fuse*'
  find target/gungraun -name summary.json -exec cat {} + | jq --slurp --exit-status --argjson tolerance 1.0 --from-file qa/backend/perf-gate.jq

# regenerate the committed proof-digest goldens (frozen-tier: review the diff)
goldens_update:
  UPDATE_GOLDENS=1 cargo test --release -p ragu_pcd --locked --features native-msm,unstable-fuzzing --test backend_goldens

# backend lane: everything the `backend boundary` and `backend equivalence`
# jobs run
backend_lane: backend_boundary backend_equivalence backend_perf

# run CI checks locally (formatting, clippy, tests)
ci_local: _book_setup backend_boundary
  @echo "Running formatting check..."
  cargo +{{_nightly}} fmt --all -- --config-path rustfmt.nightly.toml --check
  @echo "Running clippy..."
  cargo clippy --workspace --lib --tests --benches --locked --all-features -- -D warnings
  @echo "Running tests..."
  cargo test --release --all --locked --all-features
  @echo "Building benchmarks and examples..."
  cargo build --workspace --benches --examples --all-features
  @echo "Checking documentation..."
  RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all --locked --all-features --document-private-items
  @echo "Building book..."
  mdbook build ./book
  @echo "All CI checks passed!"
