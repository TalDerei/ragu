# Proof-Carrying Data

## What is Proof-Carrying Data?

**Proof-Carrying Data (PCD)** is a cryptographic primitive where data is bundled together with a proof of its correctness. When you receive proof-carrying data, you get both:
- The actual data (computation outputs, public inputs, etc.)
- A cryptographic proof that this data was produced correctly

This allows nodes in a distributed system to pass data to each other along with verifiable evidence of how it was computed, without requiring recipients to re-execute the computation or trust the sender.

### IVC vs PCD

**Incrementally Verifiable Computation (IVC)** handles linear chains of computation:
```
Step 1 → Step 2 → Step 3 → Step 4
```
Each step proves it correctly computed on the output of the previous step.

**Proof-Carrying Data (PCD)** generalizes this to tree-structured computations:
```
        Step 4
       /      \
    Step 2   Step 3
       \      /
        Step 1
```
Each node can verify and combine proofs from multiple previous computations, enabling parallel and distributed workflows.

**Ragu's Approach:** Ragu treats all recursion uniformly as PCD with arity-2 (two inputs). Even when you only need IVC semantics (a linear chain), Ragu uses a dummy second input to maintain a uniform structure. This creates a lopsided binary tree where IVC emerges as a special case. While this might seem less efficient than specialized IVC handling, the performance cost appears negligible while significantly simplifying the implementation and API.

## Recursive Proof Composition

Ragu's power comes from its ability to prove statements about proofs themselves. This recursive property enables:

- **Incremental verification**: Each step verifies previous steps without re-executing them
- **Proof aggregation**: Multiple computations can be combined into a single proof
- **Unbounded computation**: Chain together arbitrarily many steps while keeping verification time logarithmic

The technical details of how this works involve specialized cryptographic primitives and accumulation schemes, but as a library user, you primarily interact with this through Ragu's API for creating, folding, and compressing proofs.

## The Cost Model: Compression vs. Folding

Ragu operates with a single proof structure that can exist in two different modes:

**Uncompressed proofs** (split-accumulation form):
- Non-succinct: size scales with the circuit size
- Large witness data, but inexpensive to generate
- Efficiently "folded" together using accumulation
- This is the natural mode for recursive computation

**Compressed proofs** (IPA-based succinct form):
- Succinct: size is logarithmic in the circuit size
- More expensive to create (compression step)
- More expensive to verify (dominated by linear-time multi-scalar multiplication)
- Optimal for bandwidth-constrained scenarios (e.g., blockchain transactions)

**When to compress:** The key is to operate in uncompressed mode during recursion and only compress at specific boundary conditions. For example, when broadcasting a proof on-chain, you compress to optimize for bandwidth. During intermediate computation steps where you'll continue folding proofs together, keep them uncompressed.

Note that compressed proofs can also be "decompressed" back into the accumulation form when needed for further folding.
