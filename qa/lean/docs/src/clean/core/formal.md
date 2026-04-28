# Formal circuits

The main abstraction used by Clean to package a verified circuit is `FormalCircuit`.
A `FormalCircuit` tightly colocates circuit definitions, properties and proofs about those properties.
At a high level, it is a structure:

```lean
structure FormalCircuit (F : Type) [Field F] (Input Output : TypeMap)
    [ProvableType Input] [ProvableType Output] where
  main : Var Input F → Circuit F (Var Output F)
  Assumptions : Input F → Prop
  Spec : Input F → Output F → Prop
  soundness : Soundness F Assumptions Spec
  completeness : Completeness F Assumptions
```

This structure is parameterized by a field `F`, and input/output shapes, which must be provable type maps.
Let's go through all the fields of this structure:
- `main` is the circuit body: it takes as input `Var Input F` and returns `(Var Output F)` wrapped in a `Circuit` monad.
- `Assumptions` is the property that must be satisfied by the circuit's inputs. Soundness is provided as long as the verifier can be sure of those assumptions without relying on the circuit. Completeness is provided as long as the honest prover can be sure of those assumptions because of the way it has been operating.
- `Spec` is a high-level property that the circuit ensures, and is typically some high-level relation between inputs and outputs.
- `soundness` and `completeness` are proofs for the soundness and completeness properties, which we describe below.


> [!NOTE]
> In the real implementation, Clean splits the structure into two layers. The real definition is:
> 
> ```lean
> structure FormalCircuit (F : Type) [Field F] (Input Output : TypeMap)
>     [ProvableType Input] [ProvableType Output]
>     extends elaborated : ElaboratedCircuit F Input Output where
>   Assumptions (_ : Input F) : Prop := True
>   Spec : Input F → Output F → Prop
>   soundness : Soundness F elaborated Assumptions Spec
>   completeness : Completeness F elaborated Assumptions
> ```
> 
> Where `ElaboratedCircuit` contains some circuit-specific fields other than the `main` field.
> Those fields are not strictly necessary to the formal circuit semantics, and are present for optimization and proof-engineering reasons: the first versions of Clean did not have this distinction.
> For most circuits, those fields are derived automatically.

## Assumptions

The field

```lean
Assumptions : Input F → Prop
```

specifies the **preconditions under which the circuit is intended to be used**. Soundness and completeness are provided conditioned on the assumptions.
The caller circuit is able to derive the specification property of the sub-formal circuit only if they can discharge such assumptions.

Typical assumptions include:

- range conditions such as "this value fits in 8 bits",
- algebraic side conditions such as "this denominator is nonzero",
- well-formedness conditions on structured inputs, such as "this point coordinates satisfy the elliptic curve equation".

If no special input conditions are needed, `Assumptions` defaults to `True`.

## Specification

The field

```lean
Spec : Input F → Output F → Prop
```

is the high-level description of the properties the circuit ensures.

Typical specifications say things like:

- the output is the sum or product of the inputs,
- the output point is the group addition of the input points,
- the output field element is the result of one squeeze operation of Poseidon in sponge mode, derived from the sponge state given in input.

## Soundness

The soundness statement is defined as:

```lean
def Soundness (F : Type) [Field F] (circuit : ElaboratedCircuit F Input Output)
    (Assumptions : Input F → Prop) (Spec : Input F → Output F → Prop) :=
  ∀ offset : ℕ, ∀ env : Environment F,
  ∀ input_var : Var Input F, ∀ input : Input F, eval env input_var = input →
  Assumptions input →
  ConstraintsHold.Soundness env (circuit.main input_var |>.operations offset) →
  let output := eval env (circuit.output input_var offset)
  Spec input output
```

Soundness is the main property provided in the **adversarial prover** case. It precisely defines what guarantees the constraints provide to the verifier, and aims at avoiding underconstrained circuits.
Intuitively, we want to prove that for every possible assignment to variables, if the Assumptions on the inputs are true, and the constraints defined in the circuit hold, then also the Spec is true.

More precisely, soundness states: take any offset and any possible `Environment` (i.e., any possible assignment from variables to field elements, plus the committed `ProverData`). Take any symbolic input, assume the input satisfies `Assumptions`, assume all circuit constraints hold, then that input/output pair satisfies `Spec`.

Note that the environment here is a `Environment`, not the full `ProverEnvironment`. The statement therefore quantifies only over what the verifier can see, so it cannot accidentally depend on the prover's `hint`.

## Completeness

The completeness statement is defined as:

```lean
def Completeness (F : Type) [Field F] (circuit : ElaboratedCircuit F Input Output)
    (Assumptions : Input F → Prop) :=
  ∀ offset : ℕ, ∀ env : ProverEnvironment F, ∀ input_var : Var Input F,
  env.UsesLocalWitnessesCompleteness offset (circuit.main input_var |>.operations offset) →
  ∀ input : Input F, eval env input_var = input →
  Assumptions input →
  ConstraintsHold.Completeness env (circuit.main input_var |>.operations offset)
```

Completeness is the main property provided in the **honest prover** case. It precisely defines if the honest prover can actually provide a satisfying assignment to the variables, and aims at avoiding overconstrained circuits.
Intuitively, we want to prove that running the default (honest) witness generation starting from inputs that satisfy the assumptions, the resulting assignment satisfies the constraints.

More precisely, completeness states: take any offset and any possible environment, if the input satisfies `Assumptions`, and all the witness values in this circuit are derived from the honest witness generation function, then the constraints also hold on those values.

## GeneralFormalCircuit

We use `FormalCircuit` when the verifier (soundness) and the honest prover (completeness) assume the same `Assumptions`. Sometimes we need different assumptions for soundness and completeness. For example, the honest prover may rely on hints that the verifier does not have access to, and those hints may have to satisfy some property for witness generation to succeed.

For these cases, Clean provides `GeneralFormalCircuit`:

```lean
structure GeneralFormalCircuit (F : Type) (Input Output : TypeMap) [Field F]
    [ProvableType Input] [ProvableType Output] where
  main : Var Input F → Circuit F (Var Output F)
  Assumptions      : Input F → ProverData F → ProverHint F → Prop
  Spec             : Input F → Output F → ProverData F → Prop
  CompletenessSpec : Input F → Output F → ProverHint F → Prop
  soundness        : GeneralFormalCircuit.Soundness F Spec
  completeness     : GeneralFormalCircuit.Completeness F Assumptions
  completenessSpec : GeneralFormalCircuit.CompletenessSpecProof F Assumptions CompletenessSpec
```

The two auxiliary pieces of data that `Input F`/`Output F` get paired with are complementary:

- `ProverData F` is committed into the proof. Both the verifier and the honest prover see the same `ProverData`. It shows up in `Spec` (soundness) and in `Assumptions` (completeness) when a property depends on committed auxiliary data such as the content of a lookup table.
- `ProverHint F` is the prover's runtime-only witness-generation aid. It never appears in the proof, so the verifier cannot observe it. It shows up in `Assumptions` (the honest prover may want to assume something about its own hint) and in `CompletenessSpec` (an extra output-side promise the honest prover can make to its caller), but not in `Spec`.

Compared to `FormalCircuit`:

- `Assumptions` is used only for completeness: it is what the honest prover assumes about the inputs, the committed `ProverData`, and its own `ProverHint` when generating witnesses.
- `Spec` is used only for soundness: it may include, as a hypothesis on the LHS of `→`, some assumptions for the verifier. The verifier needs to establish the LHS of `→` without depending on the circuit before using the `Spec`. The LHS of `→` in `Spec` is usually different from the honest prover's `Assumptions` (otherwise, `FormalCircuit` is commonly preferred).
- `CompletenessSpec` lets the honest prover promise an extra relation between inputs, outputs, and its hint. It defaults to the trivially-true predicate, so most circuits ignore it.
