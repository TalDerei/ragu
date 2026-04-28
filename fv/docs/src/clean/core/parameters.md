# Compile-time parameters

In Clean, compile-time parameters are simply ordinary Lean parameters of a circuit family.
A parameterized circuit is just a function returning a circuit object.
In the Ragu gadgets, a good example is the point-allocation circuit:

```lean
def circuit (curveParams : Spec.CurveParams p) : FormalCircuit (F p) unit Spec.Point := ...
```

The important point is that these parameters come *before* the circuit input type. In other words, they are part of Lean's definition of the circuit, not part of the witness or public/private inputs handled by the circuit itself.

## Instantiation by partial application

Because these are ordinary Lean function arguments, instantiating a parameterized circuit is just partial application.
For example:

```lean
Ragu.Circuits.Point.Alloc.circuit curveParams
```

means: first choose the compile-time parameter `curveParams`, then obtain a concrete formal circuit of type

```lean
FormalCircuit (F p) unit Spec.Point
```

After that, the resulting circuit can be used normally on symbolic inputs.


## Example: point on the curve

In `Ragu.Circuits.Point.Alloc`, the circuit is parameterized by curve parameters:

```lean
def circuit (curveParams : Spec.CurveParams p) : FormalCircuit (F p) unit Spec.Point :=
  {
    (elaborated curveParams) with
    Assumptions,
    Spec := (Spec curveParams),
    soundness := soundness curveParams,
    completeness := completeness curveParams
  }
```

The associated specification depends on the same parameter:

```lean
def Spec (curveParams : Spec.CurveParams p) (_input : Unit) (out : Spec.Point (F p)) :=
  out.isOnCurve curveParams
```

So `curveParams` is not a circuit input, but it is part of the Lean-level definition of the circuit family. Once it is fixed, it determines which curve equation the circuit enforces.
Notice that both `Assumptions` and `Spec` can depend on those parameters.
One final note, since those are just parameters, this forms an implicit "forall": soundness and completeness are generic over all possible choices of `Spec.CurveParams`.

### Concrete instantiation

In `Ragu.Circuits.Point.Spec`, the repository defines concrete parameters for the Pasta curves:

```lean
def EpAffineParams: Circuits.Point.Spec.CurveParams Core.Primes.p :=
{
  b := 5,
  ζ := 0x12ccca834acdba712caad5dc57aab1b01d1f8bd237ad31491dad5ebdfdfe4ab9,
  h_small_order := by native_decide
}
```

Instantiating the circuit with those parameters is just ordinary application:

```lean
Ragu.Circuits.Point.Alloc.circuit Ragu.Circuits.Point.Spec.EpAffineParams
```

After this application, the result is a concrete circuit over `F p` that allocates a point satisfying the curve equation determined by `EpAffineParams`.