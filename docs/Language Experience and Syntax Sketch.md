**Status:** North-star design sketch  
**Normative status:** Illustrative, not final syntax  
**Purpose:** Show what complete end-user programs should feel like before the surface language is formally designed.

---

## 1. Purpose

The semantic kernel is designed from the category theory upward.

The surface language must also be designed from the programmer downward.

This document describes the intended experience of writing ordinary programs in the completed language.

It is not a grammar specification.

Exact punctuation, keywords, delimiters, effect notation, and declaration syntax remain open.

The examples instead establish higher-level requirements:

- Ordinary programs must be readable without exposing raw categorical combinators everywhere.
- Composition must remain a visible and useful programming operation.
- Pure functions must actually be total and pure.
- Failure, effects, nontermination, and resources must remain explicit.
- Records, variants, functions, pattern matching, and recursive data must elaborate into genuine categorical structures.
- Handlers and interpreters must have semantic meaning rather than acting as dependency-injection syntax.
- Resource safety must arise from a noncartesian semantic layer.
- Advanced programmers must be able to inspect and directly use the categorical structures beneath ordinary syntax.
- Surface conveniences must elaborate into the verified semantic architecture.

The language should feel like a practical general-purpose language with an unusually coherent foundation.

It should not feel like manually assembling `first`, `pair`, `curry`, and `eval` for every ordinary calculation.

---

## 2. What Is Already Committed

The final syntax is not committed, but the following user-visible properties are.

### Composition is first-class syntax

Given:

```text
f : A -> B
g : B -> C
````

the programmer can write:

```
f >>> g
```

to construct:

```
A -> C
```

Composition is not merely a library function over host-language functions.

The compiler preserves and reasons about the resulting composition.

### Pure functions are honest

A pure declaration cannot secretly:

- Fail
- Diverge
- Perform I/O
- Read time
- Use randomness
- Mutate external state
- Acquire resources
- Panic

Such behavior must be represented in the type and semantic layer of the program.

### Ordinary syntax elaborates into categorical structure

Conceptually:

```
record
    ↓
product structure

variant
    ↓
coproduct structure

function value
    ↓
exponential object

lambda
    ↓
currying

application
    ↓
pairing followed by evaluation

pattern matching
    ↓
coproduct elimination

inductive data
    ↓
initial algebra

fold
    ↓
catamorphism

effect handler
    ↓
interpretation of computational structure

resource scope
    ↓
resource-sensitive semantic construction
```

### Semantic layers remain visible

The language distinguishes among:

```
persistent pure values
resource-sensitive values
effectful computations
potentially nonterminating computations
proofs
compile-time programs
```

These may use convenient unified syntax, but they are not silently collapsed into one unrestricted category.

### Elaboration is inspectable

The compiler should expose commands conceptually similar to:

```
category inspect --parsed checkout
category inspect --resolved checkout
category inspect --typed checkout
category inspect --core checkout
category inspect --simplified checkout
category inspect --effects checkout
category inspect --resources checkout
category inspect --proofs checkout
category inspect --lowered checkout
```

The exact command name is undecided.

---

## 3. Surface Type Sketch

The source language should provide familiar syntax for common categorical structures.

### Records

```
record Item {
    name: Text
    price: Money
}
```

A record is a labeled product.

### Variants

```
variant CheckoutError {
    EmptyOrder
    PaymentFailed(PaymentError)
}
```

A variant is a labeled coproduct.

### Pure functions

```
total : List[Item] -> Money
```

A pure function type denotes a morphism in the persistent pure-value category.

### Effectful functions

Illustrative effect notation:

```
checkout
    : Order
   ->{Payments, Clock}
      Result[PaidOrder, CheckoutError]
```

This denotes a computation using the listed effects.

It is not a pure morphism disguised as a function.

### Resource-sensitive values

Illustrative declaration:

```
resource Connection
```

A `Connection` does not inhabit the unrestricted cartesian value category.

It cannot automatically be duplicated or discarded.

### Potentially nonterminating computations

Illustrative notation:

```
serve
    : Server
   ->{Network, Async, Divergence}
      Never
```

The final nontermination representation remains undecided.

---

## 4. Canonical Full Program

The canonical north-star example is a small order-processing application.

It demonstrates:

- Records
- Variants
- Pure transformations
- Recursive data
- Composition
- Pattern matching
- Explicit effects
- Effect handlers
- Resource safety
- Testing through alternate interpretations
- Inspectable elaboration

The syntax is illustrative.

---

## 5. Domain Types

```
module Store.Checkout

record Item {
    name: Text
    price: Money
}

record Customer {
    id: CustomerId
    email: EmailAddress
}

record Order {
    id: OrderId
    customer: Customer
    items: List[Item]
}

record ChargeRequest {
    customer: Customer
    amount: Money
}

record Receipt {
    id: ReceiptId
    amount: Money
}

record PaidOrder {
    order: Order
    receipt: Receipt
    paidAt: Instant
}

variant PaymentError {
    CardDeclined
    ProviderUnavailable
    InvalidPaymentMethod
}

variant CheckoutError {
    OrderNotFound(OrderId)
    EmptyOrder
    PaymentFailed(PaymentError)
    StorageFailed(StorageError)
}
```

The semantic structures are:

```
Item
    labeled product

Customer
    labeled product

Order
    labeled product containing an inductive List

PaymentError
    labeled coproduct

CheckoutError
    labeled coproduct with nested payloads
```

The source names and labels are preserved for diagnostics and tooling.

The core elaboration ultimately uses products and coproducts.

---

## 6. Effect Signatures

```
effect Payments {
    charge : ChargeRequest -> Result[Receipt, PaymentError]
}

effect Clock {
    now : Unit -> Instant
}

effect Console {
    print : Text -> Unit
}

effect Database {
    connect : DatabaseConfig -> resource Connection
}
```

`Payments`, `Clock`, and `Console` are shown as first-order effect signatures.

`Database.connect` produces a resource-sensitive value and may require a scoped or higher-order effect construction in the final semantics.

The uniform appearance of these declarations does not imply that every operation has the same categorical implementation.

---

## 7. Resource Operations

```
resource Connection {
    loadOrder
        : borrow Connection × OrderId
       -> Result[Order, StorageError]

    close
        : consume Connection
       -> Unit
}
```

The exact ownership syntax is undecided.

The intended distinctions are:

```
borrow Connection
```

temporarily uses the connection without consuming it.

```
consume Connection
```

uses ownership of the connection exactly once.

A resource value cannot be copied merely because an ordinary record can be copied.

---

## 8. Pure Functions

### Calculating an order total

```
pure total
    : List[Item] -> Money
=
    List.map(.price)
    >>> Money.sum
```

This is a composition of pure morphisms.

`List.map` is the functorial action associated with the list construction.

`Money.sum` may be defined as a fold:

```
pure Money.sum
    : List[Money] -> Money
=
    List.fold(
        initial: Money.zero,
        step: Money.add
    )
```

The fold arises from the initial-algebra structure of `List`.

It is not unrestricted recursion.

### Validating an order

```
pure validate
    : Order -> Result[Order, CheckoutError]
=
    order =>
        match order.items {
            [] =>
                Err(EmptyOrder)

            _ =>
                Ok(order)
        }
```

The pattern match elaborates into elimination of the recursive list structure and coproduct construction for `Result`.

### Creating a charge request

```
pure makeCharge
    : Order -> ChargeRequest
=
    order => {
        customer: order.customer,
        amount: total(order.items)
    }
```

The record expression elaborates into product construction.

Field access elaborates into labeled projections.

### Composing the validation pipeline

```
pure prepareCharge
    : Order -> Result[ChargeRequest, CheckoutError]
=
    validate
    >>> Result.map(makeCharge)
```

This pipeline is categorically meaningful.

`Result.map` is the functorial action on the successful branch of the result coproduct.

Conceptually:

```
validate
    : Order -> Order + CheckoutError

Result.map(makeCharge)
    : Order + CheckoutError
   -> ChargeRequest + CheckoutError
```

Their composition is:

```
Order -> ChargeRequest + CheckoutError
```

The compiler may preserve the source-level `Result` name while the core sees the underlying coproduct structure.

---

## 9. Effectful Checkout

```
checkout
    : Order
   ->{Payments, Clock}
      Result[PaidOrder, CheckoutError]
=
    order => do {
        request <- prepareCharge(order)?

        receipt <- Payments.charge(request)
            |> Result.mapError(PaymentFailed)
            |>? 

        paidAt <- Clock.now()

        pure Ok({
            order,
            receipt,
            paidAt
        })
    }
```

The exact `do`, `?`, `|>`, and effect-row syntax is not committed.

The semantic requirements are:

1. `prepareCharge` remains pure.
2. Failure from `prepareCharge` is explicit coproduct data.
3. `Payments.charge` is an effect operation.
4. `Clock.now` is an effect operation.
5. Sequencing occurs in the computation semantics.
6. `PaymentError` is explicitly translated into `CheckoutError`.
7. The function cannot be typed as a pure `Order -> PaidOrder`.

Conceptually, `?` performs typed propagation through the `Result` coproduct.

It is not a hidden exception.

---

## 10. Rendering Results

```
pure renderResult
    : Result[PaidOrder, CheckoutError] -> Text
=
    result =>
        match result {
            Ok(paid) =>
                "Order \(paid.order.id) paid at \(paid.paidAt)."

            Err(OrderNotFound(id)) =>
                "Order \(id) was not found."

            Err(EmptyOrder) =>
                "The order contains no items."

            Err(PaymentFailed(CardDeclined)) =>
                "Payment failed because the card was declined."

            Err(PaymentFailed(ProviderUnavailable)) =>
                "The payment provider is unavailable."

            Err(PaymentFailed(InvalidPaymentMethod)) =>
                "The payment method is invalid."

            Err(StorageFailed(error)) =>
                "The order could not be loaded: \(error.message)"
        }
```

The match must be exhaustive.

There is no hidden universal `null` and no unchecked default branch.

The compiler can derive exhaustiveness from the coproduct structure.

---

## 11. Composing the Effectful Workflow

```
processOrder
    : Order
   ->{Payments, Clock, Console}
      Unit
=
    checkout
    >>> Computation.map(renderResult)
    >>> Console.print
```

This is intended to remain recognizable as composition even though it occurs in a computation category rather than the Phase 0 pure category.

The exact operator may remain `>>>` if the morphisms inhabit the same explicitly selected category.

The compiler must never guess an ambiguous category silently.

If category selection cannot be inferred uniquely, the programmer must make it explicit.

Conceptually:

```
checkout
    : Order ⟶ Result[PaidOrder, CheckoutError]

renderResult lifted into computations
    : Result[PaidOrder, CheckoutError] ⟶ Text

Console.print
    : Text ⟶ Unit
```

where these arrows belong to the selected computational category.

---

## 12. Loading an Order with a Resource

```
loadAndProcess
    : DatabaseConfig × OrderId
   ->{Database, Payments, Clock, Console}
      Unit
=
    input => do {
        with connection <- Database.connect(input.first) {
            loaded <- connection.loadOrder(input.second)

            match loaded {
                Ok(order) =>
                    processOrder(order)

                Err(error) =>
                    Console.print(
                        renderResult(
                            Err(StorageFailed(error))
                        )
                    )
            }
        }
    }
```

The `with` block establishes a resource scope.

The final language must guarantee:

- `connection` cannot escape the scope.
- `connection` cannot be duplicated unless explicitly shareable.
- The connection is closed on normal completion.
- The connection is closed after recoverable failure.
- The connection is closed during cancellation.
- The connection is closed when a nested effect aborts the computation.
- Cleanup behavior is derived from the resource semantics.

This cannot be implemented merely as:

```
remember to call close()
```

or as a hidden backend convention.

---

## 13. Program Entry Point

```
main
    : Unit
   ->{Arguments, Database, Payments, Clock, Console}
      ExitCode
=
    _ => do {
        arguments <- Arguments.read()

        match arguments {
            ["checkout", orderIdText] =>
                match OrderId.parse(orderIdText) {
                    Ok(orderId) => do {
                        loadAndProcess(config, orderId)
                        pure ExitCode.success
                    }

                    Err(error) => do {
                        Console.print(
                            "Invalid order id: \(error.message)"
                        )

                        pure ExitCode.invalidInput
                    }
                }

            _ => do {
                Console.print(
                    "Usage: store checkout <order-id>"
                )

                pure ExitCode.invalidInput
            }
        }
    }
```

The program is still explicit about:

- Argument access
- Parsing failure
- Database access
- Payments
- Time
- Console output
- Exit status

None of these are silently permitted inside a pure function.

---

## 14. Providing Runtime Interpretations

A production entry point supplies handlers or interpreters:

```
run main()
with {
    Arguments = ProcessArguments
    Database  = PostgresDatabase(databaseUrl)
    Payments  = StripePayments(apiKey)
    Clock     = SystemClock
    Console   = StandardOutput
}
```

This should not be mere string-keyed dependency injection.

Each supplied handler must have a checked relationship to the effect or resource signature it interprets.

The compiler should know:

- Which operations are handled
- Which effects remain
- Which resources are introduced
- Which laws or trust assumptions apply
- Whether the interpretation is pure, effectful, trusted, or verified

---

## 15. Testing Through Alternate Interpretations

```
test "declined cards produce a clear message" {
    captured =
        run loadAndProcess(
            TestDatabase.config,
            OrderId("order-123")
        )
        with {
            Database =
                InMemoryDatabase {
                    orders: {
                        "order-123": exampleOrder
                    }
                }

            Payments =
                AlwaysDecline

            Clock =
                FixedClock(
                    "2030-01-01T00:00:00Z"
                )

            Console =
                CaptureOutput
        }

    assert captured.output
        == [
            "Payment failed because the card was declined."
        ]
}
```

The same program is interpreted with different handlers.

This supports testing because the computation is separated from a specific runtime interpretation.

The test handler is not allowed to violate the declared operation types.

---

## 16. Testing Pure Categorical Laws

```
property "preparing an empty order fails" {
    order <- generate Order
        where order.items == []

    assert prepareCharge(order)
        == Err(EmptyOrder)
}
```

For a user-defined functor or category, a test may supplement proof:

```
property "mapping preserves composition" {
    f <- generate Morphism[A, B]
    g <- generate Morphism[B, C]
    x <- generate F[A]

    assert map(f >>> g)(x)
        == (map(f) >>> map(g))(x)
}
```

Tests do not establish laws required for trusted compiler transformations.

Such laws require proof, derivation, or visible trust.

---

## 17. Inspecting Elaboration

The programmer should be able to inspect:

```
pure prepareCharge
    : Order -> Result[ChargeRequest, CheckoutError]
=
    validate
    >>> Result.map(makeCharge)
```

at multiple levels.

### Source view

```
validate
>>> Result.map(makeCharge)
```

### Resolved view

```
Store.Checkout.validate
>>> Core.Result.map[Order, ChargeRequest, CheckoutError](
        Store.Checkout.makeCharge
    )
```

### Product and coproduct view

Conceptually:

```
validate
>>>
case(
    makeCharge >>> left[ChargeRequest, CheckoutError],
    right[ChargeRequest, CheckoutError]
)
```

### Checked categorical view

```
prepareCharge
    : Order
    ⟶ ChargeRequest + CheckoutError
```

### Simplified view

The simplifier may reduce any redundant identities, projections, or rebuilt structures while preserving the same arrow type.

This inspectability is essential.

The surface language may be convenient without concealing its semantics permanently.

---

## 18. Raw Core Programming Remains Available

Advanced users, compiler developers, tests, and metaprograms may construct explicit core terms:

```
not =
    case(
        right[Unit, Unit],
        left[Unit, Unit]
    )
```

or:

```
uncurry(k) =
    pair(
        first[X, A] >>> k,
        second[X, A]
    )
    >>> eval[A, B]
```

Ordinary users should rarely need to write this form.

It remains available because:

- It is the trusted elaboration target.
- It is useful for teaching and debugging.
- It exposes the real categorical structure.
- Compile-time programs may construct it directly.
- Proof and compiler tooling may reason over it.

---

## 19. User-Defined Category Sketch

Advanced users should eventually be able to define an external category.

Illustrative syntax:

```
category Migration {
    object Schema

    morphism Change[
        source: Schema,
        target: Schema
    ]

    id[A: Schema]
        : Change[A, A]

    compose[A, B, C]
        : Change[A, B] × Change[B, C]
       -> Change[A, C]

    law leftIdentity
    law rightIdentity
    law associativity
}
```

A program in this category may be:

```
upgrade
    : Change[SchemaV1, SchemaV4]
=
    addEmailColumn
    >>> normalizePhoneNumbers
    >>> splitAddressTable
```

A functorial interpretation might be:

```
functor execute
    : Migration -> DatabaseProgram
{
    object schema =>
        RuntimeSchema[schema]

    morphism change =>
        compileMigration(change)

    preserves identity by
        executeIdentityProof

    preserves composition by
        executeCompositionProof
}
```

The compiler must not accept `execute` as a functor merely because it has methods named `object` and `morphism`.

Preservation laws require:

- Construction guarantees
- Compiler derivation
- Machine-checked proofs
- Or explicit visible trust

---

## 20. Proven Equality Sketch

A user may prove a domain-specific equality:

```
theorem mapFusion
    [F: Functor]
    (f: A -> B)
    (g: B -> C)
:
    F.map(f)
    >>> F.map(g)
    =
    F.map(f >>> g)
=
    F.preservesComposition(f, g)
```

This is proven equality.

It does not become Phase 0 definitional equality.

A compiler optimization may use the theorem because explicit proof evidence accompanies the transformation.

---

## 21. Compile-Time Language Construction Sketch

A typed compile-time elaborator might eventually construct checked terms:

```
elaborator query {
    input:
        QuerySyntax

    output:
        Morphism[Database, ResultSet]

    elaborate syntax =>
        buildQueryPlan(syntax)
        >>> optimizeWithProofs
        >>> verify
}
```

The generated program must still pass through the trusted kernel.

The elaborator may propose syntax, terms, morphisms, proofs, or lowering steps.

It may not bypass checking.

---

## 22. Surface Simplicity Requirements

The language should optimize for these ordinary forms:

```
value.field
```

rather than requiring explicit projections.

```
f(x)
```

rather than requiring explicit `pair` and `eval`.

```
match value { ... }
```

rather than requiring explicit `case`.

```
{ x, y }
```

rather than requiring explicit product constructors.

```
Ok(value)
```

rather than requiring explicit coproduct injections.

```
items.map(f)
```

or:

```
List.map(f)(items)
```

rather than exposing recursion schemes for every ordinary use.

However, the compiler must know and expose what these forms mean categorically.

---

## 23. What Must Not Happen

The final language must not become:

### A conventional language with categorical names

```
interface Functor {
    map(...)
}
```

is not enough by itself.

The compiler must understand the structure and its laws.

### A core-combinator-only language

Users should not need to manually write projection trees for routine programs.

### A hidden-effect language

A function typed:

```
A -> B
```

cannot secretly perform I/O or fail.

### A fake resource system

The compiler cannot treat a cartesian object as freely duplicable and then add scattered special cases saying it is not.

### A rewrite-rule free-for-all

User equations cannot silently enter kernel definitional equality.

### An implicit category guessing system

When multiple categorical interpretations are possible, the compiler must not make invisible arbitrary choices.

### A proof burden for ordinary programming

Users should not need to prove category laws to define an ordinary record transformation.

Proof obligations should arise when users define new trusted structure or request law-dependent behavior.

---

## 24. Syntax Decisions Still Open

The following are intentionally not locked:

- `fn` versus declaration-only syntax
- Whether `pure` is written or inferred
- `->` versus another source arrow
- Effect-row notation
- Handler syntax
- `do` notation
- Error-propagation syntax
- Pipe syntax
- Lambda syntax
- Record delimiters
- Variant declaration syntax
- Module syntax
- Resource ownership keywords
- Borrow syntax
- Generic parameter syntax
- Proof syntax
- Category declaration syntax
- Functor declaration syntax
- Command-line tool names

These should be chosen after testing complete examples for:

- Readability
- Ambiguity
- Elaboration clarity
- Error diagnostics
- Categorical consistency
- Editor tooling

---

## 25. North-Star User Experience

An ordinary programmer should be able to think:

```
I am transforming an order,
performing a payment,
using a database connection safely,
and printing the result.
```

The compiler should simultaneously understand:

```
This portion is a pure morphism.
This record is product structure.
This result is coproduct structure.
This function value uses an exponential.
This list fold is an initial-algebra morphism.
This operation belongs to a computation category.
This handler is an interpretation.
This connection inhabits a resource-sensitive category.
This cleanup follows from the resource semantics.
This optimization uses a proven equality.
```

The category theory should make the language more coherent, safe, compositional, inspectable, and optimizable.

It should not make routine programming needlessly ceremonial.

---

## 26. Planned Companion Examples

Future example documents should explore individual capabilities in greater depth:

```
Examples/
    Command-Line Application.md
    Resource-Safe Database Program.md
    Recursive Data and Folds.md
    Algebraic Effects and Handlers.md
    Scoped Effects and Cancellation.md
    Linear Resources and Ownership.md
    Parametric Library Design.md
    User-Defined Category.md
    Proven Optimization.md
    Compile-Time DSL.md
```

Each example should include:

1. The complete surface program.
2. Its inferred types and effects.
3. Its resource behavior.
4. Its elaborated categorical structures.
5. Its proof obligations.
6. Its runtime interpretation.
7. Any remaining trust boundaries.