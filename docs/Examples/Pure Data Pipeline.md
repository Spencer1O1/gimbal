**Status:** North-star example  
**Normative status:** Illustrative syntax, semantic requirements are intentional  
**Purpose:** Pressure-test ordinary pure programming over records, variants, recursive data, pattern matching, composition, and folds.

See [[Projects/CategoryLanguage/Language Experience and Syntax Sketch|Language Experience and Syntax Sketch]].

---

## 1. Scenario

This program receives a sales report containing raw transactions.

It:

1. Rejects malformed transactions.
2. Converts valid transactions into normalized sales.
3. Groups sales by product category.
4. Computes totals.
5. Produces a summary report.

The entire program is pure and total.

It performs no:

- I/O
- Mutation
- Failure outside explicit coproducts
- Unrestricted recursion
- Hidden exceptions
- Time access
- Randomness

---

## 2. Domain Types

```text
module Examples.PureDataPipeline

record RawTransaction {
    id: TransactionId
    product: Text
    category: Text
    quantity: Int
    unitPrice: Money
}

record Sale {
    id: TransactionId
    product: ProductName
    category: Category
    quantity: PositiveInt
    unitPrice: Money
}

record CategoryTotal {
    category: Category
    unitsSold: Nat
    revenue: Money
}

record SalesSummary {
    transactionCount: Nat
    totalUnits: Nat
    totalRevenue: Money
    categories: List[CategoryTotal]
}

variant ValidationError {
    EmptyProduct(TransactionId)
    EmptyCategory(TransactionId)
    InvalidQuantity(TransactionId, Int)
    NegativePrice(TransactionId, Money)
}

Records elaborate into labeled products.

Variants elaborate into labeled coproducts.

List[A] is intended to arise from the initial algebra:

ListF[A, X] = Unit + A × X
List[A]     = μX. ListF[A, X]
3. Small Validation Functions
pure validateProduct
    : RawTransaction
   -> Result[ProductName, ValidationError]
=
    transaction =>
        match ProductName.fromText(transaction.product) {
            Some(product) =>
                Ok(product)

            None =>
                Err(
                    EmptyProduct(transaction.id)
                )
        }
pure validateCategory
    : RawTransaction
   -> Result[Category, ValidationError]
=
    transaction =>
        match Category.fromText(transaction.category) {
            Some(category) =>
                Ok(category)

            None =>
                Err(
                    EmptyCategory(transaction.id)
                )
        }
pure validateQuantity
    : RawTransaction
   -> Result[PositiveInt, ValidationError]
=
    transaction =>
        match PositiveInt.fromInt(transaction.quantity) {
            Some(quantity) =>
                Ok(quantity)

            None =>
                Err(
                    InvalidQuantity(
                        transaction.id,
                        transaction.quantity
                    )
                )
        }
pure validatePrice
    : RawTransaction
   -> Result[Money, ValidationError]
=
    transaction =>
        if transaction.unitPrice >= Money.zero {
            Ok(transaction.unitPrice)
        } else {
            Err(
                NegativePrice(
                    transaction.id,
                    transaction.unitPrice
                )
            )
        }

The if expression is Boolean coproduct elimination.

Conceptually:

Bool = Unit + Unit

The Result type is also coproduct structure.

4. Combining Independent Validation
pure validateTransaction
    : RawTransaction
   -> Result[Sale, List[ValidationError]]
=
    transaction =>
        Result.collect {
            product:
                validateProduct(transaction)

            category:
                validateCategory(transaction)

            quantity:
                validateQuantity(transaction)

            unitPrice:
                validatePrice(transaction)
        }
        |> Result.map(
            fields => {
                id: transaction.id,
                product: fields.product,
                category: fields.category,
                quantity: fields.quantity,
                unitPrice: fields.unitPrice
            }
        )

Result.collect is intended to accumulate independent validation errors.

Its exact implementation depends on the selected applicative structure for error accumulation.

It must not be presented as ordinary monadic sequencing if it accumulates multiple errors rather than stopping at the first.

The semantic distinction should remain explicit:

dependent validation
    uses sequential composition

independent validation
    may use applicative product structure

This example therefore pressures the language to distinguish:

Functorial mapping
Sequential dependent composition
Independent product-like validation

without introducing unrelated syntax for each.

5. Validating the Entire Input
pure validateAll
    : List[RawTransaction]
   -> Result[List[Sale], List[ValidationError]]
=
    List.traverse(validateTransaction)

List.traverse must arise from lawful structure associated with List and Result.

The compiler or library must know which laws are:

Derived
Proven
Trusted
Merely tested

The implementation must not special-case this exact pair of types in the compiler.

6. Calculating Sale Values
pure saleRevenue
    : Sale -> Money
=
    sale =>
        Money.multiply(
            sale.unitPrice,
            sale.quantity.toNat
        )
pure saleUnits
    : Sale -> Nat
=
    .quantity
    >>> PositiveInt.toNat

Field projection syntax elaborates into product projections.

The second definition emphasizes composition:

Sale
    ⟶ PositiveInt
    ⟶ Nat
7. Category Accumulation
record CategoryAccumulator {
    unitsSold: Nat
    revenue: Money
}
pure emptyCategoryAccumulator
    : Unit -> CategoryAccumulator
=
    _ => {
        unitsSold: Nat.zero,
        revenue: Money.zero
    }
pure addSale
    : CategoryAccumulator × Sale
   -> CategoryAccumulator
=
    input => {
        unitsSold:
            input.first.unitsSold
            + saleUnits(input.second)

        revenue:
            input.first.revenue
            + saleRevenue(input.second)
    }

The explicit product input:

CategoryAccumulator × Sale

matches the categorical shape of a fold algebra.

8. Grouping Sales
pure groupByCategory
    : List[Sale]
   -> Map[Category, List[Sale]]
=
    List.fold(
        initial: Map.empty,
        step:
            (groups, sale) =>
                groups.update(
                    sale.category,
                    existing =>
                        existing.append(sale),
                    default:
                        [sale]
                )
    )

This uses a fold over the initial algebra of List.

The implementation does not require unrestricted recursion.

The exact semantics of Map remain to be designed.

For this example, Map is treated as a pure persistent data structure.

It must not hide mutable state.

9. Summarizing One Category
pure summarizeCategory
    : Category × List[Sale]
   -> CategoryTotal
=
    input => {
        category:
            input.first

        unitsSold:
            input.second
            |> List.map(saleUnits)
            |> Nat.sum

        revenue:
            input.second
            |> List.map(saleRevenue)
            |> Money.sum
    }

Equivalent composition-oriented form:

pure categoryUnits
    : List[Sale] -> Nat
=
    List.map(saleUnits)
    >>> Nat.sum
pure categoryRevenue
    : List[Sale] -> Money
=
    List.map(saleRevenue)
    >>> Money.sum
pure summarizeCategory
    : Category × List[Sale]
   -> CategoryTotal
=
    input => {
        category: input.first,
        unitsSold: categoryUnits(input.second),
        revenue: categoryRevenue(input.second)
    }

The language should allow both point-free composition and explicit local expression syntax.

They must elaborate into the same semantic foundation.

10. Building the Final Summary
pure summarize
    : List[Sale] -> SalesSummary
=
    sales => {
        transactionCount:
            List.length(sales)

        totalUnits:
            sales
            |> List.map(saleUnits)
            |> Nat.sum

        totalRevenue:
            sales
            |> List.map(saleRevenue)
            |> Money.sum

        categories:
            sales
            |> groupByCategory
            |> Map.entries
            |> List.map(summarizeCategory)
            |> List.sortBy(.category)
    }

This is an ordinary pure program.

The user is not required to write raw categorical combinators for every projection and pairing.

The compiler should still be able to expose the elaborated structure.

11. Complete Pipeline
pure buildSalesSummary
    : List[RawTransaction]
   -> Result[SalesSummary, List[ValidationError]]
=
    validateAll
    >>> Result.map(summarize)

This is the central program:

List[RawTransaction]
    ⟶ Result[List[Sale], List[ValidationError]]
    ⟶ Result[SalesSummary, List[ValidationError]]

The composition should remain visible in compiler diagnostics and IR inspection.

12. Example Input
exampleTransactions
    : List[RawTransaction]
=
    [
        {
            id: "transaction-1",
            product: "Mechanical Keyboard",
            category: "Hardware",
            quantity: 2,
            unitPrice: $120.00
        },

        {
            id: "transaction-2",
            product: "Compiler Book",
            category: "Books",
            quantity: 1,
            unitPrice: $65.00
        },

        {
            id: "transaction-3",
            product: "USB Cable",
            category: "Hardware",
            quantity: 4,
            unitPrice: $8.50
        }
    ]
13. Example Evaluation
test "valid transactions produce a summary" {
    assert buildSalesSummary(exampleTransactions)
        == Ok({
            transactionCount: 3,
            totalUnits: 7,
            totalRevenue: $339.00,
            categories: [
                {
                    category: "Books",
                    unitsSold: 1,
                    revenue: $65.00
                },

                {
                    category: "Hardware",
                    unitsSold: 6,
                    revenue: $274.00
                }
            ]
        })
}
14. Validation Failure Example
test "independent errors are accumulated" {
    invalid =
        [
            {
                id: "transaction-1",
                product: "",
                category: "",
                quantity: 0,
                unitPrice: -$10.00
            }
        ]

    assert buildSalesSummary(invalid)
        == Err([
            EmptyProduct("transaction-1"),
            EmptyCategory("transaction-1"),
            InvalidQuantity("transaction-1", 0),
            NegativePrice("transaction-1", -$10.00)
        ])
}

This test requires Result.collect and List.traverse to preserve the intended error accumulation order deterministically.

That order must be either:

Semantically specified
Explicitly absent from equality
Or documented as presentation-only

It must not depend accidentally on hash-map iteration.

15. Expected Elaboration
Field access
sale.quantity

elaborates into a projection from the product representing Sale.

Record construction
{
    unitsSold: ...,
    revenue: ...
}

elaborates into product pairing.

Variant construction
Ok(value)
Err(error)

elaborates into coproduct injections.

Pattern matching
match result {
    Ok(value) => ...
    Err(error) => ...
}

elaborates into coproduct elimination.

Function application
f(x)

elaborates through pairing and evaluation.

Composition
f >>> g

remains explicit categorical composition.

List fold
List.fold(...)

elaborates through the catamorphism of the List initial algebra.

16. Semantic Questions Exposed by This Example

This example intentionally exposes future design questions:

What is the precise categorical structure of Result.collect?
How does the language distinguish applicative accumulation from monadic short-circuiting?
What laws does List.traverse require?
How are persistent maps represented categorically?
Is ordering part of Map.entries, or must sorting always be explicit?
How are numeric literals backed by signatures or later categorical numeric data?
Which source transformations are definitionally equal?
Which collection fusion rules require proofs?
How are overloaded operators such as + resolved without hidden category selection?

These questions do not block Phase 0 implementation.

They must be resolved before the corresponding source-language or recursive-data features are considered complete.

17. Acceptance Criteria

The eventual language passes this example when:

The program is readable without raw core combinators.
Every pure function is genuinely total and effect-free.
Validation failure is explicit.
Records and variants elaborate into products and coproducts.
List processing uses controlled structural recursion.
Composition remains visible and inspectable.
Independent validation accumulation has lawful semantics.
No compiler special case is required for this domain.
The elaborated program can be inspected as categorical structure.