**Status:** North-star example  
**Normative status:** Illustrative syntax, semantic requirements are intentional  
**Purpose:** Pressure-test linear or affine resources, borrowing, deterministic cleanup, failure, cancellation, and interaction between resources and effects.

See [[Projects/CategoryLanguage/Language Experience and Syntax Sketch|Language Experience and Syntax Sketch]] and [[Projects/CategoryLanguage/Computational Structure and Safety|Computational Structure and Safety]].

---

## 1. Scenario

This program transforms a large line-oriented data file.

It:

1. Opens an input file.
2. Opens an output file.
3. Reads the input incrementally.
4. Parses and validates each line.
5. Writes normalized records.
6. Reports progress.
7. Closes both files on every exit path.

The program must remain safe under:

- Normal completion
- Parse failure
- Read failure
- Write failure
- Early return
- Cancellation
- A nested handled effect
- A host runtime fault at a trusted boundary

The example is intended to expose whether the resource system is genuinely structural or merely conventional.

---

## 2. Domain Types

```text
module Examples.ResourceSafeFileProcessor

record InputPath {
    value: Text
}

record OutputPath {
    value: Text
}

record RawLine {
    number: Nat
    text: Text
}

record Record {
    id: RecordId
    name: Text
    score: Score
}

record ProcessingSummary {
    linesRead: Nat
    recordsWritten: Nat
    rejectedLines: Nat
}
variant ParseError {
    MissingField(Nat)
    InvalidId(Nat, Text)
    InvalidScore(Nat, Text)
}
variant FileError {
    NotFound(Text)
    PermissionDenied(Text)
    ReadFailed(Text)
    WriteFailed(Text)
    CloseFailed(Text)
}
variant ProcessingError {
    InputFailed(FileError)
    OutputFailed(FileError)
    InvalidLine(ParseError)
    Cancelled
}
3. Resource Types
resource ReadFile
resource WriteFile

These are not ordinary persistent values.

The language must not automatically provide:

ReadFile -> ReadFile × ReadFile

or:

ReadFile -> Unit

A file handle must be consumed, transferred, borrowed, or closed according to the resource semantics.

4. File Operations

Illustrative declarations:

effect Files {
    openRead
        : InputPath
       -> Result[resource ReadFile, FileError]

    openWrite
        : OutputPath
       -> Result[resource WriteFile, FileError]
}

Resource operations:

resource ReadFile {
    readLine
        : borrow ReadFile
       -> Result[Option[RawLine], FileError]

    close
        : consume ReadFile
       -> Result[Unit, FileError]
}
resource WriteFile {
    writeLine
        : borrow WriteFile × Text
       -> Result[Unit, FileError]

    flush
        : borrow WriteFile
       -> Result[Unit, FileError]

    close
        : consume WriteFile
       -> Result[Unit, FileError]
}

The exact syntax is undecided.

The intended distinctions are not:

borrow
consume
resource

must correspond to real typing and categorical structure.

5. Other Effects
effect Console {
    print
        : Text
       -> Unit
}
effect Cancellation {
    check
        : Unit
       -> Bool
}

Cancellation.check is first-order in this sketch.

A final structured-cancellation design may instead require scoped or higher-order effect semantics.

6. Pure Parsing
pure parseLine
    : RawLine -> Result[Record, ParseError]
=
    line =>
        match Text.split(line.text, ",") {
            [idText, name, scoreText] =>
                Result.collect {
                    id:
                        RecordId.parse(idText)
                        |> Result.mapError(
                            _ =>
                                InvalidId(
                                    line.number,
                                    idText
                                )
                        )

                    score:
                        Score.parse(scoreText)
                        |> Result.mapError(
                            _ =>
                                InvalidScore(
                                    line.number,
                                    scoreText
                                )
                        )
                }
                |> Result.map(
                    fields => {
                        id: fields.id,
                        name: Text.trim(name),
                        score: fields.score
                    }
                )

            _ =>
                Err(
                    MissingField(line.number)
                )
        }

This function is pure.

It cannot read another line, write output, or inspect cancellation.

7. Pure Rendering
pure renderRecord
    : Record -> Text
=
    record =>
        "\(record.id),\(record.name),\(record.score)"
8. Processing State
record ProcessingState {
    linesRead: Nat
    recordsWritten: Nat
    rejectedLines: Nat
}
pure initialState
    : Unit -> ProcessingState
=
    _ => {
        linesRead: 0,
        recordsWritten: 0,
        rejectedLines: 0
    }
pure markRead
    : ProcessingState -> ProcessingState
=
    state => {
        ...state,
        linesRead: state.linesRead + 1
    }
pure markWritten
    : ProcessingState -> ProcessingState
=
    state => {
        ...state,
        recordsWritten: state.recordsWritten + 1
    }
pure markRejected
    : ProcessingState -> ProcessingState
=
    state => {
        ...state,
        rejectedLines: state.rejectedLines + 1
    }

Record update syntax must elaborate into product reconstruction.

There is no hidden mutation in these pure functions.

9. Processing One Line
processLine
    : borrow WriteFile
    × ProcessingState
    × RawLine
   ->{Console}
      Result[ProcessingState, ProcessingError]
=
    input => do {
        output =
            input.first

        state =
            markRead(input.second)

        line =
            input.third

        match parseLine(line) {
            Ok(record) => do {
                _ <- output.writeLine(
                    renderRecord(record)
                )
                |> Result.mapError(OutputFailed)
                |>? 

                pure Ok(
                    markWritten(state)
                )
            }

            Err(error) => do {
                Console.print(
                    "Rejected line \(line.number): \(error)"
                )

                pure Ok(
                    markRejected(state)
                )
            }
        }
    }

The output file is borrowed.

processLine cannot:

Close it
Transfer ownership elsewhere
Store it in persistent state
Return it as a duplicated value

The borrow must end before the surrounding owner continues.

10. Recursive Processing Loop

The source language should avoid unrestricted recursion in pure code.

This loop is an effectful computation and may be potentially nonterminating if the input source is unbounded.

For a finite file, the file interface may expose a structured stream fold.

Preferred high-level form:

processLines
    : borrow ReadFile
    × borrow WriteFile
   ->{Console, Cancellation}
      Result[ProcessingSummary, ProcessingError]
=
    input =>
        FileLines.foldEffectful(
            source: input.first,
            initial: initialState(),
            step:
                state => line => do {
                    cancelled <- Cancellation.check()

                    if cancelled {
                        fail Cancelled
                    } else {
                        processLine(
                            input.second,
                            state,
                            line
                        )
                    }
                }
        )
        |> Result.map(
            state => {
                linesRead: state.linesRead,
                recordsWritten: state.recordsWritten,
                rejectedLines: state.rejectedLines
            }
        )

This pressures the design to provide a principled effectful fold over a finite resource-backed stream.

The fold must explain:

Who owns the read handle
How each borrow is scoped
Whether the stream is guaranteed finite
How cancellation exits
Which effects occur during each step
How cleanup is preserved
11. Scoped Resource Acquisition
transformFile
    : InputPath × OutputPath
   ->{Files, Console, Cancellation}
      Result[ProcessingSummary, ProcessingError]
=
    paths => do {
        with input <- Files.openRead(paths.first)
            |> Result.mapError(InputFailed)
            |>? 
        {
            with output <- Files.openWrite(paths.second)
                |> Result.mapError(OutputFailed)
                |>? 
            {
                summary <- processLines(
                    borrow input,
                    borrow output
                )?

                _ <- output.flush()
                    |> Result.mapError(OutputFailed)
                    |>? 

                pure Ok(summary)
            }
        }
    }

The with form must represent scoped ownership.

At the end of each scope, the resource is consumed by cleanup.

Conceptually:

with resource <- acquire {
    body
}

must guarantee cleanup around body.

This is a scoped or higher-order operation because it receives a computation whose lifetime is bounded by the resource scope.

It should not be falsely modeled as an ordinary first-order effect operation.

12. Cleanup Guarantees

The outer input resource and inner output resource must be closed in reverse acquisition order:

open input
open output
run body
close output
close input

This ordering must hold under:

Success
Parse rejection
Recoverable read failure
Recoverable write failure
Cancellation
Early return
Nested handled effects

The semantic system must answer what happens when:

body fails
and cleanup also fails

Possible policies include:

Preserve the original error and attach cleanup failure
Replace with a combined structured error
Prioritize cleanup failure
Treat cleanup failure as a runtime fault

The policy must be explicit.

13. Explicit Cleanup Expansion

The compiler may conceptually elaborate:

with output <- acquire {
    body
}

into a scoped handler or resource combinator:

bracket(
    acquire,
    use:
        output => body,
    release:
        output => output.close()
)

But bracket itself must have formal resource and effect semantics.

It cannot merely be a library function over unrestricted values if output is linear.

14. Invalid Programs
Duplicating a resource

This must fail:

with file <- Files.openRead(path)? {
    files = (file, file)
}

The resource cannot be duplicated.

Dropping a resource

This must fail unless the enclosing scope owns cleanup:

file <- Files.openRead(path)?
pure Unit

The compiler must know that ownership was abandoned.

Returning a borrowed resource

This must fail:

pure borrowFile
    : borrow ReadFile -> borrow ReadFile
=
    file => file

unless the lifetime system proves the returned borrow is valid in the caller’s scope.

Escaping a scoped resource

This must fail:

getFile
    : InputPath
   ->{Files}
      ReadFile
=
    path =>
        with file <- Files.openRead(path)? {
            pure file
        }

The owned file cannot escape after its cleanup scope ends.

Closing through a borrow

This must fail:

pure closeBorrowed
    : borrow ReadFile -> Unit
=
    file =>
        file.close()

Closing requires ownership consumption.

15. Cancellation Example
test "cancellation closes both files" {
    files =
        TrackedFiles {
            input: [
                "1,Alice,90",
                "2,Bob,85",
                "3,Carla,95"
            ]
        }

    cancellation =
        CancelAfterChecks(2)

    result =
        run transformFile(
            InputPath("input.csv"),
            OutputPath("output.csv")
        )
        with {
            Files = files
            Console = CaptureOutput
            Cancellation = cancellation
        }

    assert result.value
        == Err(Cancelled)

    assert files.events
        == [
            OpenRead("input.csv"),
            OpenWrite("output.csv"),
            ReadLine(1),
            WriteLine("1,Alice,90"),
            ReadLine(2),
            CloseWrite("output.csv"),
            CloseRead("input.csv")
        ]
}

The exact timing of cancellation checks must be specified.

Cleanup must not be skipped.

16. Write Failure Example
test "write failure still closes resources" {
    files =
        FailOnWriteFiles {
            failAtWrite: 2
        }

    result =
        run transformFile(
            InputPath("input.csv"),
            OutputPath("output.csv")
        )
        with {
            Files = files
            Console = CaptureOutput
            Cancellation = NeverCancel
        }

    assert result.value
        == Err(
            OutputFailed(
                WriteFailed("output.csv")
            )
        )

    assert files.outputWasClosed
    assert files.inputWasClosed
}
17. Nested Cleanup Failure
test "cleanup failure is represented explicitly" {
    files =
        CloseFailureFiles {
            outputCloseFails: true,
            inputCloseFails: false
        }

    result =
        run transformFile(
            InputPath("input.csv"),
            OutputPath("output.csv")
        )
        with {
            Files = files
            Console = CaptureOutput
            Cancellation = NeverCancel
        }

    assert result.value
        == Err(
            OutputFailed(
                CloseFailed("output.csv")
            )
        )
}

This example assumes cleanup failure is translated into the declared error.

The actual policy remains open and must be defined before the resource system is complete.

18. Resource Sharing

Some runtime resources may support safe shared access.

This must be explicit.

Illustrative declaration:

resource SharedReadFile
    capability Duplicate

or:

share
    : consume ReadFile
   -> Shared[ReadFile]

The system must not infer duplicability from the host implementation merely using an atomic reference count.

Semantic permission to duplicate is distinct from physical ability to clone a pointer.

19. Interaction with Effects

The resource scope may contain effects:

with output <- Files.openWrite(path)? {
    Console.print("Started")
    Clock.now()
    output.writeLine(...)
}

Handlers must not reorder these operations across acquisition or cleanup in a way that changes resource safety.

A handler that captures or resumes a continuation multiple times could duplicate resource use.

Therefore, resource scopes may impose restrictions on:

Resumption multiplicity
Continuation storage
Nondeterministic branching
Parallel execution
Handler ordering

This is a major reason resources cannot be bolted onto unrestricted ordinary algebraic effects.

20. Interaction with Concurrency

A future parallel version might process chunks concurrently.

The resource system must specify whether:

A file handle is transferable between tasks
A borrow may cross task boundaries
Writes are serialized
Output ordering is deterministic
Cancellation joins child tasks before cleanup
Cleanup waits for all borrows to end

The following must not be permitted without explicit sharing structure:

parallel {
    output.writeLine(a)
    output.writeLine(b)
}

using the same exclusive borrowed handle.

21. Expected Semantic Layers

This example likely involves at least:

persistent pure values
    RawLine
    Record
    ProcessingState
    ProcessingSummary

resource-sensitive values
    ReadFile
    WriteFile

effectful computations
    file operations
    console output
    cancellation

scoped higher-order structure
    resource acquisition and cleanup

The syntax may appear unified.

The compiler must preserve the distinctions.

22. Expected Elaboration
Resource acquisition
with file <- Files.openRead(path) {
    body
}

elaborates into a scoped resource construction with explicit acquisition, use, and release.

Borrowing
borrow file

creates a lifetime-bounded non-owning capability.

Consumption
file.close()

consumes ownership.

Effectful fold
FileLines.foldEffectful(...)

elaborates into a structured recursion or fold over the file stream computation.

Cancellation propagation
fail Cancelled

is explicit computation failure.

It must not bypass cleanup.

23. Laws and Proof Obligations

The resource system must eventually establish properties such as:

A consumed resource cannot be reused.
An exclusive resource cannot be duplicated.
Borrows do not outlive owners.
Cleanup occurs at most once.
Cleanup occurs on every permitted scope exit.
Cleanup ordering is deterministic.
Handler transformations preserve resource invariants.
Cancellation preserves cleanup.
Parallel composition respects exclusivity.
Safe abstractions cannot expose invalid ownership states.

Some properties may be guaranteed by typing.

Others may require handler laws or formal proofs.

24. Semantic Questions Exposed by This Example
Is the resource discipline linear or affine?
What is the exact persistent/resource adjunction?
What modality marks duplicable resources?
Are borrows first-class values?
How are lifetimes represented?
Are lifetimes inferred or explicit?
How are scoped resource operations represented?
How are cleanup failures combined with body failures?
May handlers resume resource-using computations more than once?
How does cancellation interact with linear continuations?
How are finite file streams represented?
Is effectful folding primitive or derived?
When may resources cross thread boundaries?
How is unsafe host ownership represented at the FFI boundary?

These questions must be answered before resource safety can be claimed.

25. Acceptance Criteria

The eventual language passes this example when:

File handles are not unrestricted cartesian values.
Resource duplication is rejected structurally.
Resource abandonment is rejected or handled by an enclosing scope.
Borrows cannot escape valid lifetimes.
Cleanup is guaranteed across all ordinary exits.
Cancellation preserves cleanup.
Handler behavior cannot duplicate linear continuations illegally.
Resource effects remain visible.
Host ownership assumptions are explicit.
The compiler can explain ownership and cleanup errors.
The elaborated resource and effect structures can be inspected.