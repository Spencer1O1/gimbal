**Status:** North-star example  
**Normative status:** Illustrative syntax, semantic requirements are intentional  
**Purpose:** Pressure-test value/computation separation, first-order algebraic effects, handlers, error propagation, and alternate test interpretations.

See [[Projects/CategoryLanguage/Language Experience and Syntax Sketch|Language Experience and Syntax Sketch]].

---

## 1. Scenario

This program sends an account-security notification.

It:

1. Loads a user profile.
2. Reads the current time.
3. Creates an email.
4. Sends the email.
5. Records an audit event.
6. Returns an explicit result.

The same program is run with:

- Production handlers
- Deterministic test handlers
- A handler that simulates failure

The example is intentionally limited to first-order effects.

Scoped resources are covered separately in [[Projects/CategoryLanguage/Examples/Resource-Safe File Processor|Resource-Safe File Processor]].

---

## 2. Domain Types

```text
module Examples.EffectsAndTesting

record User {
    id: UserId
    email: EmailAddress
    displayName: Text
}

record SecurityEvent {
    userId: UserId
    kind: SecurityEventKind
    occurredAt: Instant
}

variant SecurityEventKind {
    PasswordChanged
    NewDeviceLogin
    RecoveryEmailChanged
}

record Email {
    recipient: EmailAddress
    subject: Text
    body: Text
}

record EmailReceipt {
    messageId: MessageId
    acceptedAt: Instant
}
````

```
variant UserLookupError {
    UserNotFound(UserId)
    UserStoreUnavailable
}
```

```
variant EmailError {
    InvalidRecipient
    ProviderRejected
    ProviderUnavailable
}
```

```
variant AuditError {
    AuditStoreUnavailable
}
```

```
variant NotificationError {
    LookupFailed(UserLookupError)
    SendFailed(EmailError)
    AuditFailed(AuditError)
}
```

All recoverable failure is explicit coproduct data.

---

## 3. Effect Signatures

```
effect Users {
    find
        : UserId
       -> Result[User, UserLookupError]
}
```

```
effect Clock {
    now
        : Unit
       -> Instant
}
```

```
effect Mail {
    send
        : Email
       -> Result[EmailReceipt, EmailError]
}
```

```
effect Audit {
    record
        : SecurityEvent
       -> Result[Unit, AuditError]
}
```

These are first-order operations:

- Their parameters are values.
- Their results are values.
- They do not directly receive scoped computations.
- They may be interpreted by handlers.

The exact internal effect representation remains undecided.

The semantic requirement is that the computation layer be explicit and categorical.

---

## 4. Pure Email Construction

```
pure eventDescription
    : SecurityEventKind -> Text
=
    kind =>
        match kind {
            PasswordChanged =>
                "Your password was changed."

            NewDeviceLogin =>
                "A new device signed in to your account."

            RecoveryEmailChanged =>
                "Your recovery email was changed."
        }
```

```
pure emailSubject
    : SecurityEventKind -> Text
=
    kind =>
        match kind {
            PasswordChanged =>
                "Your password changed"

            NewDeviceLogin =>
                "New device sign-in"

            RecoveryEmailChanged =>
                "Your recovery email changed"
        }
```

```
pure buildEmail
    : User × SecurityEvent -> Email
=
    input => {
        recipient:
            input.first.email

        subject:
            emailSubject(input.second.kind)

        body:
            """
            Hello \(input.first.displayName),

            \(eventDescription(input.second.kind))

            Time: \(input.second.occurredAt)

            If this was not you, secure your account immediately.
            """
    }
```

`buildEmail` is a pure morphism.

It cannot read the clock or send the email itself.

---

## 5. Creating the Event

```
createSecurityEvent
    : UserId × SecurityEventKind
   ->{Clock}
      SecurityEvent
=
    input => do {
        occurredAt <- Clock.now()

        pure {
            userId: input.first,
            kind: input.second,
            occurredAt
        }
    }
```

This computation uses only `Clock`.

The effect appears in its type.

---

## 6. Notification Workflow

```
notifySecurityEvent
    : UserId × SecurityEventKind
   ->{Users, Clock, Mail, Audit}
      Result[EmailReceipt, NotificationError]
=
    input => do {
        user <- Users.find(input.first)
            |> Result.mapError(LookupFailed)
            |>? 

        event <- createSecurityEvent(input)

        email =
            buildEmail(user, event)

        receipt <- Mail.send(email)
            |> Result.mapError(SendFailed)
            |>? 

        _ <- Audit.record(event)
            |> Result.mapError(AuditFailed)
            |>? 

        pure Ok(receipt)
    }
```

The exact syntax is not committed.

The semantic ordering is:

```
load user
then read time
then send email
then record audit event
then return receipt
```

Because effects are present, sequencing is semantically observable.

The compiler must not reorder these operations unless a proof or effect law permits it.

---

## 7. Composition-Oriented View

The workflow should also have an inspectable compositional presentation.

Conceptually:

```
UserId × SecurityEventKind
    ⟶ Result[EmailReceipt, NotificationError]
```

inside a computation category generated by:

```
{Users, Clock, Mail, Audit}
```

The source language may elaborate `do` notation into categorical composition in that computation category.

The programmer should be able to inspect something conceptually similar to:

```
Users.find
>>> bind(
        user =>
            Clock.now
            >>> bind(
                    occurredAt =>
                        Mail.send(...)
                        >>> bind(
                                receipt =>
                                    Audit.record(...)
                                    >>> map(
                                            _ => receipt
                                        )
                            )
                )
    )
```

The actual elaborated form should use the selected value/computation semantics rather than an arbitrary monad encoding if the language adopts a richer structure.

---

## 8. Production Handlers

```
run notifySecurityEvent(
    UserId("user-42"),
    NewDeviceLogin
)
with {
    Users =
        PostgresUsers(databasePool)

    Clock =
        SystemClock

    Mail =
        TransactionalEmailProvider(apiKey)

    Audit =
        PostgresAudit(databasePool)
}
```

Each handler must be checked against its effect signature.

The compiler should know:

- Which operations are implemented
- Which effects are eliminated
- Which effects remain
- Which host capabilities are trusted
- Whether the handler is total
- Whether the handler may fail through declared results
- Whether the handler introduces further effects

A handler is not merely a map from effect names to arbitrary callbacks.

---

## 9. Deterministic Test Handlers

```
test "security email is sent and audited" {
    users =
        InMemoryUsers {
            UserId("user-42"): {
                id: UserId("user-42"),
                email: "spencer@example.com",
                displayName: "Spencer"
            }
        }

    clock =
        FixedClock(
            "2030-01-02T03:04:05Z"
        )

    mail =
        CaptureMail {
            receipt: {
                messageId: MessageId("message-1"),
                acceptedAt: "2030-01-02T03:04:06Z"
            }
        }

    audit =
        CaptureAudit

    result =
        run notifySecurityEvent(
            UserId("user-42"),
            NewDeviceLogin
        )
        with {
            Users = users
            Clock = clock
            Mail = mail
            Audit = audit
        }

    assert result.value
        == Ok({
            messageId: MessageId("message-1"),
            acceptedAt: "2030-01-02T03:04:06Z"
        })

    assert mail.messages
        == [
            {
                recipient: "spencer@example.com",
                subject: "New device sign-in",
                body: """
                Hello Spencer,

                A new device signed in to your account.

                Time: 2030-01-02T03:04:05Z

                If this was not you, secure your account immediately.
                """
            }
        ]

    assert audit.events
        == [
            {
                userId: UserId("user-42"),
                kind: NewDeviceLogin,
                occurredAt: "2030-01-02T03:04:05Z"
            }
        ]
}
```

The deterministic handlers interpret the same computation differently from production handlers.

The program itself is unchanged.

---

## 10. Simulating Lookup Failure

```
test "missing users return an explicit error" {
    result =
        run notifySecurityEvent(
            UserId("missing-user"),
            PasswordChanged
        )
        with {
            Users =
                AlwaysMissingUsers

            Clock =
                FixedClock(
                    "2030-01-02T03:04:05Z"
                )

            Mail =
                FailIfCalledMail

            Audit =
                FailIfCalledAudit
        }

    assert result.value
        == Err(
            LookupFailed(
                UserNotFound(
                    UserId("missing-user")
                )
            )
        )

    assert result.handledOperations
        == [
            Users.find(
                UserId("missing-user")
            )
        ]
}
```

`Mail` and `Audit` must not be invoked after the explicit failure is propagated.

This property follows from the selected sequencing and result-propagation semantics.

---

## 11. Simulating Mail Failure

```
test "mail failure prevents auditing" {
    result =
        run notifySecurityEvent(
            UserId("user-42"),
            PasswordChanged
        )
        with {
            Users =
                OneUser(exampleUser)

            Clock =
                FixedClock(
                    "2030-01-02T03:04:05Z"
                )

            Mail =
                AlwaysRejectMail

            Audit =
                FailIfCalledAudit
        }

    assert result.value
        == Err(
            SendFailed(
                ProviderRejected
            )
        )
}
```

This test establishes the intended source behavior.

It does not prove the general handler laws.

---

## 12. Alternative Audit Policy

A different handler may batch audit events:

```
run notifySecurityEvent(
    userId,
    kind
)
with {
    Users = productionUsers
    Clock = systemClock
    Mail = productionMail

    Audit =
        BufferedAudit {
            flushEvery: 100
        }
}
```

This may introduce additional effects or resources.

The handler type must expose them.

Conceptually:

```
BufferedAudit
    handles Audit
    introduces State, Database
```

The language must not claim that `Audit` has been fully eliminated while silently retaining new effects.

---

## 13. Transforming Effects

A handler may translate one effect into another:

```
handler AuditThroughConsole
    : Audit
   => Console
=
    operation record(event) =>
        Console.print(
            formatAuditEvent(event)
        )
        >>> pure Ok(Unit)
```

Applying the handler transforms the effect set:

```
{Users, Clock, Mail, Audit}
```

into:

```
{Users, Clock, Mail, Console}
```

This transformation should be reflected in the type.

---

## 14. Pure Versus Effectful Boundaries

The following is invalid:

```
pure notifySecurityEvent
    : UserId × SecurityEventKind
   -> Result[EmailReceipt, NotificationError]
```

because the implementation invokes:

- `Users.find`
- `Clock.now`
- `Mail.send`
- `Audit.record`

The compiler must reject the hidden effects.

Similarly, this is invalid:

```
pure currentTime
    : Unit -> Instant
=
    SystemClock.now()
```

Time access belongs to a computation effect.

---

## 15. Recoverable Failure Versus Handler Failure

The program distinguishes:

### Declared recoverable failure

```
Result[A, E]
```

Examples:

- User not found
- Email provider rejected the message
- Audit storage unavailable

### Effect interpretation fault

Examples:

- A handler returns a runtime value with the wrong object
- A supposedly total host callback panics
- A handler violates its declared operation contract
- The runtime cannot downcast an opaque payload

These are trusted runtime faults.

They do not inhabit `NotificationError` unless explicitly translated.

---

## 16. Expected Elaboration

### Effect invocation

```
Clock.now()
```

elaborates into an operation in the selected computation structure.

### `do` sequencing

```
x <- computation
rest
```

elaborates into composition or binding in the computation category.

### Error propagation

```
result |>? 
```

elaborates through explicit coproduct elimination.

It is not exception throwing.

### Handler application

```
run computation with { ... }
```

elaborates into one or more interpretations of effect structure.

### Pure embedding

```
pure value
```

embeds a value into the computation layer through the selected categorical connection.

---

## 17. Laws Required

The effect system must eventually specify and prove or derive:

- Identity of pure embedding
- Associativity of sequencing
- Handler compatibility with sequencing
- Operation interpretation laws
- Effect transformation composition
- Preservation of source and target types
- Correct effect elimination
- Correct propagation of unhandled effects
- Any laws assumed by compiler reordering or fusion

The source syntax alone is insufficient.

---

## 18. Semantic Questions Exposed by This Example

- What value/computation structure is selected?
- Is the source language call-by-value, call-by-name, or call-by-push-value based?
- How are effects represented in types?
- Are effect collections ordered?
- How are duplicate effects represented?
- How does `Result` failure interact with effects?
- Does `?` short-circuit through ordinary coproduct elimination or through a dedicated error effect?
- How are handlers composed?
- Can handlers introduce effects?
- How are handler laws represented?
- When may the compiler reorder independent effects?
- How is operation tracing represented without changing program semantics?
- What does it mean for a test handler to expose captured operations?

These questions must be resolved before the first-order effect phase is complete.

---

## 19. Acceptance Criteria

The eventual language passes this example when:

- Pure code cannot invoke effects.
- Effects remain visible in types.
- Recoverable failure remains explicit.
- Sequencing has a formal categorical semantics.
- Production and test handlers interpret the same computation.
- Handlers are typed and structure-aware.
- Handlers may transform effects explicitly.
- Introduced effects remain visible.
- Host faults are not confused with language errors.
- Compiler optimizations cannot reorder effects without justification.
- The elaborated computation can be inspected.