import Graded.Grade

/-! What an error *is*, separated from which errors a grade admits.

    Every module before this one treats an error kind as the whole error:
    `Graded.err e he` records *that* an `e`-shaped failure happened and
    nothing about it. `docs/design.md#cpp-counterpart` says otherwise, and
    always has — "An instance holds **one** error value, whose type is in
    the set." A C++ `error_set<Es...>` selects an error *type*; an
    instance stores a value of it. Parse errors carry a location, range
    errors carry the bound that was exceeded, I/O errors carry an errno.
    The model could not state a single law about any of that.

    An `ErrorSignature` is the missing half: a type of kinds, and for each
    kind the type of payload it carries. The grade stays what it was, a
    `Finset` of *kinds* — payloads are not part of what a signature
    admits, which is why `error_set<parse_error>` is one type however much
    data a parse error turns out to carry.

    **The tag-only signature is a specialization, not an analogue.**
    `tagOnly Err` gives every kind the payload `PUnit`, and
    `Graded/Carrier.lean` defines the original carrier as
    `ExpectedG (tagOnly Err)` — definitionally, not through an
    equivalence. That choice is the whole cost profile of this step: an
    `Equiv` would leave every existing theorem needing transport, where a
    definitional specialization leaves them proved. See
    `docs/design.md#payloads` for what it bought. -/

namespace Graded

universe u v

/-- A type of error kinds, and the payload each kind carries. -/
structure ErrorSignature where
  /-- The error kinds. This is what a grade is a finite set of. -/
  Kind : Type u
  /-- What a failure of each kind carries. -/
  Payload : Kind → Type v

/-- The tag-only signature: every kind carries no information beyond
    having happened. Declared `abbrev` rather than `def` **deliberately**
    — instance search has to see through `(tagOnly Err).Kind` to `Err` to
    find `DecidableEq`, and through `(tagOnly Err).Payload k` to `PUnit`
    to elaborate `⟨⟩`. A `def` makes both opaque and the specialization
    stops working, with errors that point at the use site rather than
    here.

    The payload universe is pinned to `0` (`Unit`, not a polymorphic
    `PUnit`). Left free it becomes an unsolvable constraint at the
    specialization: `ExpectedG` lives in `Type (max u v_payload w)`, and
    `Graded`'s result universe can only be stated as `max u v` if the
    payload universe is known to be no larger. Pinning it is the honest
    fix, and it costs nothing — a tag carries no data, so there is no
    payload to be polymorphic about. Real signatures keep a free payload
    universe; only this one is pinned. -/
abbrev tagOnly (Err : Type u) : ErrorSignature.{u, 0} := ⟨Err, fun _ => Unit⟩

end Graded
