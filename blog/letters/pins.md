# Source pins for the Lean letters

Verbatim source excerpts in the Org letters use `orgit-file` links. Each link
names an annotated `blog/<letter-basename>` tag and a file/line range at the
revision where that letter's prose and quoted source last agreed. Moving
branches and later refactors therefore cannot silently rewrite a published
letter.

| Letter | Pinned commit |
|---|---|
| `applicative-from-monad` | `fc9db03` |
| `canonical-representation` | `fc9db03` |
| `grade-join-strength` | `a812b07` |
| `graded-morphism` | `fc9db03` |
| `monad-laws` | `fc9db03` |
| `morphism-bridge` | `8e7e1f9` |
| `oracle-export` | `fc9db03` |
| `payload-carrier` | `96548e1` |
| `subsumption-widen` | `fc9db03` |
| `traverse-tuple` | `fc9db03` |
| `ungraded-baseline` | `fc9db03` |

Abbreviated examples, compiler diagnostics, and pseudocode remain ordinary
inline source blocks: they are explanatory text rather than verbatim source
inclusions.
