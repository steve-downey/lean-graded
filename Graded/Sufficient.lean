import Graded.Sufficient.MonadK
import Graded.Sufficient.ApplicativeK
import Graded.Sufficient.TraversableK
import Graded.Sufficient.ComposeK
import Graded.Sufficient.CompK
import Graded.Sufficient.TupleK
import Graded.Sufficient.MorphismK

/-! The sufficient-grade layer, as one import.

    This file used to be the layer: eleven hundred lines carrying
    `bindK`, `apK`, `traverseK`, `flattenK`, `Comp.apK` and `GradedHomK`
    together. [module-split] broke it into six, and what remains here is
    a **re-export shim**: every name that was importable from
    `Graded.Sufficient` still is, so no consumer changed.

    The split exists because importing `bindK` should not import
    traversal. The pieces, in dependency order:

    | module | holds | imports beyond its predecessor |
    |---|---|---|
    | `.MonadK` | `bindK`, `pureK`, the monad laws | `Graded.Monad` only |
    | `.ApplicativeK` | `apK`, `map2K`, `apFlippedK` | `Graded.Applicative` |
    | `.TraversableK` | `traverseK` and its laws | `Graded.Traverse` |
    | `.ComposeK` | `flattenK` | `Graded.Compose` |
    | `.CompK` | `Comp.apK`, `traverseCompK` | `Graded.ComposeApp` |
    | `.TupleK` | `sequenceK`, heterogeneous | `Graded.Tuple` |
    | `.MorphismK` | `GradedHomK`, the bridge, `constHomK` | `Graded.Morphism` |

    `.MonadK` is the one that matters for the boundary: it imports
    `Graded.Monad` and nothing else, so it reaches `Widen`, `Carrier`,
    `Signature`, `Grade` and `Prelude` and stops. Traversal, composition
    and the morphism records are not behind it.

    Prefer importing the piece you need. Importing this file is correct
    and costs what the whole layer costs. -/
