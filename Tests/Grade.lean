import Graded.Grade

/-! Examples instantiating every `Graded.Grade` lemma at a concrete error
    type, plus a `#guard` that computes via `decide`. -/

namespace Tests

inductive E | parse | range | io
  deriving DecidableEq, Repr

open Graded Graded.Grade

#guard join ({E.parse} : Graded.Grade E) {E.range} = join ({E.range} : Graded.Grade E) {E.parse}

example (g h k : Graded.Grade E) : join (join g h) k = join g (join h k) :=
  join_assoc g h k

example (g h : Graded.Grade E) : join g h = join h g :=
  join_comm g h

example (g : Graded.Grade E) : join g g = g :=
  join_idem g

example (g : Graded.Grade E) : join (bot : Graded.Grade E) g = g :=
  bot_join g

example (g : Graded.Grade E) : join g (bot : Graded.Grade E) = g :=
  join_bot g

example (g h : Graded.Grade E) : g ⊆ join g h :=
  le_join_left g h

example (g h : Graded.Grade E) : h ⊆ join g h :=
  le_join_right g h

example (g h k : Graded.Grade E) (hg : g ⊆ k) (hh : h ⊆ k) : join g h ⊆ k :=
  join_le hg hh

example (g g' h h' : Graded.Grade E) (hg : g ⊆ g') (hh : h ⊆ h') : join g h ⊆ join g' h' :=
  join_mono hg hh

example (g : Graded.Grade E) : g ⊆ g :=
  le_refl' g

example (g h k : Graded.Grade E) (hgh : g ⊆ h) (hhk : h ⊆ k) : g ⊆ k :=
  le_trans' hgh hhk

example (g : Graded.Grade E) : (bot : Graded.Grade E) ⊆ g :=
  bot_le g

example (g h : Graded.Grade E) (hgh : g ⊆ h) : join g h = h :=
  join_eq_right_of_le hgh

end Tests
