# Letter 30: A third of the inventory vanished and the check said fine

Steve,


# What I set out to do

One file in this model had grown to eleven hundred lines. It held sequencing at a caller-chosen grade, and applying, and traversing, and flattening, and the nested composite, and the two morphism records. All of it together, because each leg of the migration was added to the end of the previous one and nobody stopped to ask whether they belonged in the same place.

The cost is not aesthetic. If you want the first of those, you get all six, and everything they in turn depend on. A second file had the same problem from the other direction: canonicalization needed one fold over a list of grades and one theorem about reordering it, and to get them it imported the entire heterogeneous tuple development.

So: split it, keep every existing import working, and check the boundary instead of asserting it.


# What the checker refused

Nothing, for a while, and that is the letter.

I split the file into seven, wired the old name as a shim that imports all seven, and everything built. Then I ran the law inventory, which walks the source and tabulates every theorem with the grade properties its proof consumes. It reported two hundred and fifty-five theorems before the split. After: one hundred and ninety-four.

Sixty-one theorems gone, and the report ended with "0 flagged".

The script globbed one directory. Not the tree, the directory. The new files were one level down, so they were not there to be tabulated, and a tool whose entire job is to notice things did not notice that a third of its subject had moved. It did not fail. It succeeded, on a smaller world, and told me so in the same words it uses when everything is fine.

There was a diff, and a reader comparing the generated table against the committed one would have seen sixty-one rows disappear. But nothing **failed**, and I have been treating green as evidence all through this project.

The fix is one word in two scripts. The thing worth keeping is the shape of the failure: a check that enumerates its own inputs can fail by enumerating fewer of them, and when it does it fails silently and it fails **green**.

I want to put the other half beside it, because the same session produced the opposite. Moving the fold's examples into their own test file took the old test file's only computing check with them. The coverage checker went red inside a second and named the file. That check was written three tranches ago to catch the class of thing I had been failing to catch by review. It works. The difference between the two is that one of them enumerates what it checks and the other is told what to check.


# What changed

Seven modules where there was one, with the old name kept as a shim, so no import anywhere changed and no theorem lost its name. The first module imports the ordinary graded monad and nothing else, so a consumer that wants sequencing gets sequencing.

The boundary is not a claim in a comment. There is a file that imports only that first module and asks for four things it should not be able to see, and it fails to find all four. That is the test.

The fold over a list of grades moved to its own module, and canonicalization imports that instead of the tuple development. It never wanted the tuples.

I also added the one operation that had no caller-chosen-grade version: sequencing a heterogeneous tuple. Its shape is different from the uniform list case in a way I had not expected. Traversing a list has one source grade, so one inclusion proof gets reused at every position. A tuple's slots have **different** grades, so the hypothesis is a whole family of proofs, one per slot. Which means the "it doesn't matter which proof you supply" theorem is stronger here than its siblings: what doesn't matter is an entire family.

It does not have the bridge back to the computed-grade version that every other such operation has, and I left it unproved instead of fudged. The two recursions descend through different grades: the computed one shrinks its grade at every step, the nominated one keeps the caller's throughout, so an induction on one says nothing about the other. It is written down in the file, next to the thing that lacks it.

And the split is free. I measured it, and the sixteen test files the split did not touch cost exactly the same as before. Not approximately. Identically.


# Back in C++

Two things, and the second is the one I would actually tell you.

Splitting a header is the same exercise. The boundary you care about is not what your header says it includes, it is what a consumer transitively gets, and the only way to know is to compile a translation unit that includes the one piece and reaches for something it should not have. If you have not written that translation unit, you do not have the boundary, you have an intention.

But the thing I will remember from this week is about the tooling rather than the code. If you have a script that finds your sources and does something to them, that glob is part of your build's correctness, and it is the part nobody reviews. Reorganize a directory and it can quietly start covering less, keep passing, and keep reporting the number it found as though it were the number that exists. Every generator, every linter-over-a-file-list, every coverage tool that discovers what to measure. Ask what happens to each of them when you add a subdirectory.

&ndash;SMD
