# Style Guide

## Coding style conventions
We are not aware of any official Agda "style guide" or similar; please let us know if you know of one.  Otherwise, please try to be consistent with style used in the repo so far and/or contribute here by helping to establish more detailed guidance.

We will maintain style-related conventions here; please try to adhere to them where possible before creating a pull request.

- *Trailing spaces*: ensure that there are none; [this script](./Scripts/remove-trailing-whitespace.sh) is useful for this purpose.
- *Module structure*: ensure that each module follows this structure and order:
  - Pragmas, if any
  - Copyright notice
  - Imports
     - In general, list all imports in the earliest place possible.  For example, the top of file should include all imports required by the file's modules except those that must be imported within the module due to a dependence on module parameters or a requirement to open public.
     - To the extent possible, group related imports together in order.  List common imports such as `LibraBFT.Prelude`, `LibraBFT.Lemmas` and `LimraBFT.Base.Types` first.
     - When a module must be imported in order to define the module parameters *and* must be imported within the module, if necessary, limit the first import with `using` or using a module qualifier; this helps to avoid conflicts with subset imports within the module.
  - Comment with overview of the module
  - Module definition
- *Syntax conventions*
  -  Example `with` abstraction (note alignment and no space between `...` and `|`)

    ```
      Example : ExampleSignature
      Example x y
         with ExampleValue
      ...| ExampleName = ...
    ```

## Assumptions, warnings and overrides
Ultimately, we aim for a clean proof with all assumptions well justified and minimal warnings and overrides thereof.  While this repo is "work in progress", it is natural that we don't always keep everything perfect in this regard.

However, each of these issues left unresolved is a threat to the validity of the overall proof, so we want to keep technical debt associated with them to a minimum.  Where practical, we will adhere to the following guidelines (and ask contributors to do so as well).

To help keep track of valid assumptions (as opposed to those made temporarily to support progress in other areas), we aim to annotate any outstanding issues to indicate whether they are temporary (and thus a [`TODO-n`](./TODO.md) can be created for addressing them), are considered valid assumptions that need not be proved, or if there is some technical issue preventing us from addressing them.

Here we list some relevant types of issues and discuss how they should be annotated:

 - `postulate`s
	 - For valid assumptions, include comment `valid assumption` on the same line as the `postulate` keyword (enabling easy exclusion from searches for issues that remain to be resolved, as well as easy searching for assumptions on which our proof depends).
	 - For properties that are `postulate`d simply because nobody has proved them yet, include comment `TODO-n: prove` (where `n` is chosen following [these guidelines](./TODO.md)).
	 - For any others, include comment `temporary`, along with an explanation of the reason for the `postulate` and a summary of issues relevant to eliminating it.
 - Pragmas to override warnings/errors should be commented and explained, similar to "other" `postulate`s above.  Examples include:
   - `{-# TERMINATING #-}`
   - `{-# OPTIONS --allow-unsolved-metas #-}`
 - Similarly, warnings (represented by different font faces) should be eliminated where possible, and if any remain, they should be explained and justified.  Examples include:
   - Unsolved metas
   - Catchall clauses
   - Unreachable clauses
