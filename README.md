# Learnings

This is the repository for saving our learning insights from the `BI Coq'ers United` sessions.


## What's this about

In this repo we'll keep insights, examples and ressource for learning Coq. 
In particular it contains things we presented during the weekly Coq meeting. 
To make it easier for us to a) build examples for tactics/strategies an problems and b) step through the examples afterwards
we'll have a little library with helper functions, datatype mocks etc. to build examples that make the examples in here standalone as for as possible i.e. please don't add (unneccesary) dependencies.

## Open topics

| Topic            | Presenter                                             |
|------------------|-------------------------------------------------------|
| `apply`, `exact` tactic   |                                              |
| `destruct` tactic |                                                      |
| `reflexivity` tactic   |                                                 |
| `simpl` tactic | |
| `auto` tactic and hint databases | |
| Type Classes ||
| Modules          |                          |
| Monads           | [Sebastian](@sebastian.ertel)                         |
| Hoare logic      | [Sebastian](@sebastian.ertel)/[Lisza](@lisza.zeidler) |
| Separation logic | [Sebastian](@sebastian.ertel)/[Lisza](@lisza.zeidler) |
| Intro into `stdpp`| |
| Equality of `bool` and `Option` (Coercions) | |
| Extraction to OCaml, Haskell | |
| Intro into mathcomp | |
| SSReflect | |
| Equations | |

## Presented topics

| Topic            | Presenter                                             | Artifacts |
|------------------|-------------------------------------------------------|-----------|
| Induction        | [Sebastian](@sebastian.ertel)                         | ???       |
| "Coq Ops" (nix/dune/opam) |  [Michael](@michael.raiza)                   | ???       |
| Vernacular Commands for Searching | [Lisza](@lisza.zeidler)                       | [code](./code/demos/searching_info.v) |
| Intro-patterns  | [Lisza](@lisza.zeidler)                       | [code](./code/demos/intro_patterns.v)  


## Contributing 

Code demos go to the `code/` folder. Make a new file for your demo in `code/demos` and if needed add
examples to the `helperLib` folder as a new file or directly to `basics.v`. If you add new files, you also have to add them to the `_CoqProject` file, so they will be build by either the nix build or the usual `> make` call.

If you present theoretical background and have slides or markdown or other artifacts, just create a new folder (like IrisRessources) and put it there. 

