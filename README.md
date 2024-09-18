# Learnings

This is the repository for saving our learning insights from the `BI Coq'ers United` sessions.


## What's this about

In this repo we'll keep insights, examples and ressource for learning Coq.
In particular it contains things we presented during the weekly Coq meeting.
To make it easier for us to a) build examples for tactics/strategies an problems and b) step through the examples afterwards
we'll have a little library with helper functions, datatype mocks etc. to build examples that make the examples in here standalone as for as possible i.e. please don't add (unneccesary) dependencies.


## Schedule

| Date       | Topic               | Presenter                     |
|------------|---------------------|-------------------------------|
| 04.09.2024 | `apply` and `exact` | [Lisza](@lisza.zeidler)       |
| 11.09.2024 | `destruct`          | [Garvit](@garvit.chhabra)     |
| 25.09.2024 | Modules             | [Max](@max.kurze)             |
| 02.10.2024 | Proof General       | Hendrik (Kernkonzept)         |


## Open topics

| Topic                                       | Presenter                                             |
|---------------------------------------------|-------------------------------------------------------|
| `reflexivity` tactic                        |                                                       |
| `simpl` tactic                              |                                                       |
| `auto` tactic and hint databases            |                                                       |
| Type Classes                                | [Max](@max.kurze)                                     |
| Monads                                      | [Sebastian](@sebastian.ertel)                         |
| Hoare logic                                 | [Sebastian](@sebastian.ertel)/[Lisza](@lisza.zeidler) |
| Separation logic                            | [Sebastian](@sebastian.ertel)/[Lisza](@lisza.zeidler) |
| Intro into `stdpp`                          |                                                       |
| Equality of `bool` and `Option` (Coercions) |                                                       |
| Extraction to OCaml, Haskell                |                                                       |
| Intro into mathcomp                         |                                                       |
| Equations                                   |                                                       |
| Partial functions                           |                                                       |
| Coq CI @ Kernkonzept                        |                                                       |
| Nix-based Coq CI                            |                                                       |

## Presented topics

| Topic                             | Presenter                     | Artifacts                             |
|-----------------------------------|-------------------------------|---------------------------------------|
| Induction                         | [Sebastian](@sebastian.ertel) | issue #2+                             |
| "Coq Ops" (nix/dune/opam)         | [Michael](@michael.raitza)    | issue #8+                             |
| Vernacular Commands for Searching | [Lisza](@lisza.zeidler)       | [code](./code/demos/searching_info.v) |
| Intro-patterns                    | [Lisza](@lisza.zeidler)       | [code](./code/demos/intro_patterns.v) |
| SSReflect Basics                  | [Sebastian](@sebastian.ertel) | [code](./code/emos/ssreflect_tour.v)  |

## Contributing

Code demos go to the `code/` folder. Make a new file for your demo in `code/demos` and if needed add
examples to the `helperLib` folder as a new file or directly to `basics.v`. If you add new files, you also have to add them to the `_CoqProject` file, so they will be build by either the nix build or the usual `> make` call.

If you present theoretical background and have slides or markdown or other artifacts, just create a new folder (like IrisRessources) and put it there.

