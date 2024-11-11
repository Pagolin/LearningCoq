# Learnings

This is the repository for saving our learning insights from the `BI Coq'ers United` sessions.


## What's this about

In this repo we'll keep insights, examples and ressource for learning Coq.
In particular it contains things we presented during the weekly Coq meeting.
To make it easier for us to a) build examples for tactics/strategies an problems and b) step through the examples afterwards
we'll have a little library with helper functions, datatype mocks etc. to build examples that make the examples in here standalone as for as possible i.e. please don't add (unneccesary) dependencies.

## Flake Templates

This repository also hosts flake templates to get your Coq project quickly up and running.
To apply a template to your project, call `nix flake init --template <learning>#<template>`, where `<learning>` can be a URL to this repository and `<template>` is the name of the templates.
For example, to list all available templates and apply one to your project, you can do the following:

```
nix flake show git+ssh://git@gitlab.barkhauseninstitut.org/versa/learning.git
...
└───templates
    ├───coq: template: Coq development environment and package framework
    └───default: template: Coq development environment and package framework

nix flake init --template git+ssh://git@gitlab.barkhauseninstitut.org/versa/learning.git#coq
```

To use the default template, you can leave out `#<template>` all together.

## Schedule

| Date       | Topic                   | Presenter                                      |
|------------|-------------------------|------------------------------------------------|
| 30.10.2024 | Proof General (part 2)  | [Hendrik](@hendriktews) (Kernkonzept)          |
| 13.11.2024 | Intro to Koika (part 2) | [Max](@max.kurze) (BI)                         |
| 11.12.2024 | Co-induction            | [Andreas](@aotto) (Kernkonzept)                |
| ???        | Notations               | [Max](@max.kurze)                              |
| ???        | Inversion               | [Lisza](@lisza.zeidler )                       |


## Open topics

| Topic                                       | Presenter                                             |
|---------------------------------------------|-------------------------------------------------------|
| `apply` and `exact`                         | [Lisza](@lisza.zeidler)                               |
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
| "Coq Ops" (nix/dune/opam)         | [Michael](@michael.raitza)    | [tutorial](./tutorials/Nix.md)        |
| Vernacular Commands for Searching | [Lisza](@lisza.zeidler)       | [code](./code/demos/searching_info.v) |
| Intro-patterns                    | [Lisza](@lisza.zeidler)       | [code](./code/demos/intro_patterns.v) |
| `destruct`                        | [Garvit](@garvit.chhabra)     | issue #3+                             |
| SSReflect Basics                  | [Sebastian](@sebastian.ertel) | [code](./code/demos/ssreflect_tour.v) |
| Modules                           | [Max](@max.kurze)             | [code](./code/demos/modules.v).       |
| Proof General intro               | [Hendrik](@hendriktews)       | [code](./code/demos/PG-intro)         |
| Intro to Koika (part 1)           | [Max](@max.kurze) (BI)        |   ???                                 |
| Induction                         | [Lisza](@lisza.zeidler)       | [code](./code/demos/induction.v)      |

## Contributing

Code demos go to the `code/` folder. Make a new file for your demo in `code/demos` and if needed add
examples to the `helperLib` folder as a new file or directly to `basics.v`. If you add new files, you also have to add them to the `_CoqProject` file, so they will be build by either the nix build or the usual `> make` call.

If you present theoretical background and have slides or markdown or other artifacts, just create a new folder (like IrisRessources) and put it there.

