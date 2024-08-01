

There's a lot of things to learn when you want to use Iris. What exactly, depends on your level of prior knowledge and of course on how you want to use it.

# Learning Coq

If you're new to the coq theorem prover, an excellent (personal opinion) source to begin with is the first book of the Software Foundations series. 
The books are digitially available [here](https://softwarefoundations.cis.upenn.edu/).
Volume 1 of the series will teach you all the basics to get started with Coq. In particular the Preface chapter expalins how to setup things. You can read the book in browser, but more importantly you can download it. What you'll get is a working Coq project in which you can and directly do the coding exercises.
Finally if you need more explanation or are more an audio-visual learner, there is a lecture series to the book by Benjamin Pierce (one of the authors), available on [youtube](https://www.youtube.com/watch?v=KKrD4JcfW90&list=PLGCr8P_YncjUT7gXUVJWSoefQ40gTOz89) or directly on the website of the [Summer School on Logic, Languages, Compilation, and Verification](https://www.cs.uoregon.edu/research/summerschool/summer12/curriculum.html). 


# Learing Iris

There is a lot to learn and know about Iris and it's theoretical foundationand there are different ways to approach it, depending on your background and usecase. If you're not familiar with the concept of semantic typing and the general idea bihind Iris, I'd strongly recommend to start with Derek Dreyers Milner Award Lecture [The Type Soundness Theorem That You Really Want to Prove ](https://www.youtube.com/watch?v=8Xyk_dGcAwk).



Sources to order and describe:
2. the video recordings of the [Oregon Programming Languages Summer School 2015](https://www.cs.uoregon.edu/research/summerschool/summer15/curriculum.html),
- lecture series held by different people 
- the lectures from Adam Chlipala at least the first ones align pretty well with the first parts of the semantic course ie. introducing to reasoning about a language in coq, the reflexive transitive closure, etc. 
- the lectures by Amal Ahmed (Co-author of Iris) introduce to the concept of logical relation to reason about program and in later videos compiler correctness, starting from what logical relations are and why they are needed/useful to proof certain properties of languages

3. The semantics course, lecture notes and coding exercises
4. Available Iris tutorials from mostly POPL
5. The BSc Tesis on Iris
    - not sure if it's helpful, it's low level but the tutorials might also cover this and
      there are missing parts, small but compile-blocking errors in the examples
6. my notes and summaries.


### Summer school Notes:
Adams lectures at https://www.youtube.com/playlist?list=PLiHLLF-foEewFOC-gScQF7QxKj07l6xQI

2nd 
- State Machine
- refl.-transitive closure
- defining a 2-threaded program and reason about invariants

3rd. 
- Operational  Semantics 
- substitution
- small-step, big-step and equivalence
- example on how to write a tactic to simplify the small=>big proof
- explains context filling

4th.
- prove Soundness via progress and preservation
- composing contexts

5th/6th
- proves and semantics for programming language features
- for/while loop, pattern matching
- reading/writing states
- loop invariants etc.


