

There's a lot of things to learn when you want to use Iris. What exactly, depends on your level of prior knowledge and of course on how you want to use it.

# Learning Coq

If you're new to the coq theorem prover, an excellent (personal opinion) source to begin with is the first book of the Software Foundations series. 
The books are digitially available [here](https://softwarefoundations.cis.upenn.edu/).
Volume 1 of the series will teach you all the basics to get started with Coq. In particular the Preface chapter expalins how to setup things. You can read the book in browser, but more importantly you can download it. What you'll get is a working Coq project in which you can and directly do the coding exercises.
Finally if you need more explanation or are more an audio-visual learner, there is a lecture series to the book by Benjamin Pierce (one of the authors), available on [youtube](https://www.youtube.com/watch?v=KKrD4JcfW90&list=PLGCr8P_YncjUT7gXUVJWSoefQ40gTOz89) or directly on the website of the [Summer School on Logic, Languages, Compilation, and Verification](https://www.cs.uoregon.edu/research/summerschool/summer12/curriculum.html). 


# Learning Basics of Formal Reasoning about Programms 

Each winter semester we (as in Dr. Sebastian Ertel from BI) teach the course "Foundations of Certified Programming Language and Compiler Design". It's main focus is to introduce formal reasoning and type theory as means of program and compiler verification. In the practical part and the excercises also functional programming basics in haskell and essential tactics in Coq are introduced and applied to the theoretical concepts tought in the course. You can find the material on the [course website](https://www.barkhauseninstitut.org/research/teaching/translate-to-deutsch-foundations-of-certified-programming-language-and-compiler-design). You'll need a login to access slides and exercises. In case you didn't take the course just as Sebastian direktly. 


# Learing Iris

There is a lot to learn and know about Iris and it's theoretical foundationand there are different ways to approach it, depending on your background and usecase. If you're not familiar with the concept of semantic typing and the general idea behind Iris, I'd strongly recommend to start with Derek Dreyers Milner Award Lecture [The Type Soundness Theorem That You Really Want to Prove ](https://www.youtube.com/watch?v=8Xyk_dGcAwk).

The next step depends on your usecase. 

1. If you want to understand how a language is intantiated in Iris, I'd recommend [this short tutorial](https://www.youtube.com/watch?v=HndwyM04KEU) first. It' a very short intro tutorial, but well suited to give a bit of orientation what the "framework"-part of the Iris framework is. The code for this tutorial can be found [in this github repo](https://github.com/tchajed/iris-simp-lang/tree/main) 

2. The next step to understand reasoning in Iris, based on the example language HeapLang is [this tutorial]() from the POPL'21 conference. The exercises and solution can be found [here](https://gitlab.mpi-sws.org/iris/tutorial-popl21) (ToDo: replace with our own version as soon as I finished the exercises, extended the comments and obviously deleted my solutions again)

3. A deep dive on semantic typing and the inner working of Iris is given in the [semantics course exercises and lecture notes](https://plv.mpi-sws.org/semantics-course/). As the name suggest, the lecture notes are written to accompany a lecture, so there might be missing puzzle or shortened puzzle piece in the explanations. A shorter and still more spelled out version of the semantic typing logic can be found in the paper 
[A Logical Approach to Type Soundness](https://iris-project.org/pdfs/2024-jacm-logical-type-soundness.pdf). A [summar of this paper](./Summary_ALogicalApproachToTypeSoundness.md).

If you start with the exercises and are not familiar with reasoning about step relations or wonder why you need the reflexive transitive closure, I'd recommend watching the video recordings of the [Oregon Programming Languages Summer School 2015](https://www.cs.uoregon.edu/research/summerschool/summer15/curriculum.html). The lectures by Adam Chlipala (alo available on [youtube](https://www.youtube.com/playlist?list=PLiHLLF-foEewFOC-gScQF7QxKj07l6xQI)) introduce reasoning about programming languages in Coq. 
In particular the second lecture introduces step relations, their reflexive transitive closure and reasoning about programs, the third and fourth lecture introduces small-step big-step and context semantics and align very well witht the first parts of the semantics course.  



Sources to order and describe:
4. Available Iris tutorials from mostly POPL
5. The BSc Tesis on Iris
    - not sure if it's helpful, it's low level but the tutorials might also cover this and
      there are missing parts, small but compile-blocking errors in the examples
6. my notes and summaries.


