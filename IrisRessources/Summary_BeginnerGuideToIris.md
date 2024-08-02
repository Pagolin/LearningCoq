
# A beginner’s guide to Iris, Coq and separation logic (BSc Thesis)

- based on case studies implementing 
  - a single threaded counter
  - a parallel counter and 
  - a program to transfer money among two banks in HeapLang
  (examples are also explained in Adams [OPLSS lecture](https://www.youtube.com/watch?v=M8pTSQ_Op5M) and [here](https://www.youtube.com/watch?v=59sPvu9RGy8))

- sections 1/2/3 give (a little) background on how to get started with Coq 

### Section 4 - Separation Logic


- Extension of Hoare Logic to reason about programs with mutable state
- HL is extended by 

1. the _separating conjuction_ __P * Q__, allowing to specify properties that hold for disjoint sections of memory e.g. variables mapping into one of the sections only 
2. the _points-to connective_ __x -> y__ that, given as a pre-condition of an expression asserts 
i) that adress x contains value y and 
ii) that the expression has (exclusive) ownership of the ressource i.e. memory location x

3. the _magic wand_ __-*__
   a program state satisfies __P -* Q__ if it can be combined (actually their memory) with any state that fulfils __P__ and the combination will fulfil __Q__ 


- a __formular__ is a logical statement specifying a set of program states a particular state may or may not satisfy (e.g. some location pointing to some particular value)

- Iris is a resource logic, meaning that each proposition in preconditions of an expression entails ownership of the memory locations in the proposition (to allow reasoning about concurrent execution)


### Section 5. - Iris Base Logic

__5.1. Propositions__

- describe ressources owned by program states (threads and subsets of the heap) they hold for
- come with classical logic grammar ($True |\ False |\ \wedge \ ...$) plus 
  1. the separating conjuction, the points-to connective and the magic wand
  2. terms for invariant specification (naming, indexing by thread, ghost state logic)
  3. terms for composing hoare/atomic tripples

__5.2. Ressource Algebra__

- to reason about ressources in Iris you need to define a __Ressource Algebra__ (as HeapLang does for the ressource 'memory on the heap')
- a RA consists of 
    1. a set of ressources $\mathcal{M}$
    2. a (unary?) validity predicate $\mathcal{V()}$ to judge wether a ressource is valid and
    3. an operation to compose ressources that is associative and commutative and has a neutral element that is always valid. also valid compositions must imply valid composed ressources

__5.3. Invariants $\boxed{P}^N$__

- properties _$P$_ 'enclosed' in invariants are used to reason about shared state 
- properties encapsulated in invariants can be shared among threads
- to manipulate properies (e.g. location x pointing to value y) in an invariant a thread must open the invariant for an atomic operation
- the invariant can only be closed again if it is proven after the atomic operation (e.g. _value y has been manipulated but is still greater than 0_ ) 
- invariants are organized in namespaces _$N$_ to ensure consistency among nested invariants (e.g. an invariant on a location being open while the invariant on the heap section containing the location is closed)


__5.4. Modalities__

- modify the conditions under which propositions hold

1. The persistence modality $\Box P$ asserts that $P$ holds without any ownership assumption i.e. it basically turns properties back to pure logic

2. The later modality $\rhd P$ asserts that $P$ holds 'one step later' (Iris is based on step indexing) ... this prevents invariants from being circular i.e. openind them grants ownership one step later and closing them reestablishes them one step later

3. The (basic) update modality $\Rrightarrow P$ asserts some ownership granting properties $P$ after performing an update on exiting ressources. Those updates are guaranteed to be _frame preserving_ i.e. to not interfere with ressources held by other threads and invariants  

__5.5. Ghost State__

- represent ressources that only exist on the logical layer
- they are used to attach them to actual ressources to reason about shared state e.g. a phsical adress pointing to a value cannot be split to reason about multiple threads accessing it potentially mutably. 
But ghost states attached to it can be split into authoritative (actual ownership) and non-authoritative (reference) parts to ensure, that updates to the value can only ybe made if all parts of the ghost state are owned by one thread 

__5.6. Hoare Triples and Atomic Triples__
Hoare Triples: 
$$\{P\}e\{Q\}$$
... if a program state $\sigma$ satisfies $P$ than e will run without erroring and if it terminates the resulting state $\sigma'$ will satisfy $Q$
 - for Iris triples the return value is explicitely included as 
 $$\{P\}e\{v.Q\}$$

 - the principle of _weakest precondition_ means, that we limit $P$ to be minimal logical requirements for e to always produce a state satisfying $Q$. In separation logic this allows for instance to reason only about the currently relevant parts of the memory   

Atomic Triples:
 $$\langle x.P\rangle e \langle v.Q\rangle$$

- regardless if $e$ is atomic or not, it's effect on the shared state _appears_ to be/is logically treated as atomic i.e. $e$ has potentially a lot of steps but only one is updating shared state

__5.7. Proof Rules__

- as the logic is based on Hoare, the basic rules are also derived from hoare logic

![hoare rules from the thesis figure](./hoare_rules.jpg)

- next the thesis explains backward reasoning as construcing a proof tree by "stacking" these logical rules to stepwise go from goal to premises, premises of premises etc. until (hopefully) reaching axioms i.e. rules without premisses


### Section 6. - Iris in Action

__6.1. HeapLang__

- full documentation [here](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md) 
- language definition [here](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/lang.v)
- features:  
  - lambda-calculus based
  - mutable state
  - recursive functions
  - general higher-order references 
  - fork-style concurrency 
- sidenote `#literal` e.g. `#3` lifts coq literals into HeapLang values
- goals are (mostly) of the form 
  $WP e @ E \{\{Q \}\} $
  where WP represents the weakest precondition
- basic tactics revolve around stepping/evaluating the expression in the current goal, thereby transforming the pre- and post-condition
 e.g. 
  - __wp_pure/wp_pures__ -> take one reduction step/as many steps as possible in $e$
  - __wp_load/wp_store/wp_op__ -> reduce specific operations (and conclude the assertions requried for memory handling)

Simple example: 

This defines a program that takes an adress and increases the value at this adress by 2.

![program incresing by two in HeapLang](./heaplang_expr.jpg)

This is the definition of a weakest precondition lemma on the program, stating that for an initially pointed-to value of one, the final value in memory will be three and the expression will return unit. (The `wp #l` is the expression defined above, naming it wp is a bit confusing)

![definition of a lemma about an expression in HeapLang](./wp_tripple.jpg) 



__6.2. Iris Proof Mode__

- embedded DSL in coq
- [code and documentation](https://gitlab.mpi-sws.org/iris/iris)
- specifically the DSL definition of steps, observations, expression etc. is [here](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/program_logic/language.v) 

- proof mode is explained using transitivity based on locations 
  i.e. 
1. a program that takes a location `"x"`, binds a second to the first `let "y" := "x"` and a third to the second `let "z" := "y"` and __???__ (ToDo: What's the semantics of `"x" = "y";;`)

2. a lemma stating transitivity for equality of locations like 
![](./transitivity.jpg)

ToDo: Where does the 'corner'-notation come from? 
- In section 6.2.6. it is explained that $\ulcorner p\urcorner$ mean that $p$ is a pure goal/proposition
-> What does _pure_ mean? It obviously doesn't mean _pure Coq_   

What do the preconditions mean?
- separting conjunction means, that the thread running `trans` has ownership of three disjoint memory regions. One in which x and are the same, one in which y and z are the same and one in which `x = x` 
Question: I see why `trans` would need ownership of the locations i.e. to not interfere with other threads expectations on `y` and `z`. BUT a) it seems y and z are bound in the program, so isn't there a way to have a local namespace? b) why are there any precondtitions on y and z if there adresses are overwritten anyways?

__Basic Terms__

- IPM vertically separates the context into
```
       pure coq/ variables context
     -------------------------------------------
       Intuitionistic separation logic context 
     -------------------------------------------
       Spatial separation logic context
     -------------------------------------------
       (Separation Logic) Goal
```     

__iIntros__
- tactic accepting introduction patterns __ipat__ to _introduce_ 
  hypothesis' into 
  1. the spatial context by default 
  2. the intuitionistic context if it starts with `#`
  3. the normal coq context if it starts with `%`

- __ipat__'s include names, `?` for unnamed and `_` for ignored 
  hypotheses, `[ipat1 ipat2]` introduces a separating conjunction from a normal one iff one of the original hypothesis' is either persistend or ignored 

- `iIntros (coqP1 coqP2 ... ) "irisP1 irisP2 ..."`
   will introduce universal quantifiers `coqP1 ...`into the coq context as the basic `intros` and `"irisP1" ...` into the spatial context

- __iClear__ works with the same syntax
- __iDestruct__ also allows to move parts of spacial hypothesis to coq context as `iDestruct "IrisHyp" as (coqP1 coqP2 ... ) "irisP1 irisP2 ..."`

__iPureIntro__ 
- allows to turn a pure goal $\ulcorner p\urcorner$ into a Coq goal 

 __iDestruct__, __iExact__ and __iApply__ 
 
 - seem to work as their "i-less" counterpart in coq, except that effects can be modified by selection patterns to manipulate in and move between the different contexts.  
 e.g. `iDestruct "IrisHyp" into %PureHype` uses the `%` modifier to move the hypothesis into the pure context

__iLeft/Right/SplitL/SplitR/Exists/ExFalso__
- basically the Iris-context versions of their Coq counterparts


__iFrame__
- separation logic specific tactic 
- ` iFrame (t1...tn) "selpat"` _"cancels Coq terms t1 to tn and Iris hypothesis given by selpat"_
ToDo: This is exactly what the Iris documentation says about this tactic but 
a) What are frames?
   - the resource "embeddings" i.e. ressources in pre and post condition of an expression. framing e.g. means to extend the ressources mentioned in pre- and post-condition of an expression to join proofs of different program fragments/threads  
b) What does canceling mean?
   - In a later part of the skript it seems you have to 'use up' a hypothesis to proof the goal i.e. _cancel_ it 

__iModIntro__
- introduces modalities (later, persitence, update, fancy update ... )
- means if the goal is to show e.g. `|= {someprop} => something`
  there's a later-modality in the goal and __iModIntro__ will (try to) remove it and transform the context accordingly yielding the goal `something`


### Section 7. - Iris Proof Setup

-  I'll test some of the examples [here](../theories/beginners_guide_examples/)
   so if there's notes on things that do/don't work that's where I tried it

- definitions in the library stack requried for Iris overlap and
  override each upon import 

- hence there is a required ordering for imports 
 1. Coq
 2. stdpp
 3. iris.algebra
 4. iris.bi
 5. iris.proofmode
 6. iris.base_logic
 7. iris.program_logic
 8. iris.heap_lang

 - examples start with decarations/shorthands on the context 
   ToDo: What is `Σ`?
 e.g.  `Context ‘{!heapG Σ}.` we assume there's a heap we can manipulate in the proofs 
- ToDo: `heapG` doesn't compile, but `heapGS` does ... Why?

- ToDo: Why do we use values for the definitions? what's the difference to using expressions?

