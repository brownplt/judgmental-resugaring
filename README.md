# SweetT: Resugaring Type Systems

This is the artifact for the paper "Inferring Type Rules for Syntactic
Sugar" by Justin Pombrio and Shriram Krishnamurthi.

------

Type systems and syntactic sugar are both valuable to programmers, but
sometimes at odds. While sugar is a valuable mechanism for
implementing realistic languages, the expansion process obscures
program source structure. As a result, type errors can reference terms
the programmers did not write (and even constructs they do not know),
baffling them. The language developer must also manually construct
type rules for the sugars, to give a typed account of the surface
language. We address these problems by presenting a process for
automatically reconstructing type rules for the surface language using
rules for the core. We have implemented this theory, and show several
interesting case studies.


## Installation Instructions

0. [Download SweetT from here](https://github.com/brownplt/judgmental-resugaring/releases/tag/v1.0).
   (Note to artifact reviewers: if you are reading this, you probably
   already have the zipfile.)
1. Install [DrRacket, version 6.10.1](https://download.racket-lang.org/all-versions.html).
   SweetT should also work fine with later versions of DrRacket. If it
   does not, please open a github issue and I'll see if I can fix it.
   (On Linux, you can either use the download link above and then run
   DrRacket from `/usr/racket/bin/drracket`, or---assuming your package
   manager is apt-get---you can simply run `sudo apt-get install racket`.)
2. Try running the `arith.rkt` test in the `examples` directory by
   opening it in DrRacket (file/open or Ctrl-o) and hitting "Run". You
   should see a popup showing resugared type rules for the sugars
   defined in the file.  You can browse them by clicking "Prev
   Derivation" and "Next Derivation".

## Usage Guide

SweetT takes as input:

1. A grammar for a core language,
2. A set of type rules for that core language, and
3. A set of desugaring rules that target that core language.

And it produces a set of type rules for the sugars.

To see how to use SweetT, let's walk through a small demo (found in
`examples/demo.rkt`):

    #lang racket

    (require redex)
    (require "../sweet-t.rkt")
    
    ;; This is a super-simple resugaring demo to demonstrate the API.
    
    (define-resugarable-language demo
      #:keywords(if true false Bool)
      (e ::= ....
         (if e e e))
      (v ::= ....
         true
         false)
      (t ::= ....
         Bool)
      (s ::= ....
         (not s)))
    
    (define-core-type-system demo
      [(⊢ Γ e_1 t_1)
       (⊢ Γ e_2 t_2)
       (⊢ Γ e_3 t_3)
       (con (t_1 = Bool))
       (con (t_2 = t_3))
       ------ t-if
       (⊢ Γ (if e_1 e_2 e_3) t_3)]
    
      [------ t-true
       (⊢ Γ true Bool)]
    
      [------ t-false
       (⊢ Γ false Bool)])
    
    (define rule_not
      (ds-rule "not" #:capture()
               (not ~a)
               (if ~a false true)))

    (view-sugar-type-rules demo ⊢ (list rule_not))

The first line says that this file is written in the Racket language.
The next two lines say that we're going to use
[redex](https://docs.racket-lang.org/redex/), which SweetT is built
on, and `sweet-t.rkt`, which is SweetT itself.

    #lang racket

    (require redex)
    (require "../sweet-t.rkt")

Next we define the language with `define-resugarable-language`. This
takes a language name (`demo`), a list of keywords (to help SweetT
tell the difference between a keyword and a variable), and a set of
extensions to productions in the language grammar. (The language you
define will build upon a very basic language defined in
`base-lang.rkt`; this base language contains things like the
`calc-type` feature described in the paper.) In this case, we extend
expressions `e` with `if` expressions, values `v` with `true` and
`false`, types `t` with `Bool`, and surface expressions `s` with `(not
s)`, which will be a sugar.

    (define-resugarable-language demo
      #:keywords(if true false Bool)
      (e ::= ....
         (if e e e))
      (v ::= ....
         true
         false)
      (t ::= ....
         Bool)
      (s ::= ....
         (not s)))

Next we define the type system for the `demo` language, using
[Redex's type judgement notation](https://docs.racket-lang.org/redex/redex2015.html#%28part._tue-aft%29).
There is one important restriction, described in the paper: the rules
must be "written using equality constraints: if two premises in a type
rule would traditionally describe equality by repeating a type
variable, SweetT instead requires that the rule be written using two
different type variables, with an equality constraint between them -
thus making the unification explicit." Thus in the `t-if` rule, we
write the equality constraints `(con (t_1 = Bool))` and `(con (t_2 =
t_3))`.

    (define-core-type-system demo
      [(⊢ Γ e_1 t_1)
       (⊢ Γ e_2 t_2)
       (⊢ Γ e_3 t_3)
       (con (t_1 = Bool))
       (con (t_2 = t_3))
       ------ t-if
       (⊢ Γ (if e_1 e_2 e_3) t_3)]
    
      [------ t-true
       (⊢ Γ true Bool)]
    
      [------ t-false
       (⊢ Γ false Bool)])

Now we're ready to write a desugaring rule. This is done with the
`ds-rule` function, which takes a rule name (`not`), a set of
variables to capture (typically the empty set), a left-hand-side `(not
~a)`, and a right-hand-side `(if ~a false true)`. Pattern variables are
written with a tilde, so `~a` is a pattern variable. This rule does
not contain any regular variables, but they would be written without a
tilde. Since `false` and `true` appeared in the keyword list above,
they are interpreted as keywords rather than variables. Finally, rules
can optionally choose to capture variables (i.e., be unhygienic) by
listing them in the `#:capture()` list.

    (define rule_not
      (ds-rule "not" #:capture()
               (not ~a)
               (if ~a false true)))

Finally, we can resugar this rule and view the resulting type rule.
`view-sugar-type-rules` expects a language name (`demo`), a type judgement
relation (which will always be `⊢`), and a list of rewrite rules to
resugar `(list rule_not)`. It then displays the inferred type rule for
`not` in a popup window.

    (view-sugar-type-rules demo ⊢ (list rule_not))

To see the type derivation that led to this type rule, use
`view-sugar-derivations` instead. (Alternatively,
`view-sugar-simplified-derivations` for the simplified derivation,
in which type equalities have been eliminated via unification.)

### How to Read the Type Rules

Here is a basic guide for how to read SweetT's type rules.

__Basics:__

    (⊢ Γ e t)     means  Γ ⊢ e : t
    (bind x t Γ)  means  x:t, Γ
    ~A            means  a pattern variable
    A             means  a variable (or type variable)

__Calctype__ (described in section 4.1):

    (calctype e as t in e2)  means  assert that 'e' has type 't', and evaluate e2

__Sequences__ (described in section 4.5):

    ϵ            means an empty list or empty record
    (cons e e*)  means cons e onto the front of the sequence e*

__Not described in paper:__

    (field x e eRec)          means add the field x:e to record eRec
    (bind* x* t* Γ)           means  x_1:t_1, ..., x_n:t_n, Γ
    (calctype* e* as t* in e) means  (calctype e_1 as t_1 in ... (calctype e_n as t_n in e) ...)

__Type Derivations__

When reading SweetT type derivations, you can ignore "con-" rules that
appear at the top of the derivation. You'll notice that they just
repeat what's below them; they're there for technical reasons.

# Artifact Evaluation Instructions

1. Follow the installation instructions above.
2. Get a sense of what SweetT is for and how it works by reading the
   paper (section 2 in particular should be a good overview), and by
   looking at the "Usage Guide" above.
3. Check that SweetT conforms to the claims of the paper. We walk
   through all of the claims we believe the paper makes next, and
   describe how to verify them.

The zip file you received has the "full" version of the paper, which
includes an appendix that will be useful. It also fixes some mistakes
in the original paper: e.g. the example in section 4.5 was wrong.

## Evaluation: Type Systems (section 6.1 from the paper)

The paper lists a number of type system features that we tested SweetT
against. (TAPL stands for "Types and Programming Languages, by
Benjamin Pierce.)

    booleans    - TAPL pg.93
    numbers     - TAPL pg.93
    stlc        - TAPL pg.103
    unit        - TAPL pg.119
    ascription  - TAPL pg.122
    let         - TAPL pg.124
    pairs       - TAPL pg.126
    tuples      - TAPL pg.128
    records     - TAPL pg.129
    sums        - TAPL pg.132 (uniq typing on pg. 135 irrelevant w/ T.I.)
    variants    - TAPL pg.136
    fixpoint    - TAPL pg.144
    lists       - TAPL pg.147
    exceptions  - TAPL pg.175 (skipping the tiny pre-version)
    alg-subty   - TAPL pg.212
    existential - TAPL pg.366

Instead of having 16 separate type systems each with one feature
(which would be unweildy), we grouped these features into five type
systems:

    examples/arith.rkt:
      booleans, numbers, unit
    examples/lambda.rkt:
      lambda (i.e. stlc), unit, ascription, fixpoint
    examples/data.rkt:
      let, pairs, tuples, records, sums, variants, lists, exceptions
    examples/exists.rkt:
      existentials
    examples/subtype.rkt:
      algorithmic subtyping

We say in the paper: "We tested each type system by picking one or
more sugars that made use of its features, resugaring them to obtain
type rules, and validating the resulting type rules by hand. All of
them resugared successfully. The full version of the paper will
provide an appendix with complete details." You can find the full
paper in the zipfile (paper.pdf).

You can verify that:

1. For each type system feature from TAPL (e.g. booleans), the example
   file that includes that feature has a sugar that uses it
   (e.g. `examples/arith.rkt` is the file that implements booleans,
   and it contains a `not` sugar that uses booleans).
2. Each of the sugars given has the type rule that you would expect it
   to have.



## Case Studies (section 6.2 from the paper)

For each sugar in the case studies, you can verify that:

1. The sugar definition matches what the paper says. (Note that the
   syntax will be superficially different, however. The implementation
   must represent everything as Redex terms which, e.g., require every
   AST node to be wrapped in parentheses. In contrast, the paper uses
   whichever syntax we think is most appropriate, e.g. the syntax used
   in TAPL for the TAPL examples, or Haskell syntax for the Haskell
   examples.)
2. The resugared type rule matches what's shown in the paper.
3. When the paper also shows the full type derivation that led to that
   type rule, the resugared type derivation matches what's shown in the
   paper. To see the resugared type derivation, you can run
   `view-sugar-derivations` instead of `view-sugar-type-rules`.

Note that (quoting the paper): "To make the examples fit we show the
derivations after unification, eliminating equality constraints."


### Foreach

The `foreach` loop can be found as the `rule_foreach` sugar given in
`examples/data.rkt`. The paper presents this sugar in psuedocode that
we believed would be a bit easier to read than the `rule_foreach` code
(which had to be expressed as a Redex term), but the correspondence
should be clear.

### Haskell List Comprehensions

The Haskell List Comprehension sugars can also be found in
`examples/data.rkt`. They are named `rule_hlc-guard`,
`rule_hlc-gen`, and `rule_hlc-let`. The syntax mapping between the
Redex terms (in the implementation) and Haskell (in the paper) is:

    Haskell       Redex
    ~~~~~~~       ~~~~~
    [e | Q]       (hlc e Q)
    b, Q          (hlc/guard b Q)
    p <- l, Q     (hlc/gen p l Q)
    let x = e, Q  (hlc/let x = e in Q)

### Newtype

The newtype sugar is named `rule_newtype` and can be found in
`examples/exists.rkt`. The syntax matches the paper quite closely.

### Figure 6: Letrec, λret, and Upcast

The "upcast" example is named `rule_upcast` in `examples/subtype.rkt`.

The "letrec" example is named `rule_letrec` in `examples/lambda.rkt`.

The "rule\_λret" example is named `rule_λret` in `examples/data.rkt`.

### Examples in the paper

Additionally, there are a few examples of type resugaring described in
prose in the paper:

* `t-and` from section 2 is tested in `examples/arith.rkt`. Note that,
  for expository purposes, the derivation shown in the paper is
  simplified. (You can view this with `view-sugar-simplified-derivations`.)
* `t-or` from section 2 is tested in `examples/data.rkt`.
* `sugar-or-1` and `sugar-or-2` from section 4.5 are tested in
  `examples/multi.rkt`.
