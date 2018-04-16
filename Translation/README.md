# Translation from ETT to ITT and then to TemplateCoq (and thus Coq)

### Prerequisites

**TemplateCoq**
In order to build this project you need to build TemplateCoq. In order to do so, just `make` in the parent repository.

**Equations**
You also need the Equations plugin to build it. See [here](http://mattam82.github.io/Coq-Equations/) for how to install it.


To build the project, you only need to `make`.


### Structure of the project

*The file [util.v](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/util.v)
provides useful lemmata that aren't specific to the formalisation.*

#### Syntax

In [SAst](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/SAst.v)
we define the common syntax to both ETT (Extensional type theory) and ITT (our own version of Itensional
type theory with some sugar) in the form of a simple inductive type `sterm`.
The module [SInduction](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/SInduction.v)
provides useful induction principles on this type. Since terms (`sterm`) are annotated with names—for
printing—which are irrelevant for computation and typing, we define an erasure map `nl : sterm -> nlterm`
in [Equality](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/Equality.v)
from which we derive a decidable equality on `sterm`.
We then define lifting operations, substitution and closedness in 
[SLiftSubst](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/SLiftSubst.v).

#### Typing

First, in [SCommon](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/SCommon.v)
we define common utility to both ETT and ITT, namely with the definition of contexts (`scontext`) and global
contexts (`sglobal_context`), the latter containing the declarations of inductive types.
[Conversion](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/Conversion.v)
is about the untyped conversion used in ITT (conversion `Σ |-i t = u` is derived from one-step reduction
`Σ |-i t ▷ u`) and contains the only axiom of the whole formalisation.
[XTyping](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/XTyping.v)
contains the definition of typing rule of ETT (`Σ ;;; Γ |-x t : A`), mutually defined with a typed
conversion (`Σ ;;; Γ |-x t = u : A`) and the well-formedness of contexts (`wf Σ Γ`).
[ITyping](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/ITyping.v)
is the same for ITT (with the difference that the conversion isn't mutually defined but instead the
one defined in [Conversion](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/Conversion.v))
except that it also defines a notion of well-formedness of global declarations (`type_glob Σ`).

#### Lemmata regarding ITT

In [ITypingInversions](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/ITypingInversions.v)
one can find an inversion lemma for each constructor of the syntax, together with the tactic `ttinv`
to apply the right one.
In [ITypingLemmata](https://github.com/TheoWinterhalter/template-coq/blob/reflection/Translation/ITypingLemmata.v)
are proven a list of different lemmata regarding ITT, including the fact that whenever we have
`Σ ;;; Γ |-i t : A` then `A` is well sorted and that lifting and substitution preserve typing.

#### TODO

### Description of the files (**OLD**)

- `SAst.v` describes common syntax (in a similar fashion to `Ast.v` of
   `theories`) to both ETT and ITT.
- `SInduction.v` is about an induction principle on the AST that gives
  properties to the lists of terms.
- `SLiftSubst.v` describes meta-operations on the syntax (namely lifting and substitution).
- `SCommon.v` states common definitions like context.

- `ITyping.v` contains the typing rules of ITT.
- `XTyping.v` contains the typing rules of ETT.

- `ITypingLemmata.v` contains lemmata regarding typing in ITT.
- `ITypingLemmata.v` contains inversion and admissibility lemmata in ITT.
- `PackLifts.v` contains the necessary lifts to deal with packing.

- `Translation.v` contains the translation itself and the necessary
  lemmata.
- `Reduction.v` is about a notion of reduction to simplify the output
  of the translation (thus reducing the use of axioms when they aren't
  needed).
- `Quotes.v` contains quotations of terms for the final translation.
- `FinalTranslation.v` containes the transaltion from ITT to
  TemplateCoq (meaning we can reify terms of ITT).
- `ExamplesUtil.v` contains utils for the examples.
- `Example.v` contains an example of the two translations chained to
  build a Coq term from an ETT derivation.
