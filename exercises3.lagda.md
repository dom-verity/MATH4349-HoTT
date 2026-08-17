# Preamble

## File options

First we specify the command line options that should be supplied to the Agda compiler / interpreter when this script is processed. These are supplied in a specially formatted comment block.

In the following code we've set the following options:
* `--without-K` disables Streicher’s K axiom, which we don’t want for univalent mathematics. We'll explain why later.
* `--exact-split` makes Agda to only accept definitions with the equality sign “=” that behave like so-called judgemental or definitional equalities.
* `--safe` disables features that may make Agda inconsistent, such as `--type-in-type`, postulates and more.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}
```

## Module declaration and imports

Every module file must start with a `module` stanza.

```agda
module exercises3 where
```

**Note:** the `module-name` must match the base of the file name `module-name.lagda.md`. The extension `.lagda.md` tells Agda that this is a **literate file** written in the markup language [Markdown](https://markdown.org). The contents of the file itself is intended to be a human readable document, with Agda code interspersed throughout and enclosed **fenced code blocks**. These start with \`\`\` or \`\`\`agda on its own line, and end with \`\`\`, also on its own line

Next we import any modules that contain Agda code that this module depends upon.

```agda
open import Agda.Primitive public
open import Function.Base public
```
Here the:

* `open` directive tells Agda that we want to refer to the definitions exported by the imported module using their simple declared names, rather than prefix them with the path `Agda.Primitive.`.
* `public` modifier specifies that the definitions imported by this stanza should be re-exported to any modules that import this one.

# Code

## Standard definitions

This following code sets up the notation for the **universes** `UU i` which are _types of types_ Formally, `UU` is a function which takes as input a **level** `i : Level` and produces `UU i`, the type of types of level at most i. 

To avoid Russell's paradox, the type `UU i` is a type of the next universe level `UU (lsuc i).

**The takeaway:** to declare that "`A` is a type of arbitrary universe level" write `A : UU i` in a context where `i : Level`.

```agda 
UU : (i : Level) → Set (lsuc i)
UU i = Set i
```

We now introduce the data types referenced in chapters 3 and 4 of [Rijke](https://arxiv.org/abs/2212.11082).

## Natural numbers ([Rijke](https://arxiv.org/abs/2212.11082) section 3.1)

We define the natural numbers to be an **inductive type** at level `lzero`, the lowest universe level.

```agda 
data ℕ : UU lzero where
    zero-ℕ : ℕ
    succ-ℕ : ℕ → ℕ
```     

In essence, this declaration:

* declares a new type `ℕ` in universe `UU lzero` in in its first line,
* which has a **zero** element `zero-ℕ` specified, given in its second line, and
* specifies that every element `n : ℕ` should have a **successor** `succ-ℕ n : ℕ` in its third line.

Section 4.1 of [Rijke](https://arxiv.org/abs/2212.11082) tells us that the induction principle for the natural numbers should take a type family `A : ℕ → UU i` and construct a dependent function of type `(n : ℕ) → A n` by specifying what it does on the constructors `zero-ℕ` and `succ-ℕ`. This formulation is expressed in the type signature of the following induction function (eliminator).

```agda
ind-ℕ : {i : Level}{A : ℕ → UU i} → A zero-ℕ → ((n : ℕ) → A n → A (succ-ℕ n)) → (n : ℕ) → A n
ind-ℕ z s zero-ℕ = z
ind-ℕ z s (succ-ℕ n) = s n (ind-ℕ z s n)
```

**Note:** Rijke also discusses the computation rules associated with this data type. These are also constructed by Agda from the data type declaration above, and they become part of the way that it executes programs. We haven't discussed those here because, as yet, we have no good way to express those equalities in our code. We will, however, return to this question when we learn about the _identity type_ in week 4.

## Unit type

The unit type has a single constructor which takes no parameters, and it lives in the lowest universe level.

```agda
data 𝟙 : UU lzero where
    ∗ : 𝟙
```

Here the blackboard bold character `𝟙` can be entered by typing "\\b1" and the name `∗` of its constructor is entered by typing "\\ast". 

Following the prescription of section 4.1 of [Rijke](https://arxiv.org/abs/2212.11082) we see that, given a type family `A : (x : 𝟙) → UU i`, the induction rule for `𝟙` constructs a dependent function `(x : 𝟙) → A x` from information that specifies where the constructor `∗ : 𝟙` should be mapped to in `A ∗`.

```agda
ind-𝟙 : {i : Level}{A : 𝟙 → UU i} → A ∗ → (x : 𝟙) → A x
ind-𝟙 a ∗ = a
```

**Note:** Technically speaking it is slightly misleading at this point to say that `𝟙` _only_ contains the element `∗`. The truth, or otherwise, of this statement depends on precisely what we mean by an _element_ of `𝟙` and how we speak about _equality_ of those elements. For the moment, however, we know that we can define maps _out of_ `𝟙` simply by specifying what they must do to the specific element `∗`. Consequently we shall sometimes refer to this as a (the) **generic element** of `𝟙` because somehow, for the purposes of mapping out of `𝟙`, all other elements of `𝟙` are _indistinguishable_ from it. 

We shall have more to say about this once we've introduced the _identity type_, which will allow us to formalise notions that involve equalities between elements of a type.

## Empty type

The empty type inhabits the lowest level universe `UU lzero` has no constructors. 

```agda
data ∅ : UU lzero where
```

Here the empty set symbol `∅` can be typed simply as "\\0". Now our induction rubric tells us that, given a type family `A : ∅ → UU i`, the induction rule for `∅` constructs a dependent function `(x : ∅) → A x` from data which specifies how it acts on constructors; but since there aren't any constructors no such data is required.

```agda
ind-∅ : {i : Level}{A : ∅ → UU i} → (x : ∅) → A x
ind-∅ ()
```

We met the case of this rule in which the type `A` does not depend on `∅` when we were discussing the false proposition `⊥`, hence the following name for it.

```agda
ex-falso : {i : Level}{A : UU i} → ∅ → A 
ex-falso = ind-∅
```

We can also follow the line of reasoning we took when we were discussing propositional logic, by defining negation in terms of `→` (implication) and `∅` (bottom), and then prove the contraposition rule ([Rijke](https://arxiv.org/abs/2212.11082) proposition 4.3.4).

```agda
infix  30 ¬_

¬_ : {i : Level} → UU i → UU i 
¬ A = A → ∅

contrapositive : {i j : Level}{A : UU i}{B : UU j} → (A → B) → (¬ B → ¬ A)
contrapositive p = λ q → λ a → q (p a)
```

As explained in [Rijke](https://arxiv.org/abs/2212.11082) (definition 4.3.2) it is also common to use the name `is-empty` for `neg`, to reflect our intuition that if a type `A` admits a function to the empty type `∅` then it too should be regarded as being empty; hence the following synonym definition.

```agda
is-empty : {i : Level} → UU i → UU i 
is-empty = ¬_
```

## Coproducts

Given a pair of types `A` and `B` their _coproduct_ `A + B` is a type which models _disjoint union_, its generic elements are either of the form `inl a` for `a : A` or of the form `inr b` for `b : B`. We sometimes say that the constructors `inl` and `inr` _tag_ the elements of `A + B` with information which tells us whether they originally came from `A` or from `B`. Here is the corresponding data declaration.

```agda
infixr 10 _+_

data _+_ {i j : Level}(A : UU i)(B : UU j) : UU (i ⊔ j) where
    inl : A → A + B 
    inr : B → A + B 
```

Our growing intuition for induction rules now tells us that, given a family of types `P : A + B → UU k`, the induction rule `ind-+` constructs a dependent function `(x : A + B) → P x` from information which specifies where generic elements of the form `inl a` or `inr b` are mapped. For this it suffices to provide a pair of dependent functions `(a : A) → P (inl a)` and `(b : B) → P (inr b)`, hence the following type signature.

```agda
ind-+ : {i j k : Level}{A : UU i}{B : UU j}{P : A + B → UU k} → 
        ((a : A) → P (inl a)) → ((b : B) → P (inr b)) → (x : A + B) → P x
ind-+ f g (inl a) = f a
ind-+ f g (inr b) = g b 
```

Now we have a couple of functions on sum types that are discussed in [Rijke](https://arxiv.org/abs/2212.11082).

### [Rijke](https://arxiv.org/abs/2212.11082) remark 4.4.2

```agda
func-+ : {i j k l : Level}{A : UU i}{B : UU j}{C : UU k}{D : UU l} → (A → C) → (B → D) → (A + B) → (C + D)
func-+ f g (inl a) = inl (f a)
func-+ f g (inr b) = inr (g b)
```

This function tells us that maps of types give rise to a map between their coproduct. In general, especially in [_category theory_](https://en.wikipedia.org/wiki/Category_theory), this sort of rule is called _functoriality_ hence the name `func=+`.

### [Rijke](https://arxiv.org/abs/2212.11082) proposition 4.4.3

```agda
empty-+-type : {i j : Level}{A : UU i}{B : UU j} → is-empty A → A + B → B
empty-+-type p (inl a) = ex-falso (p a)
empty-+-type p (inr b) = b

type-+-empty : {i j : Level}{A : UU i}{B : UU j} → is-empty B → A + B → A
type-+-empty p (inl a) = a
type-+-empty p (inr b) = ex-falso (p b)
```

In essence, these functions tell is that the empty type is the _unit_ for the sum type. We will make this intuition far more precise when we discuss the topic of _univalence_.

## Integers

In section 4.5 of [Rijke](https://arxiv.org/abs/2212.11082) the integers are defined as a sum type as follows.

```agda
ℤ : UU lzero
ℤ = ℕ + (𝟙 + ℕ)
```

Notice that in this encoding the numbers `0`, `-1` and `1` have the encodings `inr (inl ∗)`, `inl zero-ℕ`, and `inr (inr zero-ℕ)`. I find using these a little confusing so I found it convenient to introduce the following [_Pattern Synonyms_](https://agda.readthedocs.io/en/stable/language/pattern-synonyms.html) for these and for the inclusions of `ℕ` onto the positive and negative integers.

```agda
pattern zero-ℤ = inr (inl ∗)
pattern one-ℤ = inr (inr zero-ℕ)
pattern neg-one-ℤ = inl zero-ℕ
pattern in-pos n = inr (inr n)
pattern in-neg n = inl n 
```

These are, of course, precisely the definitions to be found in definition 5.4.1 of [Rijke](https://arxiv.org/abs/2212.11082). The benefit of using pattern synonyms is for these definitions is that they may now be used both in expressions (on the right hand side of defining equalities in function definitions) and in patterns (on the left hand side of those definitions). My definition of the induction rule for `ℤ` illustrates this point.

Our induction rule mantra for `ℤ` tells us that, given a type family `A : ℤ → UU i`, the induction functional `ind-ℤ` constructs a dependent function `(z : ℤ) → A z` from data in `A` that is mapped to from the generic elements `zero-ℤ`, `one-ℤ` and `neg-one-ℤ` and the successor functions on the positive and negative integers.

```agda
ind-ℤ : {i : Level}{A : ℤ → UU i} → A zero-ℤ → 
        A one-ℤ → ({n : ℕ} → A (in-pos n) → A (in-pos (succ-ℕ n))) → 
        A neg-one-ℤ → ({n : ℕ} → A (in-neg n) → A (in-neg (succ-ℕ n))) → (z : ℤ) → A z
ind-ℤ a a+ f a- g zero-ℤ = a
ind-ℤ a a+ f a- g one-ℤ = a+
ind-ℤ {A = A} a a+ f a- g (in-pos (succ-ℕ n)) = f (ind-ℤ {A = A} a a+ f a- g (in-pos n))
ind-ℤ a a+ f a- g neg-one-ℤ = a-
ind-ℤ {A = A} a a+ f a- g (in-neg (succ-ℕ n)) = g (ind-ℤ {A = A} a a+ f a- g (in-neg n))
```

Persuading Agda to correctly type this definition is slightly delicate. This explains the patterns `{A = A}` on the left and the parameters `{A = A}` on the right. The function `ind-ℤ` is declared to have an implicit type family parameter `A` and it needs to know that when we make a recursive call to `ind-ℤ` we intend that call to be made using that same type parameter. Unfortunately we can't just bind that parameter to a variable on the left and then pass that on to the recursive calls on the right as usual because that parameter in implicit. The way around this is the notation `{A = A}`, on the left that says _bind a variable `A` to the value of the implicit parameter also called `A`_ and on the right it says _pass the type family `A` as the value of the implicit parameter `A`_. You can find out more about how to handle this kind of shenanigans in the [_Implicit Arguments_](https://agda.readthedocs.io/en/stable/language/implicit-arguments.html) of the Agda manual.

Now we can define the _successor_ function for `ℤ` as discussed in definition 4.5.3 of [Rijke](https://arxiv.org/abs/2212.11082). 

```agda
succ-ℤ : ℤ → ℤ
succ-ℤ zero-ℤ = one-ℤ
succ-ℤ (in-pos n) = in-pos (succ-ℕ n)
succ-ℤ neg-one-ℤ = zero-ℤ
succ-ℤ (in-neg (succ-ℕ n)) = in-neg n 
```

**Note** that this function doesn't have a pattern matching clause for the pattern synonym `one-ℤ`. This is the case because, by definition, `one-ℤ` is a synonym for `in-pos zero-ℕ` and that matches the pattern `in-pos n` in the third line of the above definition. Had we also included a clause for the pattern `one-ℤ` then Agda would have made the following (slightly confusing) complaint:

> Exact splitting is enabled, but the following clause could not be
> preserved as definitional equalities in the translation to a case
> tree:
>>  `succ-ℤ (in-pos n) = in-pos (succ-ℕ n)`

In other words, it detected the pattern overlap between `one-ℤ` and `in-pos n` and since we set the `--exact-split` it disallowed it.

If we really wanted to add the clause matching `one-ℤ` then we should modify the pattern `in-pos n` to exclude the case `in-pos zero-ℕ`, which we can do by matching against the pattern `in-pos (succ-ℕ n)`. This then gives the following variant definition, which you should compare to the clauses given in definition 4.5.3 of [Rijke](https://arxiv.org/abs/2212.11082).

```agda
succ-ℤ' : ℤ → ℤ
succ-ℤ' zero-ℤ = one-ℤ
succ-ℤ' one-ℤ = in-pos (succ-ℕ zero-ℕ)
succ-ℤ' (in-pos (succ-ℕ n)) = in-pos (succ-ℕ (succ-ℕ n))
succ-ℤ' neg-one-ℤ = zero-ℤ
succ-ℤ' (in-neg (succ-ℕ n)) = in-neg n 
```

## Dependent sums

The **dependent sum** type, often referred to as the **Σ-type** (pronounced "Sigma type"), of a type family is called the **dependent pair type** in section 4.6 of [Rijke](https://arxiv.org/abs/2212.11082). As that latter name implies, if `A : UU i` is a type and `B : A → UU j` is a type family then the Σ-type of `B` is the type  `dsum A B : UU (i ⊔ j)` whose elements are of the form `pair a b` where `a : A` and `b : B a`. Such things are called _dependent_ pairs because the type of the second component `b` of `pair a b` _depends_ upon the first component `a`. In Agda this idea is implemented in the following `data` type declaration.

```agda
data dsum {i j : Level} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
    pair : (a : A) → B a → dsum A B
```

We can now introduce two pieces of handy notation, first a [_Syntax Declaration_](https://agda.readthedocs.io/en/stable/language/syntax-declarations.html) which allows us to use `Σ` notation for dependent sums in a manner close to the way they are often annotated on paper.

```agda
syntax dsum A (λ x → B) = Σ x ∈ A , B
```

Then notation for the special case where the type `B` does not depend on the type `A`, as in definition 4.6.4 of [Rijke](https://arxiv.org/abs/2212.11082).

```agda
infixr 10 _×_

_×_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
A × B = Σ x ∈ A , B
```

In an ironic quirk of fate, the type `A × B` is usually referred to as the _(Cartesian) product_ of types `A` and `B`. Its elements are pairs `pair a b` of elements `a : A` and `b : B` much as the product of two sets contains elements that are pairs of the elements in each factor.

**Note:** the operator names appearing in these definitions can be typed in Visual Studio Code using the following key sequences:

* The _sum type (Sigma) operator_ `Σ` is entered using the key sequence "\\Sigma",
* The _element of operator_ `∈` is entered using the key sequence "\\in", and
* The _product operator_ `×` is entered using the key sequence "\\times" or "\\x".

Sum types come with _projection_ functions, definition 4.6.2 of [Rijke](https://arxiv.org/abs/2212.11082), which map pairs to their first and second components respectively.

```agda
pr₁ : {i j : Level}{A : UU i}{B : A → UU j} → Σ a ∈ A , B a → A
pr₁ (pair a b) = a

pr₂ : {i j : Level}{A : UU i}{B : A → UU j} → (p : Σ a ∈ A , B a) → B (pr₁ p)
pr₂ (pair a b) = b 
```

**Note** The type of the second projection `pr₂` is a little finicky, because the output type of this function depends on the first component of its input parameter. Consequently, we define the first projection `pr₁` and use it in specifying the output type of the second projection `pr₂`.

As explained in remark 4.6.3 of [Rijke](https://arxiv.org/abs/2212.11082), for each type family `C : Σ x ∈ A , B x → UU k` the induction principle for the Σ-type constructs a dependent function `(p : Σ x ∈ A , B x) → P p` out of a two parameter dependent function `f : (a : A) → (b : P a) → P (pair a b)`, as follows.

```agda
ind-Σ : {i j k : Level}{A : UU i}{B : A → UU j}{C : Σ x ∈ A , B x → UU k} → 
        ((a : A) → (b : B a) → C (pair a b)) → (p : Σ x ∈ A , B x) → C p
ind-Σ f (pair a b) = f a b
```

**Note:** 

## Exercises

The following are largely the exercises from chapter 4 of [Rijke](https://arxiv.org/abs/2212.11082) converted into a form that Agda will understand.

### Exercise 4.1 (a)

Define the predecessor function on `ℤ`.

```agda
pred-ℤ : ℤ → ℤ
pred-ℤ z = {!   !}
```

### Exercise 4.1 (b)

Define the additive group operations on `ℤ`.

```agda
add-ℤ : ℤ → ℤ → ℤ
add-ℤ z = {!   !}

neg-ℤ : ℤ → ℤ
neg-ℤ z = {!   !}
```

### Exercise 4.2

Define the type `bool :: UU lzero` of _booleans_, which contains two generic elements `true :: bool` and `false :: bool`, using a algebraic `data` type declaration in Agda. Now define the following functions

* The **boolean negation** function `¬-bool : bool → bool`,
* The **boolean conjunction** function `_∧_ : bool → bool → bool`, and
* The **boolean disjunction** function `_∨_ : bool → bool → bool`.
* The **boolean implication** function `_⇒_ : bool → bool → bool` (**hint:** this can be defined in terms of the booleans negation and disjunction functions).

### Exercise 4.3

**Note:** These exercises involve (double) negation and so they can be expected to be a little tricky. That said, if you did the double negation exercises in `exercises2.lagda.md` many of these will be familiar.

For types `P` and `Q` we shall write `P ↔ Q` for the **bi-implication** which is defined to be the product type `(P → Q) × (Q → P)`. Note here that the bi-implication operator `↔` can be entered by typing the key sequence `\\lr`.

```agda
infixr 0 _↔_

_↔_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
A ↔ B = (A → B) × (B → A)
```

#### Ex 4.3.1

Show that:
1. `¬ (P × ¬ P)`
2. `¬ (P ↔ ¬ P)`

**Note:** in other words your task is to construct a term that inhabits each of these types.

```agda
non-contradiction : {i : Level}{P : UU i} → ¬ (P × ¬ P)
non-contradiction p = {!   !}

not-P-iff-not-P : {i : Level}{P : UU i} → ¬ (P ↔ ¬ P)
not-P-iff-not-P p = {!   !}
```

**Note:** By definition `¬ (P × ¬ P)` and `¬ (P ↔ ¬ P)` are function types with output type `∅` and input types `P × ¬ P` and `P ↔ ¬ P` respectively. Consequently, the type of the parameter `p` I've given in these definitions is `P × ¬ P` in the first and `P ↔ ¬ P` in the second. You can see this for yourself by loading this file into Agda in Visual Studio Code, moving to each hole on the right hand side above in turn, and typing "ctrl-X ctrl-E" to show the _environment_ of variables that are in scope in that hole.

**Hint:** In 2. case split on the parameter `p` which unfolds it into two functions `f : P → ¬ P` and `g : ¬ P → P`, but by definition `¬ P = P → ∅` so the type of `f` expands to `f : P → P → ∅`. So use `f` to construct a term of type `¬ P` and then use that and `g` to also construct a term of type `P`. From here its a downhill run.

#### Ex 4.3.2

Construct maps of the following types, which are all part of a thing called the **double negation monad**.

1. `P → ¬ ¬ P` double negation introduction.
2. `(P → Q) ­→ (¬ ¬ P → ¬ ¬ Q)` the functoriality of double negation.
3. `(P → ¬ ¬ Q) → (¬ ¬ P → ¬ ¬ Q)` Kleisli extension.

```agda
¬¬-intro : {i : Level}{P : UU i} → P → ¬ ¬ P 
¬¬-intro = {!   !}

¬¬-func : {i j : Level}{P : UU i}{Q : UU j} → (P → Q) → (¬ ¬ P → ¬ ¬ Q)
¬¬-func = {!   !}

¬¬-kleisli : {i j : Level}{P : UU i}{Q : UU j} → (P → ¬ ¬ Q) → (¬ ¬ P → ¬ ¬ Q)
¬¬-kleisli = {!   !}
```

**Hint:** These types are nested function types so start by introducing enough parameters on the left to reduce the type of the output type to `∅`, now combine the parameters to form a term of that type. Again to see what variables are available in the environment of each hole move to that hole and type "ctrl-X ctrl-E".   
