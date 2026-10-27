# Preamble

## File options

First we specify the command line options that should be supplied to the Agda compiler / interpreter when this script is processed. These are supplied in a specially formatted comment block.

In the following code we've set the following options:
* `--without-K` disables Streicher’s K axiom, which we don’t want for univalent mathematics. We'll explain why later.
* `--exact-split` makes Agda to only accept definitions with the equality sign “=” that behaves like so-called judgemental or definitional equalities.
* `--safe` disables features that may make Agda inconsistent, such as `--type-in-type`, postulates and more.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}
```

## Module declaration and imports

Every module file must start with a `module` stanza.

```agda
module MiniHoTT where
```

**Note:** the `module-name` must match the base of the file name `module-name.lagda.md`. The extension `.lagda.md` tells Agda that this is a **literate file** written in the markup language [Markdown](https://markdown.org). The contents of the file itself is intended to be a human readable document, with Agda code interspersed throughout and enclosed **fenced code blocks**. These start with \`\`\` or \`\`\`agda on its own line, and end with \`\`\`, also on its own line

Next we import any modules that contain Agda code that this module depends upon.

```agda
open import Agda.Primitive public
open import Agda.Builtin.Equality public
open import Function.Base public
open import Data.Nat.Base hiding (_⊔_) public
```
Here the:

* `open` directive tells Agda that we want to refer to the definitions exported by the imported module using their simple declared names, rather than prefix them with the path `Agda.Primitive.`.
* `public` modifier specifies that the definitions imported by this stanza should be re-exported to any modules that import this one.

We have now standardised on using Agda's builtin identity type, denoted `≡`. We shall also use the definition of the natural numbers from the Agda standard library. This type is still denoted `ℕ` but its constructors are simply called `zero` and `suc`. By using the standard library version of `ℕ` we can now:

* use literal constants like `2`, `13`, `1001` etc. to denote the corresponding expression for that number given in terms of iterated application of `suc` to `zero-ℤ`,
* use infix symbols `+` and `*` for the algebraic operations of addition and multiplication, these are given by the same definitions as before (using induction in the first variable), and
* reuse a whole bunch of useful algebraic laws and identities that have been defined there - by importing `Data.Nat.Properties`.

Later on I'll also use the equational reasoning support provided by the standard library.

```agda
open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties
    using (module ≡-Reasoning)
open ≡-Reasoning
```

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

```code
data ℕ : UU lzero where
    zero : ℕ
    suc : ℕ → ℕ
```

In essence, this declaration:

* declares a new type `ℕ` in universe `UU lzero` in in its first line,
* which has a **zero** element `zero` specified, given in its second line, and
* specifies that every element `n : ℕ` should have a **successor** `suc n : ℕ` in its third line.

Section 4.1 of [Rijke](https://arxiv.org/abs/2212.11082) tells us that the induction principle for the natural numbers should take a type family `A : ℕ → UU i` and construct a dependent function of type `(n : ℕ) → A n` by specifying what it does on the constructors `zero` and `suc`. This formulation is expressed in the type signature of the following induction function (eliminator).

```agda
ind-ℕ : {i : Level}{A : ℕ → UU i} → A zero → ((n : ℕ) → A n → A (suc n)) → (n : ℕ) → A n
ind-ℕ z s zero = z
ind-ℕ z s (suc n) = s n (ind-ℕ z s n)
```

**Note:** Rijke also discusses the computation rules associated with this data type. These are also constructed by Agda from the data type declaration above, and they become part of the way that it executes programs. We haven't discussed those here because, as yet, we have no good way to express those equalities in our code. We will, however, return to this question when we learn about the _identity type_ in week 4.

## Unit type

The unit type has a single constructor which takes no parameters, and it lives in the lowest universe level.

```agda
data 𝟙 : UU lzero where
    ∗ : 𝟙
```

Here the blackboard bold character `𝟙` can be entered by typing "\b1" and the name `∗` of its constructor is entered by typing "\ast".

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

Here the empty set symbol `∅` can be typed simply as "\0". Now our induction rubric tells us that, given a type family `A : ∅ → UU i`, the induction rule for `∅` constructs a dependent function `(x : ∅) → A x` from data which specifies how it acts on constructors; but since there aren't any constructors no such data is required.

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
infixr 30 ¬_

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
infixr 10 _⊎_

data _⊎_ {i j : Level}(A : UU i)(B : UU j) : UU (i ⊔ j) where
    inl : A → A ⊎ B
    inr : B → A ⊎ B
```

You can type the symbol `⊎` in VSCode using the key sequence `\u+` or `\uplus`.

Our growing intuition for induction rules now tells us that, given a family of types `P : A ⊎ B → UU k`, the induction rule `ind-⊎` constructs a dependent function `(x : A ⊎ B) → P x` from information which specifies where generic elements of the form `inl a` or `inr b` are mapped. For this it suffices to provide a pair of dependent functions `(a : A) → P (inl a)` and `(b : B) → P (inr b)`, hence the following type signature.

```agda
ind-⊎ : {i j k : Level}{A : UU i}{B : UU j}{P : A ⊎ B → UU k} →
        ((a : A) → P (inl a)) → ((b : B) → P (inr b)) → (x : A ⊎ B) → P x
ind-⊎ f g (inl a) = f a
ind-⊎ f g (inr b) = g b
```

Now we have a couple of functions on sum types that are discussed in [Rijke](https://arxiv.org/abs/2212.11082).

### [Rijke](https://arxiv.org/abs/2212.11082) remark 4.4.2

```agda
func-⊎ : {i j k l : Level}{A : UU i}{B : UU j}{C : UU k}{D : UU l} → (A → C) → (B → D) → (A ⊎ B) → (C ⊎ D)
func-⊎ f g (inl a) = inl (f a)
func-⊎ f g (inr b) = inr (g b)
```

This function tells us that maps of types give rise to a map between their coproduct. In general, especially in [_category theory_](https://en.wikipedia.org/wiki/Category_theory), this sort of rule is called _functoriality_ hence the name `func=⊎`.

### [Rijke](https://arxiv.org/abs/2212.11082) proposition 4.4.3

```agda
empty-⊎-type : {i j : Level}{A : UU i}{B : UU j} → is-empty A → A ⊎ B → B
empty-⊎-type p (inl a) = ex-falso (p a)
empty-⊎-type p (inr b) = b

type-⊎-empty : {i j : Level}{A : UU i}{B : UU j} → is-empty B → A ⊎ B → A
type-⊎-empty p (inl a) = a
type-⊎-empty p (inr b) = ex-falso (p b)
```

In essence, these functions tell is that the empty type is the _unit_ for the sum type. We will make this intuition far more precise when we discuss the topic of _univalence_.

## Integers

In section 4.5 of [Rijke](https://arxiv.org/abs/2212.11082) the integers are defined as a sum type `ℤ = ℕ ⊎ (𝟙 ⊎ ℕ)`. In Agda it is a little more natural to define this using the equivalent data type definition.

```agda
data ℤ : UU lzero where
    zero-ℤ : ℤ
    in-pos : ℕ → ℤ
    in-neg : ℕ → ℤ

pattern one-ℤ = in-pos zero
pattern neg-one-ℤ = in-neg zero
```

Here we are also using a couple of [_Pattern Synonyms_](https://agda.readthedocs.io/en/stable/language/pattern-synonyms.html) so that we can use the symbols `one-ℤ` and `neg-one-ℤ` to refer to the integers `1` and `-1`. The benefit of using pattern synonyms is for these definitions here is that they may now be used both in expressions (on the right hand side of defining equalities in function definitions) and in patterns (on the left hand side of those definitions). My definition of the induction rule for `ℤ` illustrates this point.

Our induction rule mantra for `ℤ` tells us that, given a type family `A : ℤ → UU i`, the induction functional `ind-ℤ` constructs a dependent function `(z : ℤ) → A z` from data in `A` that is mapped to from the generic elements `zero-ℤ`, `one-ℤ` and `neg-one-ℤ` and the successor functions on the positive and negative integers.

```agda
ind-ℤ : {i : Level}{A : ℤ → UU i} → A zero-ℤ →
        A one-ℤ → ({n : ℕ} → A (in-pos n) → A (in-pos (suc n))) →
        A neg-one-ℤ → ({n : ℕ} → A (in-neg n) → A (in-neg (suc n))) → (z : ℤ) → A z
ind-ℤ a a+ f a- g zero-ℤ = a
ind-ℤ a a+ f a- g one-ℤ = a+
ind-ℤ {A = A} a a+ f a- g (in-pos (suc n)) = f (ind-ℤ {A = A} a a+ f a- g (in-pos n))
ind-ℤ a a+ f a- g neg-one-ℤ = a-
ind-ℤ {A = A} a a+ f a- g (in-neg (suc n)) = g (ind-ℤ {A = A} a a+ f a- g (in-neg n))
```

Persuading Agda to correctly type this definition is slightly delicate. This explains the patterns `{A = A}` on the left and the parameters `{A = A}` on the right. The function `ind-ℤ` is declared to have an implicit type family parameter `A` and it needs to know that when we make a recursive call to `ind-ℤ` we intend that call to be made using that same type parameter. Unfortunately we can't just bind that parameter to a variable on the left and then pass that on to the recursive calls on the right as usual because that parameter in implicit. The way around this is the notation `{A = A}`, on the left that says _bind a variable `A` to the value of the implicit parameter also called `A`_ and on the right it says _pass the type family `A` as the value of the implicit parameter `A`_. You can find out more about how to handle this kind of shenanigans in the [_Implicit Arguments_](https://agda.readthedocs.io/en/stable/language/implicit-arguments.html) of the Agda manual.

Now we can define the _successor_ function for `ℤ` as discussed in definition 4.5.3 of [Rijke](https://arxiv.org/abs/2212.11082).

```agda
succ-ℤ : ℤ → ℤ
succ-ℤ zero-ℤ = one-ℤ
succ-ℤ (in-pos n) = in-pos (suc n)
succ-ℤ neg-one-ℤ = zero-ℤ
succ-ℤ (in-neg (suc n)) = in-neg n
```

**Note** that this function doesn't have a pattern matching clause for the pattern synonym `one-ℤ`. This is the case because, by definition, `one-ℤ` is a synonym for `in-pos zero` and that matches the pattern `in-pos n` in the third line of the above definition. Had we also included a clause for the pattern `one-ℤ` then Agda would have made the following (slightly confusing) complaint:

> Exact splitting is enabled, but the following clause could not be
> preserved as definitional equalities in the translation to a case
> tree:
>>  `succ-ℤ (in-pos n) = in-pos (suc n)`

In other words, it detected the pattern overlap between `one-ℤ` and `in-pos n` and since we set the `--exact-split` it disallowed it.

If we really wanted to add the clause matching `one-ℤ` then we should modify the pattern `in-pos n` to exclude the case `in-pos zero`, which we can do by matching against the pattern `in-pos (suc n)`. This then gives the following variant definition, which you should compare to the clauses given in definition 4.5.3 of [Rijke](https://arxiv.org/abs/2212.11082).

```agda
succ-ℤ' : ℤ → ℤ
succ-ℤ' zero-ℤ = one-ℤ
succ-ℤ' one-ℤ = in-pos (suc zero)
succ-ℤ' (in-pos (suc n)) = in-pos (suc (suc n))
succ-ℤ' neg-one-ℤ = zero-ℤ
succ-ℤ' (in-neg (suc n)) = in-neg n
```

## Dependent sums

The **dependent sum** type, often referred to as the **Σ-type** (pronounced "Sigma type"), of a type family is called the **dependent pair type** in section 4.6 of [Rijke](https://arxiv.org/abs/2212.11082). As that latter name implies, if `A : UU i` is a type and `B : A → UU j` is a type family then the Σ-type of `B` is the type  `dsum A B : UU (i ⊔ j)` whose elements are of the form `pair a b` where `a : A` and `b : B a`. Such things are called _dependent_ pairs because the type of the second component `b` of `pair a b` _depends_ upon the first component `a`. In Agda this idea is implemented in the following `data` type declaration.

```agda
record dsum {i j : Level} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
    constructor pair
    field
        pr₁ : A
        pr₂ : B pr₁

open dsum public 
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

* The _sum type (Sigma) operator_ `Σ` is entered using the key sequence "\Sigma",
* The _element of operator_ `∈` is entered using the key sequence "\in", and
* The _product operator_ `×` is entered using the key sequence "\times" or "\x".

As explained in remark 4.6.3 of [Rijke](https://arxiv.org/abs/2212.11082), for each type family `C : Σ x ∈ A , B x → UU k` the induction principle for the Σ-type constructs a dependent function `(p : Σ x ∈ A , B x) → P p` out of a two parameter dependent function `f : (a : A) → (b : P a) → P (pair a b)`, as follows.

```agda
ind-Σ : {i j k : Level}{A : UU i}{B : A → UU j}{C : Σ x ∈ A , B x → UU k} →
        ((a : A) → (b : B a) → C (pair a b)) → (p : Σ x ∈ A , B x) → C p
ind-Σ f (pair a b) = f a b
```

**Note:** This function is sometimes called **un-currying** in honour of [_Haskell Curry_](https://en.wikipedia.org/wiki/Haskell_Curry), it is inverse to the [_currying_](https://en.wikipedia.org/wiki/Currying) operation. Actually the idea of representing two parameter functions as functions that take a single parameter and return a function with a single parameter is originally due to [_Gottlob Frege_](https://en.wikipedia.org/wiki/Gottlob_Frege) and was developed in its modern form by [_Moses Schönfinkel_](https://en.wikipedia.org/wiki/Moses_Sch%C3%B6nfinkel).

## Identity type ([Rijke](https://arxiv.org/abs/2212.11082) chapter 5)

This is really where things get interesting. If propositions are types then the equality proposition, which we are familiar with from first order logic, must also ben implemented as a type. In Martin-Löf type theory this is called the _identity type_. At this point we might transition to using Agda's builtin identity type. It has the same definition as the type we've been using, but Agda provides a number of convenience features that make it a little easier to use in big proofs.

Agda's identity type is imported in the preamble of this document, and it definition may be found in the [`Agda.Builtin.Equality`](https://agda.readthedocs.io/en/stable/language/built-ins.html#equality) module. We can now use the infix notation `≡` for the identity type, which is typed using the character sequence "\equiv" or "\==", but its constructor is still called `refl`.

**Note:** Rijke uses the term **identifications** for the elements of `a ≡ x`, because they witness the various ways of demonstrating that `a` is identified with `x`. We shall also use the term **path** for these elements, which is common usage in the Homotopy Type Theory literature.

### Path induction

The induction rule for `≡` is often referred to as **path induction** and it takes the following form in Agda.

```agda
ind-≡ : {i j : Level}{A : UU i}{a : A}(B : {x : A} → a ≡ x → UU j) → (b : B refl) →
         {x : A} → (p : a ≡ x) → B p
ind-≡ _ b refl = b
```

As a rule in "pen and paper" type theory this rule is displayed in the equivalent form:

```math
\dfrac{\Gamma\vdash a : A \hspace{2em} \Gamma, x : A, p : Id(a, x) ⊢ B(x, p)\,\text{type} \;\;}{\Gamma\vdash \text{ind-Id}_a : B(a, refl_a) → \Pi_{x : A} \Pi_{p : \text{Id}(a,x)} B(x, p)}
```

### The "[_Groupoid_](https://en.wikipedia.org/wiki/Groupoid)" structure of types ([Rijke](https://arxiv.org/abs/2212.11082) section 5.2)

We tend to think of types `A` as being _spaces_ and of `a ≡ x` as being the space of paths in `A` from the point `a : A` to the point `x : A`.

#### Path concatenation ([Rijke](https://arxiv.org/abs/2212.11082) definition 5.2.1)

We define both the concatenation function and an infix operator synonym `·`, here this _centre dot_ symbol is typed using the key sequence "\cdot".

```agda
concat : {i : Level}{A : UU i}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
concat refl q = q

infixr 20 _·_
_·_ = concat
```

Now we can prove that `refl : a ≡ a` is a unit for this concatenation operation ([Rijke](https://arxiv.org/abs/2212.11082) definition 5.2.4):

```agda
left-unit : {i : Level}{A : UU i}{a b : A}{p : a ≡ b} → (refl · p) ≡ p
left-unit {p = refl} = refl

right-unit : {i : Level}{A : UU i}{a b : A}{p : a ≡ b} → (p · refl) ≡ p
right-unit {p = refl} = refl
```

#### Path inverse or reversal ([Rijke](https://arxiv.org/abs/2212.11082) definition 5.2.2)

```agda
inv : {i : Level}{A : UU i}{a b : A} → a ≡ b → b ≡ a
inv refl = refl
```

The reversed path `inv p` is both left and right inverse to `p` under the concatenation operation ([Rijke](https://arxiv.org/abs/2212.11082) definition 5.2.5).

```agda
left-inv : {i : Level}{A : UU i}{a b : A}{p : a ≡ b} → (inv p · p) ≡ refl
left-inv {p = refl} = refl

right-inv : {i : Level}{A : UU i}{a b : A}{p : a ≡ b} → (p · inv p) ≡ refl
right-inv {p = refl} = refl
```

#### Associativity of path concatenation ([Rijke](https://arxiv.org/abs/2212.11082) section 5.2.3)

```agda
assoc : {i : Level}{A : UU i}{a b c d : A}{p : a ≡ b}{q : b ≡ c}{r : c ≡ d} →
        ((p · q) · r) ≡ (p · (q · r))
assoc {p = refl} = refl
```

#### Functions act on paths ([Rijke](https://arxiv.org/abs/2212.11082) definition 5.3.1)

```agda
ap : {i j : Level}{A : UU i}{B : UU j}(f : A → B){a a' : A} → a ≡ a' → (f a) ≡ (f a')
ap f refl = refl
```

```agda
ap-id : {i : Level}{A : UU i}{a a' : A}{p : a ≡ a'} → (ap id p) ≡ p
ap-id {p = refl} = refl

ap-comp : {i j k : Level}{A : UU i}{B : UU j}{C : UU k}{a a' : A}{f : A → B}{g : B → C}
          {p : a ≡ a'} → (ap (g ∘ f) p) ≡ (ap g (ap f p))
ap-comp {p = refl} = refl
```

#### Relating actions on paths to composition and inverses (([Rijke](https://arxiv.org/abs/2212.11082) definition 5.3.2)

##### Actions on paths preserve `refl`.

```agda
ap-refl : {i j : Level}{A : UU i}{B : UU j}{f : A → B}{a : A} → (ap f {a = a} refl) ≡ refl
ap-refl = refl
```

**Note:** In the definition above we had to help the Agda type checker a little. If we leave out the slightly unexpected implicit parameter binding `{a = a}` on the right we get a peculiar goal `_a_445 : A` showing up in the **All Goals** window, and we see that the use of `ap` in the type signature above is highlighted in yellow. This indicates that when typechecking the `ap` expression the Agda compiler can't work out what value to bind its parameter `a` to. The type checker can infer that the `a` parameters to `ap` and the first `refl` must both be bound to the same element of `_a_445 : A` and that the `a` parameter of the second `refl` must then be bound to `f _a_445 : B`. It can't, however, guess which element of `A` in the current environment to take to be `_a_445`.

Consequently we must supply that information, and in principle we can do that by adding an explicit binding for the parameter `a` to the instance of `ap` or to either of the instances of `refl`. These parameters are, however, implicit so we must do that using the notation {a = a} to bind the implicit parameter `a` of `ap` (on the left of the `=` sign) to the value `a` in the ambient environment (on its right).

##### Actions on paths preserve path inverses.

```agda
ap-inv : {i j : Level}{A : UU i}{B : UU j}{f : A → B}{a a' : A}{p : a ≡ a'} → (ap f (inv p)) ≡ (inv (ap f p))
ap-inv {p = refl} = refl
```

##### Actions on paths preserve path concatenation.

```agda
ap-concat : {i j : Level}{A : UU i}{B : UU j}{f : A → B}{a a' a'' : A}{p : a ≡ a'}{q : a' ≡ a''} →
            (ap f (p · q)) ≡ ((ap f p) · (ap f q))
ap-concat {p = refl} = refl
```

#### Transport of structure ([Rijke](https://arxiv.org/abs/2212.11082) definition 5.4.1)

As a special case of the `ind-≡` induction rule we have the following **transport** function. Given an element `p : a ≡ b` this transports an element `b : B a` along the path `p` to give an element `tr p b : B a'`.

```agda
tr : {i j : Level}{A : UU i}{B : A → UU j}{a a' : A} → a ≡ a' → B a → B a'
tr {B = B} p b = ind-≡ (λ {x} _ → B x) b p

tr-refl : {i j : Level}{A : UU i}{B : A → UU j}{a : A}{b : B a} → (tr {B = B} refl b ≡ b)
tr-refl = refl
```

We also have an important _naturality law_ for transport relative to a family of functions. This states that transportation and the application of the family of functions _commute_ in a suitable sense.

```agda
tr-naturality : {i j : Level} {A : UU i} {B C : A → UU j} {f : {a : A} → B a → C a}
                {a a' : A} {p : a ≡ a'} {b : B a} → f {a = a'} (tr p b) ≡ tr p (f b)
tr-naturality {f = f} {p = p} {b = b} = ind-≡ (λ {a'} p → f (tr p b) ≡ tr p (f b)) refl p
```

#### The action of dependent functions on paths ([Rijke](https://arxiv.org/abs/2212.11082) definition 5.4.2)

Suppose that `f : (a : A) → B a` is a dependent function, where `B` is a type that depends on the type `A`, then at first blush it doesn't seem to make much sense to apply `f` to a path `p : a ≡ a'`, since `f a` and `f a'` lie in (possibly) distinct types `B a` and `B a'`. We can, however, use the transport function to give some sense to the application of `f` to paths.

```agda
apd : {i j : Level}{A : UU i}{B : A → UU j}(f : (a : A) → B a){a a' : A} →
      (p : a ≡ a') → (tr p (f a)) ≡ (f a')
apd f refl = refl
```

#### The uniqueness of `refl` ([Rijke](https://arxiv.org/abs/2212.11082) section 5.5)

The identity type is a family of inductively defined types, for each term `a : A` the inductive type `a ≡ x` is generated by the constructor `refl {a = a}`. We might therefore expect that, in some sense, `refl {a = a}` is the "unique" element of `a ≡ x`, which leaves the question _what do we mean by "unique"?_ That uniqueness won't be expressed in terms of _definitional equality_, which would force every term of `a ≡ x` to reduce literally to the term `refl`, it will instead be expressed in terms of the identity type on `a ≡ x`.

Here is where a little intuition from homotopy theory comes in handy. We might consider the space `Σ x ∈ A , a ≡ x` of all paths (identifications) in `A` whose starting point is fixed at `a` but whose end point can be **any** point `A`. In homotopy theory such paths can be "shrunk down" along themselves towards their fixed initial point, a process formalised by the observation that **in any space** `A` the space of paths with a fixed initial point `a : A` is _contractible_. We'll talk a little about contractible spaces in class, but suffice it to say that as far as homotopy theory is concerned the terms _contractible_ and _unique_ are synonymous.

Here is how we use this intuition to express the uniqueness of `refl`.

```agda
refl-unique : {i : Level}{A : UU i}{a a' : A} → (p : Σ x ∈ A , (a ≡ x)) → p ≡ (pair a refl)
refl-unique (pair a refl) = refl
```

This function tells us that every point `p` in the space `Σ x ∈ A , (a ≡ x)` of paths whose starting point is `a : A` is equal in that space to the special point `pair a refl` given by the constant path at `a`.

It is important to note that while the space `Σ x ∈ A , a ≡ x` of all paths starting at `a : A` is contractible this is **not** necessarily the case for **any** of its constituent part `a ≡ a'`. In particular, it is generally **not** the case that `refl` is the unique point in the space of loops `a ≡ a` based at `a : A`!

#### Dual path induction and double inversion of paths

Sometimes it is also convenient to use the following variant of the path induction rule in which the endpoints of paths are pinned at their endpoints rather than their start points. Our proof of this makes use of the fact that path inversion is an _involutive_ function.

```agda
inv-involutive : {i : Level} {A : UU i} {x y : A} {p : x ≡ y} → inv (inv p) ≡ p
inv-involutive {p = p} = ind-≡ (λ {y} p → inv (inv p) ≡ p) refl p

ind-≡' : {i j : Level}{A : UU i}{a : A}(B : {x : A} → x ≡ a → UU j) → (b : B refl) →
         {x : A} → (p : x ≡ a) → B p
ind-≡' B b p = tr {B = B} inv-involutive (ind-≡ (B ∘ inv) b (inv p))
```

### Laws of addition on `ℕ`

Here are proofs of the algebraic laws of addition listed at the the top of section 5.6 of [Rijke](https://arxiv.org/abs/2212.11082).

First the definition of addition...

```agda
add-ℕ : ℕ → ℕ → ℕ
add-ℕ zero m = m
add-ℕ (suc n) m = suc (add-ℕ n m)
```

... then some basic laws that tease out how addition interacts with uses of `zero` and `suc`.

```agda
left-unit-law-add-ℕ : {n : ℕ} → (add-ℕ zero n) ≡ n
left-unit-law-add-ℕ = refl

right-unit-law-add-ℕ : {n : ℕ} → (add-ℕ n zero) ≡ n
right-unit-law-add-ℕ {n = zero} = refl
right-unit-law-add-ℕ {n = suc n} = ap suc right-unit-law-add-ℕ

left-successor-law-add-ℕ : {n m : ℕ} → (add-ℕ (suc n) m) ≡ (suc (add-ℕ n m))
left-successor-law-add-ℕ = refl

right-successor-law-add-ℕ : {n m : ℕ} → (add-ℕ n (suc m)) ≡ (suc (add-ℕ n m))
right-successor-law-add-ℕ {n = zero} = refl
right-successor-law-add-ℕ {n = suc n} = ap suc right-successor-law-add-ℕ
```

Notice that the left hand versions of these laws have completely trivial proofs - a simple `refl`. This is because these simply _reify_ the defining computation rules for `add-ℕ`, which are given as the pattern matching clauses in its definition. Their right hand versions, however, require a proof by induction on the variable `n : N` and hence are implemented using pattern matching and a recursive call.

The next law given in Egbert's list is the _associativity of addition_ for natural numbers.

```agda
associative-law-add-ℕ : {n m r : ℕ} → (add-ℕ (add-ℕ n m) r) ≡ (add-ℕ n (add-ℕ m r))
associative-law-add-ℕ {n = zero} = refl
associative-law-add-ℕ {n = suc n} = ap suc (associative-law-add-ℕ {n = n})
```

And finally _commutativity of addition_ for natural numbers.

```agda
commutative-law-add-ℕ : {n m : ℕ} → (add-ℕ n m) ≡ (add-ℕ m n)
commutative-law-add-ℕ {n = zero} = inv right-unit-law-add-ℕ
commutative-law-add-ℕ {n = suc n} =
    (ap suc (commutative-law-add-ℕ {n = n})) · (inv right-successor-law-add-ℕ)
```

## Week 7 - Homotopies

For the moment the type theory rules we've discussed do not give us enough to be able to establish identities between pairs of dependent functions `f , g : (x : A) → B a`. So instead we shall study the properties of **homotopies** between them, that is to say **pointwise** identifications. Here is the relevant definition from [Rijke](https://arxiv.org/abs/2212.11082) Definition 9.1.2:

```agda
infix 1 _∼_

_∼_ : {i j : Level}{A : UU i}{B : A → UU j} (f g : (x : A) → B x) → UU (i ⊔ j)
f ∼ g = (x : _) → (f x) ≡ (g x)
```

In this definition the placeholder `_` in the parameter declaration `(x : _)` invites Agda to infer the type of the variable `x`. It can work out it must be `A` from the declared types of `f` and `g`.

**Note:** in VSCode you can type the homotopy symbol `∼` using the key sequence `\sim` or `\~`. It is important to observe that this is actually a different character to the tilde symbol `~` at the top left of your keyboard.

### Homotopy is an equivalence relation

Definition 9.1.5 of [Rijke](https://arxiv.org/abs/2212.11082) tells us that `∼` is reflexive, symmetric and transitive.

```agda
refl-htpy : {i j : Level}{A : UU i}{B : A → UU j} {f : (x : A) → B x} → f ∼ f
refl-htpy x = refl

inv-htpy : {i j : Level}{A : UU i}{B : A → UU j} {f g : (x : A) → B x} → f ∼ g → g ∼ f
inv-htpy H x = inv (H x)

concat-htpy : {i j : Level}{A : UU i}{B : A → UU j} {f g h : (x : A) → B x} → f ∼ g → g ∼ h → f ∼ h
concat-htpy H K x = concat (H x) (K x)

infixr 20 _∙_
_∙_ = concat-htpy
```

**Note** we are using the _bullet_ symbol `•`, typed `\bullet` or simply `\.`, for concatenation of homotopies. This is not to be confused with the centre dot symbol `·` which we used above as a synonym for concatenation of identifications (paths).

### Groupoid laws for homotopies

Proposition 9.1.6 of [Rijke](https://arxiv.org/abs/2212.11082) proves that `∼` satisfies the groupoid laws:

```agda
assoc-htpy : {i j : Level}{A : UU i}{B : A → UU j} {f g h k : (x : A) → B x}
             {G : f ∼ g}{H : g ∼ h}{K : h ∼ k} → (G ∙ H) ∙ K ∼ G ∙ (H ∙ K)
assoc-htpy {G = G} {H = H} {K = K} x = assoc {p = G x} {q = H x} {r = K x}

left-unit-htpy : {i j : Level}{A : UU i}{B : A → UU j} {f g : (x : A) → B x}{G : f ∼ g} →
                 refl-htpy ∙ G ∼ G
left-unit-htpy x = left-unit

right-unit-htpy : {i j : Level}{A : UU i}{B : A → UU j} {f g : (x : A) → B x}{G : f ∼ g} →
                 G ∙ refl-htpy ∼ G
right-unit-htpy x = right-unit

left-inv-htpy : {i j : Level}{A : UU i}{B : A → UU j} {f g : (x : A) → B x}{G : f ∼ g} →
                 inv-htpy G ∙ G ∼ refl-htpy
left-inv-htpy {G = G} x = left-inv {p = G x}

right-inv-htpy : {i j : Level}{A : UU i}{B : A → UU j} {f g : (x : A) → B x}{G : f ∼ g} →
                 G ∙ inv-htpy G ∼ refl-htpy
right-inv-htpy {G = G} x = right-inv {p = G x}
```

We might observe two things here. These theorems all construct homotopies between homotopies (known as higher homotopies) and their proofs are all simply a matter of applying the corresponding theorem for paths _pointwise_.

### Whiskering operations

The term _"whiskering"_ comes from the field of [_2-category theory_](https://en.wikipedia.org/wiki/2-category) and it was originally coined by my good friend and mentor Ross Street. Why whiskering, I hear you ask? Well the pictures on page 106 of [Rijke](https://arxiv.org/abs/2212.11082) help to explain that, since they look a little like faces with whiskers to the left or right.

Left whiskering post-composes a homotopy, and right whiskering pre-composes it. These are the basic operations from Definition 9.1.7 of [Rijke](https://arxiv.org/abs/2212.11082).

```agda
left-whisker : {i j k : Level}{A : UU i}{B : UU j}{C : UU k}{f g : A → B} →
               (h : B → C) → (f ∼ g) → (h ∘ f ∼ h ∘ g)
left-whisker h H x = ap h (H x)

right-whisker : {i j k : Level}{A : UU i}{B : UU j}{C : UU k}{g h : B → C} →
                (g ∼ h) → (f : A → B) → (g ∘ f ∼ h ∘ f)
right-whisker H f x = H (f x)
```

Whiskering also acts on homotopies between homotopies. Left whiskering maps each path with `ap (ap u)`; right whiskering reindexes the paths along the input function.

```agda
left-whisker-htpy : {i j k : Level}{A : UU i}{B : UU j}{C : UU k}
                    {f g : A → B}{H K : f ∼ g} → H ∼ K → (u : B → C) →
                    left-whisker u H ∼ left-whisker u K
left-whisker-htpy α u x = ap (ap u) (α x)

right-whisker-htpy : {i j k : Level}{A : UU i}{B : UU j}{C : UU k}
                     {f g : B → C}{H K : f ∼ g} → H ∼ K → (u : A → B) →
                     right-whisker H u ∼ right-whisker K u
right-whisker-htpy α u x = α (u x)
```

Successive left whiskering composes functions, and left whiskering preserves homotopy concatenation.

```agda
left-whisker-comp-htpy : {i j k l : Level} {X : UU i} {A : UU j} {B : UU k} {C : UU l}
                         {p q : X → A} (H : p ∼ q) (g : A → B) (f : B → C) →
                         left-whisker f (left-whisker g H) ∼ left-whisker (f ∘ g) H
left-whisker-comp-htpy H g f x = inv ap-comp

left-whisker-concat-htpy : {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
                           {f g h : A → B} (H : f ∼ g) (K : g ∼ h) (u : B → C) →
                           left-whisker u (H ∙ K) ∼ (left-whisker u H ∙ left-whisker u K)
left-whisker-concat-htpy H K u x = ap-concat {f = u} {p = H x} {q = K x}
```

Here the `∘` operation denotes _function composition_ `(g ∘ f) x := g (f x)`, and this symbol is entered using the character sequence `\circ` or simply `\o`.

With a little extra work these can be extended to dependently typed functions, but at this stage that process will introduce complications that we shouldn't worry ourselves with just yet.

The dual right whiskering laws describe successive pre-composition and preservation of homotopy concatenation. The composition law is definitional.

```agda
right-whisker-comp-htpy : {i j k l : Level} {Z : UU i} {A : UU j} {X : UU k} {Y : UU l}
                          {p q : X → Y} (H : p ∼ q) (f : A → X) (g : Z → A) →
                          right-whisker (right-whisker H f) g ∼ right-whisker H (f ∘ g)
right-whisker-comp-htpy H f g = refl-htpy

right-whisker-concat-htpy : {i j k l : Level} {A : UU i} {X : UU j} {Y : UU k}
                            {f g h : X → Y} (H : f ∼ g) (K : g ∼ h) (u : A → X) →
                            right-whisker (H ∙ K) u ∼
                            (right-whisker H u ∙ right-whisker K u)
right-whisker-concat-htpy H K u = refl-htpy
```

Homotopy concatenation is congruent in either argument, so either component of a composite can be varied while the other is fixed.

```agda
left-concat-htpy : {i j : Level} {A : UU i} {B : A → UU j}
                   {f g h : (x : A) → B x} {H H' : f ∼ g} {K : g ∼ h} →
                   H ∼ H' → (H ∙ K) ∼ (H' ∙ K)
left-concat-htpy {K = K} P x = ap (λ p → p · K x) (P x)

right-concat-htpy : {i j : Level} {A : UU i} {B : A → UU j}
                    {f g h : (x : A) → B x} {H : f ∼ g} {K K' : g ∼ h} →
                    K ∼ K' → (H ∙ K) ∼ (H ∙ K')
right-concat-htpy {H = H} P x = ap (λ q → H x · q) (P x)
```

Finally, when `H : f ∼ id`, whiskering its inverse and concatenating with `H` gives a cancellation. These pointwise path lemmas provide the left and right forms.

```agda
left-whisker-inv-cancel-path : {i j : Level} {A : UU i} {B : UU j}
                               (f : A → A) (g : A → B) (H : f ∼ id) (x : A) →
                               ap g (ap f (inv (H x))) · ap (g ∘ f) (H x) ≡ refl
left-whisker-inv-cancel-path f g H x =
    ap (λ p → p · ap (g ∘ f) (H x))
         (inv ap-comp) ·
    inv (ap-concat {f = g ∘ f} {p = inv (H x)} {q = H x}) ·
    ap (ap (g ∘ f)) (left-inv {p = H x})

right-whisker-inv-cancel-path : {i j : Level} {A : UU i} {X : UU j}
                                (f : A → A) (g : X → A) (H : f ∼ id) (x : X) →
                                inv (H (f (g x))) · H (f (g x)) ≡ refl
right-whisker-inv-cancel-path f g H x = left-inv {p = H (f (g x))}
```

The pointwise cancellations lift to homotopies.

```agda
left-whisker-inv-cancel-htpy : {i j : Level} {A : UU i} {B : UU j}
                               (f : A → A) (g : A → B) (H : f ∼ id) →
                               (left-whisker g (left-whisker f (inv-htpy H)) ∙
                                left-whisker (g ∘ f) H) ∼ refl-htpy
left-whisker-inv-cancel-htpy f g H x = left-whisker-inv-cancel-path f g H x

right-whisker-inv-cancel-htpy : {i j : Level} {A : UU i} {X : UU j}
                                (f : A → A) (g : X → A) (H : f ∼ id) →
                                (right-whisker (inv-htpy H) (f ∘ g) ∙
                                 right-whisker H (f ∘ g)) ∼ refl-htpy
right-whisker-inv-cancel-htpy f g H x = right-whisker-inv-cancel-path f g H x
```

### Bi-invertible maps (equivalences).

We use the notion of homotopy to define what it means for a map to have a _section_ (right inverse) or a _retraction_ (left inverse) and then define the notion of **homotopy equivalence** (or just _equivalence_ for short) to be a map which has both a section and a retraction.

```agda
sec : {i j : Level}{A : UU i}{B : UU j}(f : A → B) → UU (i ⊔ j)
sec {A = A} {B = B} f = Σ g ∈ (B → A) , (f ∘ g ∼ id)

retr : {i j : Level}{A : UU i}{B : UU j}(f : A → B) → UU (i ⊔ j)
retr {A = A} {B = B} f = Σ h ∈ (B → A) , (h ∘ f ∼ id)

is-equiv : {i j : Level}{A : UU i}{B : UU j}(f : A → B) → UU (i ⊔ j)
is-equiv f = sec f × retr f
```

**Note** The term `id` denotes the _identity_ map `λ x → x` whose type is `{i : Level}{A : UU i} → A → A`.

The term `sec(f)` denotes the type of all sections of `f`, the term `retr(f)` denotes the type of all retractions of `f` and `is-equiv(f) := sec(f) × retr(f)` is then a type inhabited by pairs comprising a section and a retraction of `f`. We say that such information _witnesses_ that `f` is an equivalence.

For example, the identity map `id : A → A` is an equivalence, since it is both its own section and retraction.

```agda
id-sec : {i : Level}{A : UU i} → sec (id {A = A})
id-sec = pair id (λ x → refl)

id-retr : {i : Level}{A : UU i} → retr (id {A = A})
id-retr = pair id (λ x → refl)

id-equiv : {i : Level}{A : UU i} → is-equiv (id {A = A})
id-equiv = pair id-sec id-retr
```

### Inverses

We might have expected equivalences to be defined as maps `f : A → B` for which there is a map `f⁻¹ : B → A` in the opposite direction which is **both** a section and a retraction.

```agda
has-inverse : {i j : Level}{A : UU i}{B : UU j}(f : A → B) → UU (i ⊔ j)
has-inverse {A = A} {B = B} f = Σ f⁻¹ ∈ (B → A) , ((f ∘ f⁻¹ ∼ id) × (f⁻¹ ∘ f ∼ id))
```

It is then easy to see that `has-inverse f` implies `is-equiv f`.

```agda
has-inverse-to-is-equiv : {i j : Level}{A : UU i}{B : UU j}{f : A → B} → has-inverse f → is-equiv f
has-inverse-to-is-equiv (pair f⁻¹ (pair H K)) = pair (pair f⁻¹ H) (pair f⁻¹ K)
```

Going in the other direction takes a little more work. We do this in two stages:
* Show that if `f` has section `g` and retraction `h` the we have a homotopy `g ∼ h`
* Show that if we have a homotopy `g ∼ h` and `g` is a retraction then `h` is a retraction.
It follows then that `h` is both a section and a retraction of `f` as required.

Both of these proofs uses the whiskering operations, along with homotopy concatenation and inverse.

```agda
equiv-section-retraction-htpy : {i j : Level}{A : UU i}{B : UU j}{f : A → B} →
                                (p : is-equiv f) → (let pair (pair g _) (pair h _) = p in g ∼ h)
equiv-section-retraction-htpy (pair (pair g H) (pair h K)) =
    concat-htpy (inv-htpy (right-whisker K g)) (left-whisker h H)

retraction-htpy-stability : {i j : Level}{A : UU i}{B : UU j}{f : A → B}{h : B → A} →
                            (p : retr f) → (let (pair g _) = p in g ∼ h) → h ∘ f ∼ id
retraction-htpy-stability {f = f} (pair g H) K = concat-htpy (right-whisker (inv-htpy K) f) H
```

Now we can use these results to show that the retraction of a equivalence is also a section, and hence prove:

```agda
is-equiv-to-has-inverse : {i j : Level}{A : UU i}{B : UU j}{f : A → B} → is-equiv f → has-inverse f
is-equiv-to-has-inverse p@(pair (pair g H) q) =
    pair g (pair H (retraction-htpy-stability q (inv-htpy (equiv-section-retraction-htpy p))))
```

**Note** In this argument we need to use the whole parameter `p` on the right-hand side **and** we need to "unpack" it into its components `g`, `H` and `q` to use those as well. To do that we use an `@`-pattern, which is described in the [as-pattern](https://agda.readthedocs.io/en/stable/language/function-definitions.html#as-patterns) section of the Agda manual.

To simplify our notation a little later we introduce a types of all equivalences and isomorphisms between two types:

```agda
infix 1 _≃_

_≃_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
_≃_ A B = Σ f ∈ (A → B) , is-equiv f

infix 1 _≃'_

_≃'_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
_≃'_ A B = Σ f ∈ (A → B) , has-inverse f
```

**Note** You can type the symbol `≃` using the character sequence `\simeq` or, more simply, `\~-`.

### Homotopies are natural (in the categorical sense)

Homotopies `H : f ∼ g` enjoy the following _naturality_ property, which should be familiar to anyone who has been introduced to the basics of category theory.

```agda
htpy-naturality : {i j : Level} {A : UU i} {B : UU j} {f g : A → B} (H : f ∼ g) {x y : A} (p : x ≡ y) →
           ap f p · H y ≡ H x · ap g p
htpy-naturality {f = f} {g = g} H {x = x} = ind-≡ (λ {y} p → ap f p · H y ≡ H x · ap g p) (inv right-unit)

htpy-naturality-htpy : {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
                       {f g : B → C} {u v : A → B} (H : f ∼ g) (P : u ∼ v) →
                       (left-whisker f P ∙ right-whisker H v) ∼
                       (right-whisker H u ∙ left-whisker g P)
htpy-naturality-htpy H P x = htpy-naturality H (P x)
```

#### Example 9.2.9

Here is the proof that cartesian products distribute over sums.

```agda
×-distrib-⊎ : {i j k : Level}{A : UU i}{B : UU j}{C : UU k} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
×-distrib-⊎ (pair a (inl b)) = inl (pair a b)
×-distrib-⊎ (pair a (inr c)) = inr (pair a c)

×-distrib-⊎' : {i j k : Level}{A : UU i}{B : UU j}{C : UU k} → (A × B) ⊎ (A × C) → A × (B ⊎ C)
×-distrib-⊎' (inl (pair a b)) = pair a (inl b)
×-distrib-⊎' (inr (pair a c)) = pair a (inr c)

×-distrib-⊎-left-htpy : {i j k : Level}{A : UU i}{B : UU j}{C : UU k} →
                        ×-distrib-⊎' ∘ ×-distrib-⊎ ∼ id {A = A × (B ⊎ C)}
×-distrib-⊎-left-htpy (pair a (inl b)) = refl
×-distrib-⊎-left-htpy (pair a (inr c)) = refl

×-distrib-⊎-right-htpy : {i j k : Level}{A : UU i}{B : UU j}{C : UU k} →
                         ×-distrib-⊎ ∘ ×-distrib-⊎' ∼ id {A = (A × B) ⊎ (A × C)}
×-distrib-⊎-right-htpy (inl (pair a b)) = refl
×-distrib-⊎-right-htpy (inr (pair a c)) = refl

×-distrib-⊎-has-inverse : {i j k : Level}(A : UU i)(B : UU j)(C : UU k) → has-inverse ×-distrib-⊎
×-distrib-⊎-has-inverse A B C =
    pair (×-distrib-⊎' {A = A} {B = B} {C = C}) (pair ×-distrib-⊎-right-htpy ×-distrib-⊎-left-htpy)
```

### Characterising the identity types of Σ-types

Identity types can be a little _opaque_, their definition in terms of a single constructor `refl` doesn't really provide us with any explicit mechanisms for constructing identifications between elements of the compound data types (Σ, Π, ×, ⊎) we've working with.

The goal in section~9.3 of is to give a more explicit characterisation of identifications between elements in a Σ-type. This is achieved in the following steps:

#### Define a binary relation...

... on the type we are analysing, in this case a Σ-type, which is intended to be _equivalent_ to its identity type.

```agda
infix 1 _≅_

_≅_ : {i j : Level}{A : UU i}{B : A → UU j} → (Σ x ∈ A , B x) → (Σ x ∈ A , B x) → UU (i ⊔ j)
_≅_ (pair a b) (pair a' b') = Σ p ∈ (a ≡ a') , (tr p b ≡ b')
```

**Note:** the symbol `≅` can be typed using the character sequence `\cong` or more simply `\~=`.

We have seen this relation before, in class I called it the "John Major equality".

#### Show that `≅` is reflexive...

```agda
refl-≅ : {i j : Level}{A : UU i}{B : A → UU j}{s : Σ x ∈ A , B x} → s ≅ s
refl-≅ = pair refl refl
```

#### Use reflexivity of `≅` to define a function from `≡`...

...easy...

```agda
pair-≅ : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} → s ≡ t → s ≅ t
pair-≅ {s = s} = ind-≡ (λ {t} p → s ≅ t) refl-≅
```

#### Show that `pair-≅` is an equivalence....

...by first defining a map in the opposite direction. First recall that in exercise 5.3 we defined a map to lift identifications in `A` to identifications in `Σ x ∈ A , B x`.

```agda
lift : {i j : Level}{A : UU i}{B : A → UU j} (s : Σ x ∈ A , B x) {a : A} (p : pr₁ s ≡ a) →
       s ≡ pair a (tr p (pr₂ s))
lift s p = ind-≡ (λ {x} q → s ≡ pair x (tr q (pr₂ s))) refl p
```

So if `(pair p q)` is an element of `s ≅ t` then its first component has type `p : pr₁ s ≡ pr₁ t` and its second component has type `q : tr p (pr₂ s) ≡ pr₂ t`. So we can lift `p` to an identification `lift s p : s ≡ pair (pr₁ t) (tr p (pr₂ s))` and then compose that with the identification that we get by applying `pair (pr₁ t) : B (pr₁ t) → Σ x ∈ A, B x` to `q`.

```agda
≅-pair : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} → s ≅ t → s ≡ t
≅-pair {s = s} {t = t} = ind-Σ (λ p q → concat (lift s p) (ap (pair (pr₁ t)) q))
```

This was a little harder, but it becomes pretty much trivial if we use pattern matching instead (which is how Egbert explained this proof).

```agda
≅-pair' : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} → s ≅ t → s ≡ t
≅-pair' (pair refl refl) = refl
```

Now we finish up by showing that `pair-≅` is both a section and a retraction of `≅-pair`:

```agda
pair-≅-retraction : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} →
                     (≅-pair ∘ pair-≅ ∼ id {A = s ≡ t})
pair-≅-retraction = ind-≡ (λ p → (≅-pair ∘ pair-≅) p ≡ p) refl

pair-≅-section : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} →
                  (pair-≅ ∘ ≅-pair ∼ id {A = s ≅ t})
pair-≅-section {A = A} {B = B} {s = pair a b} {t = pair a' b'} (pair p q) = outer p q
    where
        inner : {b' : B a} (q : tr {A = A} {B = B} refl b ≡ b') →
                ((pair-≅ {s = pair a b}) ∘ ≅-pair) (pair refl q) ≡ pair refl q
        inner = ind-≡ (λ {b'} q → ((pair-≅ {s = pair a b}) ∘ ≅-pair) (pair refl q) ≡ pair refl q) refl

        outer : {a' : A} (p : a ≡ a') {b' : B a'} (q : tr p b ≡ b') →
                (pair-≅ ∘ ≅-pair) (pair p q) ≡ pair p q
        outer =
            ind-≡ (λ {a'} p →
                    {b' : B a'} (q : tr p b ≡ b') → (pair-≅ ∘ ≅-pair) (pair p q) ≡ pair p q) inner

pair-≅-equiv : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} →
                is-equiv (pair-≅ {s = s} {t = t})
pair-≅-equiv = pair (pair ≅-pair pair-≅-section) (pair ≅-pair pair-≅-retraction)
```

Here again, if we allow ourselves the luxury of pattern matching (which is how Rijke implemented the same proofs in the book) things get a little easier:

```agda
pair-≅-retraction' : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} →
                     (≅-pair' ∘ pair-≅ ∼ id {A = s ≡ t})
pair-≅-retraction' refl = refl

pair-≅-section' : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} →
                  (pair-≅ ∘ ≅-pair' ∼ id {A = s ≅ t})
pair-≅-section' (pair refl refl) = refl

pair-≅-equiv' : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} →
                is-equiv (pair-≅ {s = s} {t = t})
pair-≅-equiv' = pair (pair ≅-pair' pair-≅-section') (pair ≅-pair' pair-≅-retraction')
```

### Exercises (Chapter 9 of [Rijke](https://arxiv.org/abs/2212.11082))

### Exercise 9.1

Show that the following functions are equivalences, by exhibiting explicit inverses.

**Note** I've filled in the proofs of these because these results will be of use in chapter 11 below.

```agda
inv-equiv : {i : Level}{A : UU i}{a b : A} → is-equiv (inv {a = a} {b = b})
inv-equiv  = pair (pair inv (λ p → inv-involutive {p = p})) (pair inv (λ p → inv-involutive {p = p}))

left-concat-equiv : {i : Level}{A : UU i}{a b c : A}{p : a ≡ b} → is-equiv (λ (q : b ≡ c) → p · q)
left-concat-equiv {a = a} {b = b} {c = c} {p = p} =
    pair (pair left-concat-inv left-concat-sec-htpy) (pair left-concat-inv left-concat-retr-htpy)
    where
        left-concat : (b ≡ c) → (a ≡ c)
        left-concat q = p · q

        left-concat-inv : (a ≡ c) → (b ≡ c)
        left-concat-inv r = (inv p) · r

        left-concat-sec-htpy : left-concat ∘ left-concat-inv ∼ id
        left-concat-sec-htpy r = (inv (assoc {p = p} {q = inv p})) · (ap (λ s → s · r) (right-inv {p = p}))

        left-concat-retr-htpy : left-concat-inv ∘ left-concat ∼ id
        left-concat-retr-htpy q = (inv (assoc {p = inv p} {q = p})) · (ap (λ s → s · q) (left-inv {p = p}))

right-concat-equiv : {i : Level}{A : UU i}{a b c : A}{q : b ≡ c} → is-equiv (λ (p : a ≡ b) → p · q)
right-concat-equiv {a = a} {b = b} {c = c} {q = q} =
    pair (pair right-concat-inv right-concat-sec-htpy) (pair right-concat-inv right-concat-retr-htpy)
    where
        right-concat : (a ≡ b) → (a ≡ c)
        right-concat p = p · q

        right-concat-inv : (a ≡ c) → (a ≡ b)
        right-concat-inv r = r · (inv q)

        right-concat-sec-htpy : right-concat ∘ right-concat-inv ∼ id
        right-concat-sec-htpy r =
            (assoc {q = inv q} {r = q}) · ap (λ s → r · s) (left-inv {p = q}) · right-unit

        right-concat-retr-htpy : right-concat-inv ∘ right-concat ∼ id
        right-concat-retr-htpy p =
            (assoc {q = q} {r = inv q}) · ap (λ s → p · s) (right-inv {p = q}) · right-unit
```

To prove the last part we start by filling in the functoriality law for transport which we omitted earlier.

```agda
tr-comp : {i j : Level} {A : UU i} {B : A → UU j} {a a' a'' : A} {p : a ≡ a'} {p' : a' ≡ a''} → 
    tr {B = B} (p · p') ∼ (tr p') ∘ (tr p)
tr-comp {a'' = a''} {p = p} {p' = p'} = 
    (ind-≡ (λ {a'} p → ((p' : a' ≡ a'') → (tr (p · p') ∼ (tr p') ∘ (tr p)))) (λ _ _ → refl) p) p'
```

And we have the following function which maps identifications of functions to homotopies

```agda
htpy-eq : {i j : Level} {A : UU i} {B : UU j} {f g : A → B} → (f ≡ g) → (f ∼ g)
htpy-eq {f = f} = ind-≡ (λ {g} _ → f ∼ g) refl-htpy 
```

Using these we get the following proof that transport of structure along and identification is an equivalence.

```agda
tr-equiv : {i j : Level}{A : UU i}{B : A → UU j}{a b : A}{p : a ≡ b} → is-equiv (tr {B = B} p)
tr-equiv {p = p} = 
    pair (pair (tr (inv p)) 
            (inv-htpy (tr-comp {p = inv p}) ∙ htpy-eq (ap tr (left-inv {p = p})))) 
            (pair (tr (inv p)) 
                (inv-htpy (tr-comp {p' = inv p}) ∙ htpy-eq (ap tr (right-inv {p = p}))))
```

### Exercise 9.3

Consider two homotopic functions `f ∼ g`, show that `is-equiv f` if and only if `is-equiv g`.

```agda
equiv-htpy-stability : {i j : Level}{A : UU i}{B : UU j}{f g : A → B} → (f ∼ g) → is-equiv f → is-equiv g
equiv-htpy-stability K (pair (pair h G) (pair k H)) =
    pair (pair h (right-whisker (inv-htpy K) h ∙ G)) (pair k (left-whisker k (inv-htpy K) ∙ H))
```

This gives the "if" direction, explain how we can quickly prove the "only if" direction from it.

```agda
equiv-htpy-stability' : {i j : Level}{A : UU i}{B : UU j}{f g : A → B} → (f ∼ g) → is-equiv g → is-equiv f
equiv-htpy-stability' = equiv-htpy-stability ∘ inv-htpy
```

Show that the inverses of two homotopic equivalences `f ∼ g` are themselves homotopic.

```agda
inverses-homotopic : {i j : Level}{A : UU i}{B : UU j}{f g : A → B} → (f ∼ g) →
                     (s : has-inverse f) → (t :  has-inverse g) → (pr₁ s ∼ pr₁ t)
inverses-homotopic G (pair f' (pair H _)) (pair g' (pair _ K)) = 
    (right-whisker (inv-htpy K) f') ∙ left-whisker g' (right-whisker (inv-htpy G) f') ∙ left-whisker g' H
```

### Exercise 9.4 - the 2-of-3 property for equivalences

We start with a commuting triangle

```agda
module _ {i j k : Level} {A : UU i} {B : UU j} {C : UU k} {f : A → C} {g : B → C} {h : A → B}
         (H : f ∼ g ∘ h) where
```

**Note** here I've used the [anonymous module feature](https://agda.readthedocs.io/en/stable/language/module-system.html#anonymous-modules), introduced by `module _ ... where`, which allows us to collect common parameter declarations together and give them once rather than repeating them in each of the (indented) definitions in the body of that module. In general modules are a way of structuring the way that names are used in an Agda program, they collect together related definitions possessing common parameters and allow us to control how the names of those functions are used in the program beyond the scope of that module. Module systems are a vitally important part of any programming language that targets the development of large and complex programs. You should consult the section of the Agda manual on its [module system](https://agda.readthedocs.io/en/stable/language/module-system.html#module-system) to find out more about its particular variant of this feature.

I should also point out that the contents of a module are determined by indenting them an extra level. So the next few blocks of Agda code are indented to ensure that they are "scoped" by the module declaration above.

In part (a) we prove that if `h` has a section then `f` has a section if and only if `g` has a section.

```agda
    sec-of-h-commutes-with-f-and-g : {s : B → A} → h ∘ s ∼ id → g ∼ f ∘ s
    sec-of-h-commutes-with-f-and-g {s = s} G = inv-htpy (right-whisker H s ∙ left-whisker g G)

    sec-h-and-sec-f-implies-sec-g : sec h → sec f → sec g
    sec-h-and-sec-f-implies-sec-g (pair s G) (pair t L) =
        pair (h ∘ t) (right-whisker (inv-htpy H) t ∙ L)

    sec-h-and-sec-g-implies-sec-f : sec h → sec g → sec f
    sec-h-and-sec-g-implies-sec-f (pair s G) (pair u M) =
        pair (s ∘ u) (inv-htpy (right-whisker (sec-of-h-commutes-with-f-and-g G) u) ∙ M)
```

In part (b) we prove the "dual" result that if `g` has a retraction then `f` has a retraction if and only if `h` has a retraction.

```agda
    retr-of-g-commutes-with-f-and-h : {r : C → B} → r ∘ g ∼ id → h ∼ r ∘ f
    retr-of-g-commutes-with-f-and-h {r = r} K = inv-htpy (left-whisker r H ∙ right-whisker K h)

    retr-g-and-retr-f-implies-retr-h : retr g → retr f → retr h
    retr-g-and-retr-f-implies-retr-h (pair r K) (pair t L) =
        pair (t ∘ g) (left-whisker t (inv-htpy H) ∙ L)

    retr-g-and-retr-h-implies-retr-f : retr g → retr h → retr f
    retr-g-and-retr-h-implies-retr-f (pair r K) (pair s M) =
        pair (s ∘ r) (left-whisker s (inv-htpy (retr-of-g-commutes-with-f-and-h {r = r} K)) ∙ M)
```

Finally in part (c) we prove the 2-of-3 property for equivalences, as three separate lemmas.

```agda
    compose-equiv : is-equiv g → is-equiv h → is-equiv f
    compose-equiv (pair u v) (pair u' v') =
        pair (sec-h-and-sec-g-implies-sec-f u' u) (retr-g-and-retr-h-implies-retr-f v v')

    right-cancel-equiv : is-equiv h → is-equiv f → is-equiv g
    right-cancel-equiv (pair u@(pair s G) _) (pair u' (pair r' K')) =
        pair (sec-h-and-sec-f-implies-sec-g u u') (pair (h ∘ r') L)
        where
            L : h ∘ r' ∘ g ∼ id
            L = left-whisker (h ∘ r') (sec-of-h-commutes-with-f-and-g G) ∙
                left-whisker h (right-whisker K' s) ∙ G

    left-cancel-equiv : is-equiv g → is-equiv f → is-equiv h
    left-cancel-equiv (pair _ v@(pair r K)) (pair (pair s' G') v') =
        pair (pair (s' ∘ g) M) (retr-g-and-retr-f-implies-retr-h v v')
        where
            M : h ∘ s' ∘ g ∼ id
            M = (right-whisker (retr-of-g-commutes-with-f-and-h {r = r} K) (s' ∘ g)) ∙
                left-whisker r (right-whisker G' g) ∙ K
```

**Note** here that in the right cancellation law we actually use the section `s` of the function `h` while proving that if `r'` is a retraction of `f` then `h ∘ r'` is a retraction of `g`. That means that we use an `@`-pattern to unpack `s` and `G` from the proof `u` that `h` has a section while still making `u` available to pass as a parameter to `sec-h-and-sec-f-implies-sec-g`. A dual comment applies to the proof of the left cancellation law.

## Contractible types

A type `A` is _contractible_ if there is some point `a : A` and a family of identifications of `a ≡ x` for all `x : A`.

```agda
is-contr : {i : Level} → UU i → UU i
is-contr A = Σ a ∈ A , ((y : A) → a ≡ y)
```

In this case, the "fixed" point `a` is called a _centre of contraction_.

```agda
-- The centre of a contractible type
centre-of-contr : {i : Level}{A : UU i} → is-contr A → A
centre-of-contr (pair x _) = x
```

If a type `A` is contractible then **all** pairs of its points are identified via a path between them

```agda
all_points_are_centres : {i : Level}{A : UU i} → is-contr A → (u v : A) → u ≡ v
all_points_are_centres (pair a ct) u v = inv (ct u) · (ct v)
```

The identity on a contractible type is homotopic to the constant endomorphism at its centre of contraction.


```agda
-- The constant endomorphism at a point
const-endo : {i : Level}{A : UU i} → A → A → A
const-endo x y = x

contr-has-contr : {i : Level}{A : UU i} → (ct : is-contr A) → id ∼ const-endo (centre-of-contr ct)
contr-has-contr (pair _ p) y = inv (p y)
```

The unit type is contractible.

```agda
unit-is-contr : is-contr 𝟙
unit-is-contr = pair ∗ (ind-𝟙 refl)
```

The space of paths anchored at one end is contractible.

```agda
-- The space of paths anchored at one end at a specified point
path_space : {i : Level}{A : UU i} → (a : A) → UU i
path_space {A = A} a = Σ x ∈ A , (a ≡ x)

-- Path spaces are contractible
path-space-is-contr : {i : Level}{A : UU i} → (a : A) → is-contr (path_space a)
path-space-is-contr {A = A} a = pair (pair a refl) ctr
    where
        ctr : (pt : path_space a) → (pair a refl) ≡ pt
        ctr (pair y refl) = refl
```

For a type `A` and a point `a : A`, singleton induction tells us that we can build maps out of `A` simply by specifying what the do on `a`. This property does **not** hold for all types, indeed it holds for precisely those types that are contractible.

```agda
-- evaluate at a point
ev-pt : {i j : Level}{A : UU i}{B : A → UU j} → (a : A) → ((x : A) → B x) → B a
ev-pt a f = f a

-- Singleton induction
ind-sing-type : {i j : Level}{A : UU i}(B : A → UU j) → A → UU (i ⊔ j)
ind-sing-type {A = A} B a = (B a) → ((x : A) → B x)

has-ind-sing : {i j : Level}(A : UU i) → UU (i ⊔ lsuc j)
has-ind-sing {j = j} A =
    Σ a ∈ A , ((B : A → UU j) → Σ f ∈ ind-sing-type B a , ((ev-pt a) ∘ f ∼ id))

-- Contractible types admit singleton induction
contr-admits-ind-sing : {i j : Level}{A : UU i} → is-contr A → has-ind-sing A
contr-admits-ind-sing {j = j} {A = A} (pair a ct) = pair a ind-sing-prf
    where
        ct' : (x : A) → (a ≡ x)
        ct' x = (inv (ct a)) · (ct x)

        ct'-at-a : ct' a ≡ refl
        ct'-at-a = left-inv {p = (ct a)}

        ind-sing-prf : (B : A → UU j) → Σ f ∈ ind-sing-type B a , ((ev-pt a) ∘ f ∼ id)
        ind-sing-prf B = pair ind-sing comp-sing
            where
                ind-sing : ind-sing-type B a
                ind-sing b x = tr (ct' x) b

                comp-sing : (ev-pt a) ∘ ind-sing ∼ id
                comp-sing x rewrite ct'-at-a = refl

-- Singleton induction implies contractible
ind-sing-implies-contr : {i : Level}{A : UU i} → has-ind-sing A → is-contr A
ind-sing-implies-contr (pair a ind-sing-prf)
    with (ind-sing-prf (λ x → a ≡ x))
... | (pair ind-sing _) = pair a (ind-sing refl)
```

In the last two proofs we've used `rewrite` to rewrite the goal type using a proof of an equality and the `with` abstraction to construct a term and pattern match against it. You can find out more about these agda convenience facilities in the [Agda manual](https://agda.readthedocs.io/en/stable/language/with-abstraction.html).

## Contractible maps

Given a map `f : A → B` and a point `b : B` the _fibre_ of `f` at `b` is defined by

```agda
fib : {i j : Level} {A : UU i} {B : UU j} → (A → B) → B → UU (i ⊔ j)
fib {A = A} f b = Σ a ∈ A , (f a ≡ b)
```

and we say that `f` is **contractible** if all of its fibres are contractible.

```agda
is-contr-map : {i j : Level} {A : UU i} {B : UU j} → (A → B) → UU (i ⊔ j)
is-contr-map {B = B} f = (b : B) → is-contr (fib f b)
```

Proposition 10.3.3 gives an observational variant of the identity type on `fib f b`. Specifically it shows that there is an equivalence between the type of identifications `pair x p ≡ pair x' p'` in `fib f b` and the type of pairs of identifications `α : x ≡ x'` and `β : p ≡ (ap f α) · p'`.

```agda
module _ {i j : Level} {A : UU i} {B : UU j} {f : A → B} {b : B} where

    ≡-fib : fib f b → fib f b → UU (i ⊔ j)
    ≡-fib (pair x p) (pair x' p') = Σ α ∈ x ≡ x' , (p ≡ (ap f α) · p')

    refl-≡-fib : {t : fib f b} → ≡-fib t t
    refl-≡-fib = pair refl refl

    ≡-to-≡-fib : {s t : fib f b} → (s ≡ t) → ≡-fib s t
    ≡-to-≡-fib {s = s} = ind-≡ (λ {t} _ → ≡-fib s t) refl-≡-fib

    ≡-fib-to-≡ : {s t : fib f b} → ≡-fib s t → (s ≡ t)
    ≡-fib-to-≡ {s = s} (pair α β) = outer α β
            where
                inner : {p' : f (pr₁ s) ≡ b} (β : (pr₂ s) ≡ p') → (s ≡ pair (pr₁ s) p')
                inner = ind-≡ (λ {p'} _ → s ≡ pair (pr₁ s) p') refl

                outer : {x' : A} (α : pr₁ s ≡ x') {p' : f x' ≡ b} (β : (pr₂ s) ≡ (ap f α) · p') →
                        (s ≡ pair x' p')
                outer = ind-≡ (λ {x'} α → {p' : f x' ≡ b} (β : pr₂ s ≡ ap f α · p') → s ≡ pair x' p') inner

    ≡-fib-left-inv : {s t : fib f b} → ≡-to-≡-fib ∘ ≡-fib-to-≡ ∼ id {A = ≡-fib s t}
    ≡-fib-left-inv {s = s} (pair α β) = outer α β
        where
            inner : {p' : f (pr₁ s) ≡ b} (β : (pr₂ s) ≡ p') →
                        (≡-to-≡-fib ∘ ≡-fib-to-≡) (pair refl β) ≡ id (pair refl β)
            inner = ind-≡ (λ {p'} β → (≡-to-≡-fib ∘ ≡-fib-to-≡) (pair refl β) ≡ id (pair refl β)) refl

            outer : {x' : A} (α : pr₁ s ≡ x') {p' : f x' ≡ b} (β : (pr₂ s) ≡ (ap f α) · p') →
                        (≡-to-≡-fib ∘ ≡-fib-to-≡) (pair α β) ≡ id (pair α β)
            outer = ind-≡ (λ {x'} α → {p' : f x' ≡ b} (β : (pr₂ s) ≡ (ap f α) · p') →
                                        (≡-to-≡-fib ∘ ≡-fib-to-≡) (pair α β) ≡ id (pair α β)) inner

    ≡-fib-right-inv : {s t : fib f b} →  ≡-fib-to-≡ ∘ ≡-to-≡-fib ∼ id {A = s ≡ t}
    ≡-fib-right-inv {s = s} = ind-≡ (λ p → (≡-fib-to-≡ ∘ ≡-to-≡-fib) p ≡ p) refl
```

Observe that I've implemented the equivalence between `≡-fib` and the identity type on `fib f b` using the raw induction rule `ind-≡` rather than resorting to pattern matching on identifications. At his stage, I don't feel entirely comfortable about relying on pattern matching because we haven't quite manually proved all of the results about `≡` upon which pattern matching itself relies. But once we emerge from chapter 11 we will be able to go to town and rely solely on pattern matching because by then we will have established all of the rules it is built from.

The main utility of pattern matching in these cases is that the Agda pattern matching knows how to construct the _motive_ type parameter of `≡-ind` from data in the context of the patterns being matched. On the other hand, my manual proofs above require us to laboriously give those (sometimes quite complex) type expressions explicitly. As a demonstration of this, here are the same proofs using pattern matching.

```agda
module _ {i j : Level} {A : UU i} {B : UU j} {f : A → B} {b : B} where

    ≡-to-≡-fib' : {s t : fib f b} → (s ≡ t) → ≡-fib s t
    ≡-to-≡-fib' refl = pair refl refl

    ≡-fib-to-≡' : {s t : fib f b} → ≡-fib s t → (s ≡ t)
    ≡-fib-to-≡' (pair refl refl) = refl

    ≡-fib-left-inv' : {s t : fib f b} → ≡-to-≡-fib ∘ ≡-fib-to-≡ ∼ id {A = ≡-fib s t}
    ≡-fib-left-inv' (pair refl refl) = refl

    ≡-fib-right-inv' : {s t : fib f b} →  ≡-fib-to-≡ ∘ ≡-to-≡-fib ∼ id {A = s ≡ t}
    ≡-fib-right-inv' refl = refl
```

### Contractible maps and coherent invertiblity

Our primary interest in contractible maps arises from the crucially important fact that a map is contractible if and only if it is an equivalence. First we introduce a _coherent_ version of invertiblity, which asks for the homotopies witnessing that `f` has an inverse `g` are themselves related by a **higher homotopy**.

```agda
is-coh-invertible : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-coh-invertible {A = A} {B = B} f =
    Σ f⁻¹ ∈ (B → A) ,
        (Σ G ∈ (f ∘ f⁻¹ ∼ id) ,
            Σ H ∈ (f⁻¹ ∘ f ∼ id) , ((right-whisker G f) ∼ (left-whisker f H)))
```

**Note** that for `x : A` we have that `right-whisker G f = G (f x)` and `left-whisker f H = ap f (H x)` so
a homotopy `K` witnessing `(right-whisker G f) ∼ (left-whisker f H)` is a family of identifications `K : (x : A) → G (f x) ≡ ap f (H x)`.

At this point our primary interest in coherent inverses is that a map `f : A → B` has a coherent inverse if and only if it is a contactable map, as demonstrated by the following propositions.

```agda
contr-map-has-coh-inverse : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
                            is-contr-map f → is-coh-invertible f
contr-map-has-coh-inverse {A = A} {B = B} {f = f} p = pair g (pair G (pair H K))
    where
        g : B → A
        g b = pr₁ (pr₁ (p b))

        G : f ∘ g ∼ id
        G b = pr₂ (pr₁ (p b))

        K' : (a : A) → ≡-fib (pr₁ (p (f a))) (pair a refl)
        K' a = ≡-to-≡-fib ((pr₂ (p (f a))) (pair a refl))

        H : g ∘ f ∼ id
        H a = pr₁ (K' a)

        K : (right-whisker G f) ∼ (left-whisker f H)
        K a = (pr₂ (K' a)) · right-unit

coh-inverse-implies-contr-map : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
                                is-coh-invertible f → is-contr-map f
coh-inverse-implies-contr-map {A = A} {B = B} {f = f} (pair g (pair G (pair H K))) b = pair (s b) (L b)
        where
            s : (b : B) → fib f b
            s b = pair (g b) (G b)

            L : (b : B) → (t : fib f b) → (s b) ≡ t
            L b (pair a h) = ≡-fib-to-≡ (
                ind-≡ (λ {b} h → ≡-fib (s b) (pair a h)) (pair (H a) (K a · inv right-unit)) h)
```

Both of these proofs rely upon building elements of the observational equality `≡-fib s t` which we convert to identifications `s ≡ t` using our translation function `≡-fib-to-≡`. The first essentially just unpacks the data encapsulated in a proof of `is-contra-map f` and uses it to populate a proof of `is-coh-invertible f` (possibly after translation by `≡-fib-to-≡`). In the converse direction, we must use path induction to extend the data built into the extra coherence homotopy to give a homotopy that witnesses the contractiblity of the spaces `fib f b`, of which it is the special case at the point `pair a refl : fib f (f a)`.

**Notice** here that when we apply path induction to reduce the second component of an element `(pair a h)` of `fib f b` to `refl` we end up considering elements of the type `fib f (f a)` for some `a : A`. This in turn means that we must _generalise_ the definitions of `s` and `L` in the `where` clause of `coh-inverse-implies-contr-map` by giving them an extra parameter `b : B` to "unpin" that end of our identifications. Had we used pattern matching against the pattern `pair a refl` instead this generalisation step would have been done auto-magically for us my Agda's pattern matching compiler.

### Equivalences are coherently invertible

Of course, we might hope that all maps with plain inverses are contractible, to which end we would like to show that if `f` has an inverse then it has a coherent inverse. Specifically we will show that if `G : f ∘ f⁻¹ ∼ id` and `H : f⁻¹ ∘ f ∼ id` then we can always construct another homotopy `H' : f⁻¹ ∘ f ∼ id` such that `G` and `H'` together satisfy the coherence property `(right-whisker G f) ∼ (left-whisker f H')`.

The argument here is a little opaque, but you can glean some intuition for what is going on by consulting the n-cat lab page on [adjoint equivalences](https://ncatlab.org/nlab/show/adjoint+equivalence). It describes this construction in terms of some nice looking _string diagrams_.

First we should fill in some basic facts about the functoriality of path composition that we missed earlier. I'll allow myself the luxury of pattern matching - these are all routine proofs with raw path induction but time is short...

```agda
module _ {i : Level} {A : UU i} {a a' a'' : A} where
    left-concat-ap : (p : a ≡ a') {q q' : a' ≡ a''} (s : q ≡ q') → (p · q ≡ p · q')
    left-concat-ap p s = ap (λ q → p · q) s

    right-concat-ap : {p p' : a ≡ a'} (r : p ≡ p') (q : a' ≡ a'') → (p · q ≡ p' · q)
    right-concat-ap r q = ap (λ p → p · q) r

    left-concat-ap-inv : (p : a ≡ a') {q q' : a' ≡ a''} (s : q ≡ q') →
        left-concat-ap p (inv s) ≡ inv (left-concat-ap p s)
    left-concat-ap-inv _ refl = refl

    right-concat-ap-inv : {p p' : a ≡ a'} (r : p ≡ p') (q : a' ≡ a'') →
        right-concat-ap (inv r) q ≡ inv (right-concat-ap r q)
    right-concat-ap-inv refl _ = refl

    left-concat-ap-concat : (p : a ≡ a') {q q' q'' : a' ≡ a''} (s : q ≡ q') (s' : q' ≡ q'') →
        left-concat-ap p (s · s') ≡ (left-concat-ap p s) · (left-concat-ap p s')
    left-concat-ap-concat _ refl _ = refl

    right-concat-ap-concat : {p p' p'' : a ≡ a'} (r : p ≡ p') (r' : p' ≡ p'') (q : a' ≡ a'') →
        right-concat-ap (r · r') q ≡ (right-concat-ap r q) · (right-concat-ap r' q)
    right-concat-ap-concat refl _ _ = refl

    right-concat-cancel : {p p' : a ≡ a'} (q : a' ≡ a'') → (p · q ≡ p' · q) → p ≡ p'
    right-concat-cancel refl r = (inv right-unit) · r · right-unit

    left-concat-cancel : (p : a ≡ a') {q q' : a' ≡ a''} → (p · q ≡ p · q') → q ≡ q'
    left-concat-cancel refl s = s
```

To break up this proof a little we first use naturality of homotopies to prove the following lemma (Definition 10.4.4).

```agda
htpy-to-id-nat : {i : Level} {A : UU i} {f : A → A} (H : f ∼ id) {x : A} → ap f (H x) ≡ H (f x)
htpy-to-id-nat {f = f} H {x = x} =
    right-concat-cancel (H x) (htpy-naturality H (H x) · left-concat-ap (H (f x)) ap-id)

htpy-to-id-nat-htpy : {i : Level} {A : UU i} {f : A → A} (H : f ∼ id) →
                      left-whisker f H ∼ right-whisker H f
htpy-to-id-nat-htpy {f = f} H x = htpy-to-id-nat H {x = x}
```

Now we get the following, slightly horrible, computation to establish Theorem 10.4.5.

```agda
has-inverse-implies-is-coh-invertible :
    {i j : Level} {A : UU i} {B : UU j} {e : A → B} → has-inverse e → is-coh-invertible e
has-inverse-implies-is-coh-invertible {A = A} {B = B} {e = e} (pair e' (pair G H)) = pair e' (pair G (pair H' (inv-htpy K)))
    where
        H' : e' ∘ e ∼ id
        H' = left-whisker (e' ∘ e) (inv-htpy H) ∙ left-whisker e' (right-whisker G e) ∙ H

        section-whiskering-naturality :
            left-whisker e (left-whisker e' (right-whisker G e)) ∼
            right-whisker (right-whisker G e) (e' ∘ e)
        section-whiskering-naturality = left-whisker-comp-htpy (right-whisker G e) e' e ∙
                                        right-whisker-htpy (htpy-to-id-nat-htpy G) e

        retraction-naturality-square :
            (right-whisker (right-whisker G e) (e' ∘ e)) ∙ (left-whisker e H) ∼
            (left-whisker (e ∘ e' ∘ e) H) ∙ (right-whisker G e)
        retraction-naturality-square = inv-htpy (htpy-naturality-htpy (right-whisker G e) H)

        whiskered-coherence-square :
            left-whisker e (left-whisker e' (right-whisker G e) ∙ H) ∼
            (left-whisker (e ∘ e' ∘ e) H) ∙ (right-whisker G e)
        whiskered-coherence-square =
            left-whisker-concat-htpy (left-whisker e' (right-whisker G e)) H e ∙
            left-concat-htpy {A = A} {B = λ _ → B} {K = left-whisker e H} section-whiskering-naturality ∙
            retraction-naturality-square

        inverse-insertion : (e ∘ (e' ∘ e)) ∼ (e ∘ ((e' ∘ e) ∘ (e' ∘ e)))
        inverse-insertion = left-whisker e (left-whisker (e' ∘ e) (inv-htpy H))

        inverse-removal : (e ∘ ((e' ∘ e) ∘ (e' ∘ e))) ∼ (e ∘ (e' ∘ e))
        inverse-removal = left-whisker (e ∘ (e' ∘ e)) H

        K : (left-whisker e H') ∼ (right-whisker G e)
        K = left-whisker-concat-htpy (left-whisker (e' ∘ e) (inv-htpy H)) (left-whisker e' (right-whisker G e) ∙ H) e ∙
            right-concat-htpy {H = inverse-insertion} whiskered-coherence-square ∙
            inv-htpy (assoc-htpy {G = inverse-insertion} {H = inverse-removal}) ∙
            left-concat-htpy (left-whisker-inv-cancel-htpy (e' ∘ e) e H) ∙ left-unit-htpy
```

This deserves to be cleaned up, but let's press on. Combining earlier lemmas with this coherence theorem we finally get.

```agda
equiv-to-contr-map : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → is-contr-map f
equiv-to-contr-map = coh-inverse-implies-contr-map ∘ has-inverse-implies-is-coh-invertible ∘
                        is-equiv-to-has-inverse

contr-map-to-equiv : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-contr-map f → is-equiv f
contr-map-to-equiv s = let (pair f' (pair G (pair H _))) = contr-map-has-coh-inverse s
                       in pair (pair f' G) (pair f' H)
```

### Equivalences and contractible types

If two types are connected by an equivalence then one is contractible if and only if the other one is. Following our class discussion we prove this my applying the 2-or-3 property to a characterisation of contractible types as those that are equivalent to `𝟙`. First some facts about maps into `𝟙`.

```agda
! : {i : Level} {A : UU i} → A → 𝟙
! _ = ∗

unique-to-contr : {i j : Level} {A : UU i} {B : UU j} {f g : A → B} → is-contr B → f ∼ g
unique-to-contr {f = f} {g = g} (pair _ H) x = inv (H (f x)) · H (g x)

unique-to-unit : {i : Level} {A : UU i} {f g : A → 𝟙} → f ∼ g
unique-to-unit = unique-to-contr unit-is-contr

pt : {i : Level} {A : UU i} → A → 𝟙 → A
pt = const
```

And now we prove that a type is contractible if and only if its unique map to the unit type is an equivalence.

```agda
contr-is-equiv-unit : {i : Level} {A : UU i} → is-contr A → is-equiv (! {A = A})
contr-is-equiv-unit (pair a H) = pair (pair (pt a) unique-to-unit) (pair (pt a) H)

equiv-unit-is-contr : {i : Level} {A : UU i} → is-equiv (! {A = A}) → is-contr A
equiv-unit-is-contr (pair _ (pair h H)) = pair (h ∗) H
```

Now we can use Exercise 9.1, the 2-of-3 property, to prove the desired stability result for contractability.

```agda
transport-of-contr-along-equiv : {i j : Level} {A : UU i} {B : UU j} → A ≃ B → is-contr A → is-contr B
transport-of-contr-along-equiv  (pair h s) t =
    equiv-unit-is-contr (right-cancel-equiv unique-to-unit s (contr-is-equiv-unit t))

transport-of-contr-along-equiv' : {i j : Level} {A : UU i} {B : UU j} → A ≃ B → is-contr B → is-contr A
transport-of-contr-along-equiv' (pair h s) u =
    equiv-unit-is-contr (compose-equiv unique-to-unit (contr-is-equiv-unit u) s)
```

Of course, the same line of reasoning also tells us that all maps between contractible spaces are equivalences.

```agda
map-of-contr-is-equiv : {i j : Level} {A : UU i} {B : UU j} {h : A → B} →
    is-contr A → is-contr B → is-equiv h
map-of-contr-is-equiv s t =
    left-cancel-equiv unique-to-unit (contr-is-equiv-unit t) (contr-is-equiv-unit s)
```

## The fundamental theorem of identity types

This theorem characterises those families of types that are (pointwise) equivalent to the identity types on a type `A` and provides us with a (propositional) induction principle for such types.

### Families of equivalences

Now we define the _total map_ associated with a family of maps...

```agda
tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} (f : {a : A} → B a → C a) →
      Σ a ∈ A , B a → Σ a ∈ A , C a
tot f (pair a b) = pair a (f b)
```

...and relate its fibres to the fibres of family members (Lemma 11.1.2 of [Rijke](https://arxiv.org/abs/2212.11082)).

```agda
tot-fibs : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} {f : {a : A} → B a → C a}
           {t : Σ a ∈ A , C a} → fib (tot f) t ≃ fib f (pr₂ t)
tot-fibs {A = A} {C = C} {f = f} = pair φ (pair (pair φ' counit) (pair φ' unit))
    where
        φ : {t : Σ a ∈ A , C a} → fib (tot f) t → fib (f {a = pr₁ t}) (pr₂ t)
        φ (pair (pair a b) p) = ind-≡ (λ {t} p → fib f (pr₂ t)) (pair b refl) p

        φ' : {t : Σ a ∈ A , C a} → fib (f {a = pr₁ t}) (pr₂ t) → fib (tot f) t
        φ' {t = pair a c} (pair b q) = ind-≡ (λ {c} q → fib (tot f) (pair a c)) (pair (pair a b) refl) q

        unit : {t : Σ a ∈ A , C a} → φ' ∘ (φ {t = t}) ∼ id
        unit (pair (pair a b) p) = ind-≡ (λ p → (φ' ∘ φ) (pair (pair a b) p) ≡ pair (pair a b) p) refl p

        counit : {t : Σ a ∈ A , C a} → φ ∘ (φ' {t = t}) ∼ id
        counit {t = pair a c} (pair b q) = ind-≡ (λ q → (φ ∘ φ') (pair b q) ≡ pair b q) refl q
```

Now as a payoff for out hard work on contractible maps and coherent inverses, we get the following characterisation of families of equivalences. Specifically a family of maps is a family of equivalences if and only if it's total map is an equivalence.

```agda
tot-of-equiv-family-is-equiv : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k}
    {f : {x : A} → B x → C x} → ((x : A) → is-equiv (f {x = x})) → is-equiv {A = Σ a ∈ A , B a} (tot f)
tot-of-equiv-family-is-equiv {A = A} {B = B} {f = f} s = contr-map-to-equiv contr-tot-f
    where
        contr-f : (x : A) → is-contr-map (f {x = x})
        contr-f x = equiv-to-contr-map (s x)

        contr-tot-f : is-contr-map {A = Σ a ∈ A , B a} (tot f)
        contr-tot-f (pair a c) = transport-of-contr-along-equiv' tot-fibs (contr-f a c)

equiv-tot-implies-equiv-family : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k}
    {f : {x : A} → B x → C x} → is-equiv {A = Σ a ∈ A , B a} (tot f) → (x : A) → is-equiv (f {x = x})
equiv-tot-implies-equiv-family {A = A} {B = B} {f = f} t = contr-map-to-equiv ∘ contr-f
    where
        contr-tot-f : is-contr-map {A = Σ a ∈ A , B a} (tot f)
        contr-tot-f = equiv-to-contr-map t

        contr-f : (x : A) → is-contr-map (f {x = x})
        contr-f x c = transport-of-contr-along-equiv tot-fibs (contr-tot-f (pair x c))
```

### Identity systems and the fundamental theorem

Given a type family `B : A → UU j` we would like to know when it is familiarly equivalent to the identity type family `λ x → a ≡ x : A → UU i` for some fixed `a : A`. For example, this is important when we are trying to find observational variants of identity types, such as the John Major equality that observationally captures identities between elements of a sum type.

Notice, however, that the path space `path-space a ≔ Σ x ∈ A , a ≡ x` is also the total map associated with the family `λ x → a ≡ x` and we already know that it is contractible. So we can combine our characterisation of families of equivalences as being those families whose total map is an equivalence with the stability results we've just derived for contractible spaces to prove the following result characterising those type families that are equivalent to `λ x → a ≡ x`:

```agda
fundamental-≡-one : {i j : Level} {A : UU i} {B : A → UU j} {a : A} {f : {x : A} → a ≡ x → B x} →
                    is-contr(Σ x ∈ A , B x) → (x : A) → is-equiv (f {x = x})
fundamental-≡-one {a = a} {f = f} s =
    equiv-tot-implies-equiv-family {f = f} (map-of-contr-is-equiv (path-space-is-contr a) s)

fundamental-≡-two : {i j : Level} {A : UU i} {B : A → UU j} {a : A} {f : {x : A} → a ≡ x → B x} →
                    ((x : A) → is-equiv (f {x = x})) → is-contr(Σ x ∈ A , B x)
fundamental-≡-two {a = a} {f = f} t =
    transport-of-contr-along-equiv (pair (tot f) (tot-of-equiv-family-is-equiv t)) (path-space-is-contr a)
```

We might hope that a family of types that is equivalent to the family of identity types based at `a : A` would inherit some aspect of the path induction principle. We can't ask for this induction principle to be **definitional**, but we can at least ask for some kind of propositionally valid instance. These are expressed using _identity systems_ which are defined to be types dependent on `A` and `B` for which a certain projection

### Characterising the identity type on fibres

As an application of the fundamental theorem we provide a characterisation of the identity types on the fibres of a map. First we give our candidate observational equality ...

```agda
module _ {i j : Level} {A : UU i} {B : UU j} {f : A → B} where
    fib-≡ : {b : B} → (s t : fib f b) → UU (i ⊔ j)
    fib-≡ (pair a p) (pair a' p') = Σ q ∈ (a ≡ a') , (ap f q · p' ≡ p)
```
... and define its comparison with the identity type ...

```agda
    fib-≡-compare : {b : B} {s t : fib f b} → (s ≡ t) → fib-≡ s t
    fib-≡-compare {s = s} = ind-≡ (λ {t} p → fib-≡ s t) (pair refl refl)
```

... which we show is an equivalence by demonstrating that for all `s : fib f b` the total space of `fib-≡ s ∶ fib f b → UU (i ⊔ j)` is contractible.

```agda
    fib-≡-tot-contr : {b : B} {s : fib f b} → is-contr (Σ t ∈ fib f b , fib-≡ s t)
    fib-≡-tot-contr {b = b} {s = s} = pair (pair s (pair refl refl)) H
        where
            H : (u : Σ t ∈ fib f b , fib-≡ s t) → pair s (pair refl refl) ≡ u
            H (pair (pair a r) (pair q p)) = outer q p
                where
                    inner : {r : f (pr₁ s) ≡ b} (p : r ≡ pr₂ s) → pair s (pair refl refl) ≡ pair (pair (pr₁ s) r) (pair refl p)
                    inner = ind-≡' (λ {r} p → pair s (pair refl refl) ≡ pair (pair (pr₁ s) r) (pair refl p)) refl 

                    outer : {a : A} (q : pr₁ s ≡ a) {r : f a ≡ b} (p : ap f q · r ≡ pr₂ s) → pair s (pair refl refl) ≡ pair (pair a r) (pair q p)
                    outer = ind-≡ (λ {a} q → {r : f a ≡ b} (p : ap f q · r ≡ pr₂ s) → pair s (pair refl refl) ≡ pair (pair a r) (pair q p)) inner

    fib-≡-compare-equiv : {b : B} {s t : fib f b} → is-equiv (fib-≡-compare {s = s} {t = t})
    fib-≡-compare-equiv {s = s} {t = t} = fundamental-≡-one {f = fib-≡-compare {s = s}} fib-≡-tot-contr t 
```

### Embeddings

In Definition 11.4.1 of [Rijke](https://arxiv.org/abs/2212.11082) we are introduced to _embeddings_, which are maps whose actions on identity types are equivalences.

```agda
is-emb : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-emb {A = A} f = {a a' : A} → is-equiv (ap f {a = a} {a' = a'})
```

Now Theorem 11.4.2 tells us that if a map is an equivalence then it is an embedding. We'll prove this directly, by first showing that if `f` has an inverse then it is an embedding.

```comment
concat-left-ap : {i : Level} {A : UU i} {a a' a'' : A} {q q' : a' ≡ a''} →
                 (p : a ≡ a') → q ≡ q' → p · q ≡ p · q'
concat-left-ap p r = ap (λ q → p · q) r

concat-right-ap : {i : Level} {A : UU i} {a a' a'' : A} {p p' : a ≡ a'} →
                 p ≡ p' → (q : a' ≡ a'') → p · q ≡ p' · q
concat-right-ap s q = ap (λ p → p · q) s

has-inverse-implies-emb : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → has-inverse f → is-emb f
has-inverse-implies-emb {A = A} f (pair g (pair sec-htpy retr-htpy)) {a = a} =
    pair (pair φ' counit) (pair φ' unit)
    where
        φ : {a' : A} → a ≡ a' → f a ≡ f a'
        φ = ap f

        φ' : {a' : A} → f a ≡ f a' → a ≡ a'
        φ' {a' = a'} q = (inv (retr-htpy a)) · (ap g q) · (retr-htpy a')

        unit : {a' : A} → φ' ∘ (φ {a' = a'}) ∼ id
        unit = ind-≡ (λ p → (φ' ∘ φ) p ≡ p) (left-inv {p = retr-htpy a})

        counit : {a' : A} → φ ∘ (φ' {a' = a'}) ∼ id
        counit = {!  !}
```
