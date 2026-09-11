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
module exercises6 where
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

open dsum
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
ind-≡ : {i j : Level}{A : UU i}{a : A}(B : (x : A) → a ≡ x → UU j) → (b : B a refl) → 
         {x : A} → (p : a ≡ x) → B x p
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
tr {B = B} p b = ind-≡ (λ x _ → B x) b p

tr-refl : {i j : Level}{A : UU i}{B : A → UU j}{a : A}{b : B a} → (tr {B = B} refl b ≡ b)
tr-refl = refl
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

Here is the Agda presentation of Definition 9.1.7 of [Rijke](https://arxiv.org/abs/2212.11082):

```agda
left-whisker : {i j k : Level}{A : UU i}{B : UU j}{C : UU k}{f g : A → B} → 
               (h : B → C) → (f ∼ g) → (h ∘ f ∼ h ∘ g)
left-whisker h H x = ap h (H x)

right-whisker : {i j k : Level}{A : UU i}{B : UU j}{C : UU k}{g h : B → C} → 
                (g ∼ h) → (f : A → B) → (g ∘ f ∼ h ∘ f)
right-whisker H f x = H (f x)
```

Here the `∘` operation denotes _function composition_ `(g ∘ f) x := g (f x)`, and this symbol is entered using the character sequence `\circ` or simply `\o`.

With a little extra work these can be extended to dependently typed functions, but at this stage that process will introduce complications that we should't worry ourselves with just yet.

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
pair-≅ refl = refl-≅
```

#### Show that `pair-≅` is an equivalence....

...by first defining a map in the opposite direction. First recall that in exercise 5.3 we defined a map to lift identifications in `A` to identifications in `Σ x ∈ A , B x`.

```agda
lift : {i j : Level}{A : UU i}{B : A → UU j} (s : Σ x ∈ A , B x) {a : A} (p : pr₁ s ≡ a) → 
       s ≡ pair a (tr p (pr₂ s))
lift s p = ind-≡ (λ x q → s ≡ pair x (tr q (pr₂ s))) refl p
```

So if `(pair p q)` is an element of `s ≅ t` then its first component has type `p : pr₁ s ≡ pr₁ t` and its second component has type `q : tr p (pr₂ s) ≡ pr₂ t`. So we can lift `p` to an identification `lift s p : s ≡ pair (pr₁ t) (tr p (pr₂ s))` and then compose that with the identification that we get by applying `pair (pr₁ t) : B (pr₁ t) → Σ x ∈ A, B x` to `q`.

```agda
≅-pair : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} → s ≅ t → s ≡ t
≅-pair {A = A} {B = B} {s = s} {t = t} = ind-Σ (λ p q → concat (lift s p) (ap (pair (pr₁ t)) q))
``` 

This was a little harder, but it becomes pretty much trivial if we use pattern matching instead (which is how Egbert explained this proof).

```agda
≅-pair' : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} → s ≅ t → s ≡ t
≅-pair' (pair refl refl) = refl
```

Now we finish up by showing that `pair-≅` is both a section and a retraction of `≅-pair` - to do this we'll allow ourselves the luxury of pattern matching:

```agda
pair-≅-retraction : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} → 
                    (≅-pair ∘ pair-≅ ∼ id {A = s ≡ t})
pair-≅-retraction refl = refl

pair-≅-section : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} → 
                    (pair-≅ ∘ ≅-pair ∼ id {A = s ≅ t})
pair-≅-section (pair refl refl) = refl

pair-≅-equiv : {i j : Level}{A : UU i}{B : A → UU j}{s t : Σ x ∈ A , B x} → is-equiv (pair-≅ {s = s} {t = t})
pair-≅-equiv = pair (pair ≅-pair pair-≅-section) (pair ≅-pair pair-≅-retraction)
```