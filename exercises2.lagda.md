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
module exercises2 where
```

**Note:** the `module-name` must match the base of the file name `module-name.lagda.md`. The extension `.lagda.md` tells Agda that this is a **literate file** written in the markup language [Markdown](https://markdown.org). The contents of the file itself is intended to be a human readable document, with Agda code interspersed throughout and enclosed **fenced code blocks**. These start with \`\`\` or \`\`\`agda on its own line, and end with \`\`\`, also on its own line

Next we import any modules that contain Agda code that this module depends upon.

```agda
open import Agda.Primitive public
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

In the last set of exercises our propositions were all types inhabiting the lowest level universe `UU lzero`. For what follows we'll generalise this to allow types in any universe to be regarded as propositions. This means that we have to worry a little about _generalising_ our definitions over universe levels, which we do by adding an extra parameter of type `Level` to out `data` and function definitions.

First our fixity and data type  declarations.

```agda 
infixr 2 _∧_
infixr 1 _∨_
infixr 0 _⇒_

data _∧_ {i j : Level} (A : UU i) (B : UU j) : UU (i ⊔ j) where
    pair : A → B → A ∧ B

data _∨_ {i j : Level} (A : UU i) (B : UU j) : UU (i ⊔ j) where
    inl : A → A ∨ B
    inr : B → A ∨ B

data _⇒_ {i j : Level} (A : UU i) (B : UU j) : UU (i ⊔ j) where
    ⇒-intro : (A → B) → A ⇒ B
```

Now these all have [_implicit arguments_](https://agda.readthedocs.io/en/v2.8.0-r3/language/implicit-arguments.html) `i` and `j` which are universe `Level`s, and their parameters `A` and `B` are now declared to live in two (possibly distinct) universes `UU i` and `UU j` respectively. This allows us to apply our logical connectives `∧`, `∨` and `⇒` to be propositions that live in arbitrary universes. The only question then is when the propositions `A` and `B` lie in separate universes where should the associated propositions `A ∧ B`, `A ∨ B` and `A ⇒ B` live? The answer is that they live in the universe `UU (i ⊔ j) whose level is the _maximum_ `i ⊔ j` of the levels `i` and `j`. You can read more about the calculus of universe levels [here](https://agda.readthedocs.io/en/v2.8.0-r3/language/universe-levels.html).

We also have our top and bottom propositions and negation, along with our various introduction and elimination rules.

```agda
infixr 3 ¬_

data ⊥ : UU lzero where

data ⊤ : UU lzero where
    tt : ⊤

¬_ : {i : Level} (A : UU i) → UU i 
¬ A = A ⇒ ⊥ 

pattern ∧-intro p q = pair p q

∧-elim-left : {i j : Level} {A : UU i} {B : UU j} → A ∧ B → A
∧-elim-left (∧-intro p _) = p

∧-elim-right : {i j : Level} {A : UU i} {B : UU j} → A ∧ B → B
∧-elim-right (∧-intro _ q) = q

pattern ∨-intro-left p = inl p
pattern ∨-intro-right q = inr q

∨-elim : {i j k : Level} {A : UU i} {B : UU j} {P : UU k} → 
            (A → P) → (B → P) → A ∨ B → P 
∨-elim f _ (∨-intro-left p) = f p
∨-elim _ g (∨-intro-right q) = g q

⇒-elim : {i j : Level} {A : UU i} {B : UU j} → (A ⇒ B) → A → B
⇒-elim (⇒-intro f) q = f q

⊥-elim : {i : Level} {A : UU i} → ⊥ → A 
⊥-elim ()

pattern ⊤-intro = tt

¬-intro : {i : Level} {A : UU i} → (A → ⊥) → ¬ A
¬-intro f = ⇒-intro f

¬-elim : {i j : Level} {A : UU i} {B : UU j} → ¬ A → A → B
¬-elim (⇒-intro f) p = ⊥-elim (f p)
```

**Note:** I've changed things up a little here by defining `∧-intro`, `∨-intro-left`, and `∨-intro-right` as [_pattern synonyms_](https://agda.readthedocs.io/en/v2.8.0-r3/language/pattern-synonyms.html). This allows us to use them as synonyms for the corresponding constructors `pair`, `inl` and `inr` both in expressions **and** in patterns (which we have done in some of the function definitions above). 

To emphasise one of our discussions from class, we note that the proposition `A ⇒ B` and Agda's (_non-dependent_) function type `A → B` are _isomorphic_ types, which is to say that to all intents and purposes they are interchangeable. Indeed the introduction and elimination rules `⇒-intro` and `⇒-elim` provide the two functions between them that we would expect from an isomorphism. There are, however, two reasons for choosing to carefully distinguish these types:

1. By distinguishing them _notatationally_ we are emphasising the _semantic_ point that we regard `A ⇒ B` as being an implicational proposition rather than a function type.

2. We enforce the requirement that the proofs of `A ⇒ B` are **non-dependently** typed functions. In the next section we shall see that types of dependently typed functions actually correspond to _universal quantification_ rather than implication.

### Exercises

Before moving on, we have a few exercises we didn't get round to last week. I always find proving statements that involve negation (`¬`) to be a little more tricky. There are deep reasons for this which can be related to the equally delicate notion of [_continuation_](https://en.wikipedia.org/wiki/Continuation-passing_style) in the world of the λ-calculus and functional programming.

#### Exercise 2.1

Define the rule `contrapositive` whose conclusion is that not `P` implies not `Q` under the supposition that `Q` implies `P`.

```agda
contrapositive : {i j : Level} {P : UU i} {Q : UU j} → (P ⇒ Q) → (¬ Q ⇒ ¬ P)
contrapositive p = {!   !}
```

#### Exercise 2.2 

Define `intro-dn`, proving that `P` implies `¬ ¬ P`

```agda
intro-dn : {i : Level} {P : UU i} → P ⇒ ¬ ¬ P 
intro-dn = {!   !}
```

#### Exercise 2.3

Prove the following _weak de Morgan's laws_.

```agda
deMorgan_∧_to_∨ : {i j : Level} {A : UU i} {B : UU j} → ¬ A ∧ ¬ B ⇒ ¬ (A ∨ B)
deMorgan_∧_to_∨ = {!   !}

deMorgan_∨_to_∧ : {i j : Level} {A : UU i} {B : UU j} → ¬ A ∨ ¬ B ⇒ ¬ (A ∧ B)
deMorgan_∨_to_∧ = {!   !}
```

In [_classical logic_](https://en.wikipedia.org/wiki/Classical_logic) the reverse direction of these implications also holds, but dependent type theory is an [_intuitionistic logic_](https://en.wikipedia.org/wiki/Intuitionistic_logic) in which that is **not** the case.

#### Exercise 2.4

Define `dn-elim-neg`, proving that `¬ ¬ ¬ P` implies `¬ P` 

```agda
dn-elim-neg : {i : Level}{P : UU i} → ¬ ¬ ¬ P ⇒ ¬ P
dn-elim-neg = {!   !}
```

#### Exercise 2.5

Define `lem-dn-elim`, proving that that _law of excluded middle_ `P ∨ ¬ P` implies _double negation elimination_ `¬ ¬ P ⇒ P`.

```agda
lem-dn-elim : {i : Level} {P : UU i} → P ∨ ¬ P ⇒ (¬ ¬ P ⇒ P)
lem-dn-elim = {!   !}
```

#### Challenge Exercise 2.6 

Define `nn-lem`, proving that the law of excluded middle is not false

```agda 
nn-lem : {i : Level}{P : UU i} → ¬ ¬ (P ∨ ¬ P)
nn-lem =  {!   !}
```

**Hint:** You might choose to define auxiliary functions 
* `¬∨-elim-left : {i j : Level}{A : UU i}{B : UU j} → ¬ (A ∨ B) → ¬ A` and 
* `¬∨-elim-right : {i j : Level}{A : UU i}{B : UU j} → ¬ (A ∨ B) → ¬ B`.

#### Challenge Exercise 2.7 

Prove that double negation elimination is not false by defining `dn-dn-elim`

```agda
dn-dn-elim : {i : Level} {P : UU i} → ¬ ¬ (¬ ¬ P ⇒ P)
dn-dn-elim =  {!   !}
``` 

#### Challenge Exercise 2.7 

Define `dn-elim-lem`, proving that if double negation elimination holds for all types `P` then the law of the excluded middle holds for all types `Q`. The type signature for this term is as follows.

```agda
dn-elim-lem : ({i : Level} {P : UU i} → (¬ ¬ P ⇒ P)) → ({j : Level} {Q : UU j} → Q ∨ ¬ Q)
dn-elim-lem p = {!   !}
```

The meaning of this type signature is a little bit opaque, so let's take a little time to parse it in more detail. Firstly it states that `dn-elim-lem` takes a parameter `p` of type `{i : Level} {P : UU i} → (¬ ¬ P ⇒ P)`,  in other words a _dependent function_ ,which takes (implicit) inputs a universe level `i` and a type `P` in the corresponding universe and returns a term of type `¬ ¬ P ⇒ P`. In logical terms we can think of `p` as being a _axiom scheme_ that provides a proof of the proposition `¬ ¬ P ⇒ P` for each proposition `P`, hence it posits that double elimination holds for all types `P`.

In a similar manner, the return type `{j : Level} {Q : UU j} → Q ∨ ¬ Q` of `dn-elim-lem` denotes a dependent function which takes arguments a universe level `j` and a type `Q` in the corresponding universe and returns a term of type `Q ∨ ¬ Q`. So in logical terms we may regard this as a _proof scheme_ that provides a proof of the proposition `Q ∨ ¬ Q` for each proposition `Q`.

**Hint:** apply the axiom scheme `p` with `P := Q ∨ ¬ Q`.

Our lemmas `dn-elim-lem` and `lem-dn-elim` together show that the law of the excluded middle and the double negation elimination law are equivalent. More precisely if we enhance our logic by adding either of these as a _postulate_ then we obtain equivalent logics. Indeed, to obtain classical logic from our intuitionistic one it suffices to add one or other of these laws as an assumption.

## Universal quantification

The type signature discussed in Exercise 2.7 points the way to encoding universal quantification in dependent type theory. We could just use raw dependent function types as we did there, but we choose instead to follow the methodology we adopted for `⇒` and introduce a new wrapper type.

```agda
data all {i j : Level}{A : UU i}(P : A → UU j): UU (i ⊔ j) where
    all-intro : ((a : A) → P a) → all P
```

We can also provide some [_syntactic sugar_](https://agda.readthedocs.io/en/v2.8.0-r3/language/syntax-declarations.html) to enable the use of notation for this quantifier which looks like standard usage.

```agda
syntax all (λ x → P) = ∀' x , P
```

Here we've had to use the name `∀'` for our universal quantifier because the undecorated symbol `∀` is already reserved for use by Agda itself. The elimination rule for universal quantification follows a pattern familiar from our discussion of implication `⇒`.

```agda
all-elim : {i j : Level}{A : UU i}{P : A → UU j} → (all P) → (a : A) → P a 
all-elim (all-intro f) a = f a
```

### Exercises

I guess we're obliged to prove a few lemmas about universal quantification, but lets keep this to a minimum so that we can move on to the existential.

#### Exercise 2.8

Prove the distributivity of the universal quantifier over conjunction.

```agda
∀-distributes-over-∧ : {i j k : Level}{A : UU i}{P : A → UU j}{Q : A → UU k} →
                       ∀' x , (P x ∧ Q x) → (∀' x , P x) ∧ (∀' x , Q x)
∀-distributes-over-∧ (all-intro f) = {!   !}

∀-distributes-over-∧' : {i j k : Level}{A : UU i}{P : A → UU j}{Q : A → UU k} →
                        (∀' x , P x) ∧ (∀' x , Q x) → ∀' x , (P x ∧ Q x)
∀-distributes-over-∧' (∧-intro p q) = {!   !}
```

#### Exercise 2.9

Prove the _weak_ distributivity of universal quantification over disjunction.

```agda
∀-distributes-over-∨ : {i j k : Level}{A : UU i}{P : A → UU j}{Q : A → UU k} →
                       (∀' x , P x) ∨ (∀' x , Q x) → ∀' x , (P x ∨ Q x)
∀-distributes-over-∨ p = {!   !}
```

This is called weak distributivity because the reverse implication does **not** hold.

#### Exercise 2.10

Prove the distributivity of universal quantification over implication.

```agda
∀-distributes-over-⇒ : {i j k : Level}{A : UU i}{P : UU j}{Q : A → UU k} →
                       ∀' x , (P ⇒ Q x) → P ⇒ (∀' x , Q x)
∀-distributes-over-⇒ p = {!   !}

∀-distributes-over-⇒' : {i j k : Level}{A : UU i}{P : UU j}{Q : A → UU k} →
                        P ⇒ (∀' x , Q x) → ∀' x , (P ⇒ Q x)
∀-distributes-over-⇒' p = {!   !}
```

Notice that for `∀' x . _` to distribute over `P ⇒ Q` we require that `P` does not depend on `x` and then `∀' x . P ⇒ Q` is equivalent to `P ⇒ ∀ x . Q`.

#### Exercise 2.11

Prove commutativity for universal quantifiers.

```agda
∀-commutes : {i j k : Level}{A : UU i}{B : UU j}{P : A → B → UU k} →
             ∀' x  , (∀' y , P x y) → ∀' y , (∀' x , P x y)
∀-commutes p = {!   !}

∀-commutes' : {i j k : Level}{A : UU i}{B : UU j}{P : A → B → UU k} →
              ∀' y , (∀' x , P x y) → ∀' x  , (∀' y , P x y)
∀-commutes' p = {!   !}
```

## Existential quantification

Given a type `A` and a predicate `P : A → UU i`, our (constructive) intuition leads us to suspect that in order to prove that an existential statement `∃ x , P x` we must give:

* an element (term) `a` of type `A`, **and** 
* a proof `p` of `P a`. 

In other words, `∃ x , P x` is a type of **dependent pairs** `(a : A, p : P a)`, in which the type of the second component _depends_ on the first component. In Agda we can again define this as an algebraic datatype.

```agda
data exists {i j : Level}{A : UU i}(P : A → UU j): UU (i ⊔ j) where
    exists-intro : (a : A) → (p : P a) → exists P

syntax exists (λ x → P) = ∃' x , P
```

As in our earlier examples, this data declaration defines the introduction rule for existential quantification as a constructor. Its elimination rule can now be derived by pattern matching. To parse the structure of this rule you can think of the quantified statement `∃' x , P x` as being akin to an _infinite disjunction_ `P a₁ ∨ P a₂ ∨ P a₃ ∨ ... ∨ P aₙ ∨ ...` where the `aₙ`s are the elements of `A`. So we might expect it too follow the form established in our discussion of disjunction elimination.

```agda
exists-elim : {i j k : Level}{A : UU i}{P : A → UU j}{Q : UU k} → ((a : A) → P a → Q) → ∃' x , P x → Q
exists-elim f (exists-intro a p) = f a p
```

The parameter of this rule of type `(a : A) → P a → Q` is a function which for each `a : A` gives a procedure which maps a proof of `P a` to a proof of `Q`. With that in mind, now compare this rule to the disjunction elimination rule.

Now given a proof of an existential statement we can extract two pieces of information

* A witnessing value `a : A` at which the quantified proposition holds, and 
* A proof that the proposition `P a` holds.

```agda
witness : {i j : Level}{A : UU i}{P : A → UU j} → ∃' x , P x → A 
witness (exists-intro a p) = a

witnessing-proof : {i j : Level}{A : UU i}{P : A → UU j} → (p : ∃' x , P x) → P (witness p)
witnessing-proof (exists-intro a p) = p 
```

### Exercises

#### Exercise 2.12

Prove the distributivity of existential quantification over disjunction. I'll leave the type signature of this one to you.

#### Exercise 2.13

Prove the _weak_ quantifier negation rules.

```agda 
exists-neg-implies-neg-all : {i j : Level}{A : UU i}{P : A → UU j} → ∃' x , (¬ P x) → ¬ (∀' x , P x)
exists-neg-implies-neg-all p = {!   !}

all-neg-implies-neg-exists : {i j : Level}{A : UU i}{P : A → UU j} → ∀' x , (¬ P x) → ¬ (∃' x , P x)
all-neg-implies-neg-exists p = {!   !}
```

The converse rules do **not** hold in our intuitionistic system, but they can be proved if we assume the law of the excluded middle.

### Exercise 2.14

Prove the _type theoretic axiom of choice_ in the following form.

```agda 
tt_axiom_of_choice : {i j k : Level}{A : UU i}{B : UU j}{P : A → B → UU k} → 
       ∀' x , (∃' y , P x y) → ∃' f , (∀' x , P x (f x))
tt_axiom_of_choice p = {!   !}
```
