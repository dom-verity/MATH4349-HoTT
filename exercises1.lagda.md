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
module exercises1 where
```

**Note:** the `module-name` must match the base of the file name `module-name.lagda.md`. The extension `.lagda.md` tells Agda that this is a **literate file** written in the markup language [Markdown](https://markdown.org). The contents of the file itself is intended to be a human readable document, with Agda code interspersed throughout and enclosed **fenced code blocks**. These start with \`\`\` or \`\`\`agda on its own line, and end with \`\`\`, also on its own line

Next we import any modules that contain Adga code that this module depends upon.

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

## Natural numbers

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

Later on we will see how we can build a function which encapsulates the the usual natural number **induction principle** using the **pattern matching** facilities of Agda. We won't do that here, since we haven't yet discussed the general form of data types and the rules that define them, but we will have lots to say about induction in type theory as we go along.

For the moment, we'll just amuse ourselves with some basic exercises: 

**Note:** To insert the natural number symbol ℕ type the character sequence "\\bN". Watch what happens at the bottom of the Visual Studio Code as you do for clues on how to insert other mathematical characters. By typing "\\" we enter _unicode input mode_, which allows us to translate the subsequent character sequence into a unicode symbol.

### Exercise 1.1: Define a function to add two natual numbers:

```agda 
add-ℕ : ℕ → ℕ → ℕ
add-ℕ n m = {!   !}
```

**Hint:** pattern match the first parameter `n` and you'll then two cases `n = ℕ-zero` and `n = ℕ-zero n'`for some value `n'`. The first case is easy (0 + m = m) but the second case requires us to **recurse** by computing `add-ℕ n' m` and then returning its successor ((n + 1) + m = (n + m) + 1).

### Exercise 1.2: Define a function to multiply two natural numbers

```agda
mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ n m = {!   !}
```

**Hint:** here again pattern match on the first variable `n`, but now you will need to use your `add-ℕ` function in the case where a recursive call to `mul-ℕ` is called for. More specifically, our cases implement the defining equations `0 * m = 0` and `(n + 1) * m = n * m + m`.

### Exercise 1.3: Define the **predecessor** function

The predecessor maps `0 ↦ 0` and maps `(n + 1) ↦ n`:

```agda 
pred-ℕ : ℕ → ℕ
pred-ℕ n = {!   !}
```

### Exercise 1.4: Define a **parity** function

First we define a new data type `Parity` which has two values `Even` and `Odd`.

```agda 
data Parity : UU lzero where
    Even : Parity
    Odd : Parity
```

Notice that now that we can define functions which take inputs of type `Parity` by pattern matching against the patterns `Even` and `Odd`. For example, here is a function to map the parity `Even` to the natural number `0` and `Odd` to the natural number `1`.

```agda 
parity-to-ℕ : Parity → ℕ
parity-to-ℕ Even = zero-ℕ
parity-to-ℕ Odd = succ-ℕ zero-ℕ
```

Now define a function which maps the even numbers in `ℕ` to the parity `Even` and the odd numbers to `Odd`.

```agda 
parity : ℕ → Parity
parity n = {!   !}
```

### More exercises

#### Exercise 1.5a: 

Define a binary function `exp-ℕ` which raises one natural number to the power of another.

#### Exercise 1.5b: 

Define a binary function `min-ℕ` which takes two natural numbers and returns their minimum.

#### Exercise 1.5c: 

Define a binary function `max-ℕ` which takes two natural numbers and returns their maximum.

#### Exercise 1.5d:

Define a function `factorial-ℕ` which takes a natural number and returns its factorial.

#### Exercise 1.5e:

Define the binary function `_choose-ℕ_` which returns the number of ways of choosing `r` things from amongst `n` things.

**Note** here the underscores surrounding `choose-ℕ` tell Agda that you want to use infix notation for this function. This enables us to write expressions like `n choose-ℕ k`.

## Some logic

Dependent type theory invites us to regard types and mathematical propositions as interchangeable. Later we will see that homotopy type theory refines this idea a little, by identifying a suitable sub-collection of type that behave even more like traditional propositions.

Of course, if we think of types as propositions we should define some propositional connectives (and, or, implication etc).

### Conjunction (and)

We would like our conjunction operation to be given in standard **infix** notation, traditionally it **associates** to the right (so `A ∧ B ∧ C` is bracketed as `A ∧ (B ∧ C)`) and it **binds** more tightly than many other operators (so `A ∧ B ∨ C` is bracketed as `(A ∧ B) ∨ C`. The following `infix` directive instructs Agda to make `∧` into an infix operator that observes those conventions.

```agda 
infixr 2 _∧_
```

**Note:** you can enter a conjunction symbol `∧` by typing "\\and".

There is a variant of this directive called `infixl` which we use to tell Agda to regard a operator as associated to the **left**. The integer supplied to `infixr` or `infixl` before the operator symbol being declared is called the **precedence** of the operator. The higher the precedence of an operator the more tightly it binds to its arguments.

The **terms** of type `A ∧ B` should correspond to **proofs** of that proposition. Of course, to prove `A ∧ B` we must provide two proofs, one of `A` and one of `B`, so the terms of conjunction as a data type should be pairs. Accordingly we get the following data type declaration:

```agda 
data _∧_ ( A B : UU lzero ) : UU lzero where
    pair : A → B → A ∧ B
```

#### Introduction and elimination rules

We can think of the **constructor** `pair` as an **introduction rule**, it tells us how to introduce a proof of `A ∧ B` by "combining" given proofs of `A` and `B`. We should also have some **elimination rules** which allow us to deconstruct a proof of `A ∧ B` to give the "parts" it is made up of. We have two of these for conjunction and we can define them using pattern matching.

```agda 
∧-elim-left : { A B : UU lzero } → A ∧ B → A
∧-elim-left p = {!   !}

∧-elim-right : { A B : UU lzero } → A ∧ B → B
∧-elim-right p = {!   !}
```

The names `∧-elim-left` and `∧-elim-right` are traditional for these conjunction elimination rules. Correspondingly, the traditional name for the introduction rule `pair` is `∧-intro`, so for future use we define the following **alias**.

```agda 
∧-intro : { A B : UU lzero } → A → B → A ∧ B
∧-intro = pair
```

This function actually has 4 inputs, two of these are the propositions `A` and `B` of type `UU lzero` and the other two are terms of types `A` and `B` respectively. However, when we use `∧-intro` (or equally `pair`) we usually only need to supply two parameters as in `∧-intro p q`, where `p` is a term (proof) of type `A` and `q` is a term of type `B`. So why don't we also need to supply the first two parameters specifying the types of `p` and `q`.

The trick here is that Agda already knows the types of the two terms (proofs) supplied as parameters to an instance of `∧-intro`. Specifically, these may be computed from the ambient **environment** (list of declared variables and functions) at the point where that instance is used. Consequently Agda it doesn't need you to supply those types because it can **infer** them from the surrounding **context**.

In the **type** signature above, the declaration `{ A B : UU lzero}` of those first two parameters is surrounded by _curly braces_. This tells Agda that it should try to infer the types to be passed as those parameters from the context, rather than asking the mathematician writing expression involving `∧-intro` to provide them explicitly.

#### Associativity proof

Of course, conjunction should be an **associative** operator, which fact we prove with the following pair of functions. 

```agda 
∧-assoc-right : { A B C : UU lzero } → A ∧ (B ∧ C) → (A ∧ B) ∧ C
∧-assoc-right p = {!   !}

∧-assoc-left : { A B C : UU lzero } → (A ∧ B) ∧ C → A ∧ (B ∧ C)
∧-assoc-left p = {!   !}
```

**Note:** To define the **bodies** of these functions (proofs!) you can either use the native pattern matching facilities of Agda, as above, or you can build them as expressions made out of `∧-intro`, `∧-elim-right` and `∧-elim-left`. Have a go at the latter approach, it gives an answer that is much closer to the kind of proof you would see in a logic textbook.

### Symmetry and idempotency proofs

Oh I nearly forgot, conjunction is also a **symmetric** operator.

```agda 
∧-symm : { A B : UU lzero } → A ∧ B → B ∧ A 
∧-symm p = {!   !}
```

Here again, we can either prove this using pattern matching or we can construct a proof expression using `∧-intro`, `∧-elim-right` and `∧-elim-left`.

And conjunction is **idempotent**, in other words the propositions `A` and `A ∧ A` are inter-derivable.

```agda
∧-idempotent : { A : UU lzero } → A → A ∧ A
∧-idempotent p = {!   !}
```

This last rule tells us that given a proof of `A` we can construct a proof of `A ∧ A`. The converse direction of constructing a proof of `A` from one of `A ∧ A` can be achieved directly using either of ‵∧-elim-left` or `∧-elim-right` - _two distinct proofs_. 

### Disjunction (or)

Here again we start by making `∨` a right associated infix operator.

```agda 
infixr 1 _∨_
```

**Note:** you can enter a disjunction symbol `∨` by typing "\\or".

Notice here that we gave `∧` the precedence 2 and `∨` the precedence 1 so **and** binds more tightly to its arguments than **or** does. So, for example, Agda now brackets the expression `A ∧ B ∨ C` as `(A ∧ B) ∨ C`.

```agda 
data _∨_ ( A B : UU lzero ) : UU lzero where
    inl : A → A ∨ B
    inr : B → A ∨ B
```

#### Introduction and elimination rules

Here again the introduction rules for disjunction are simply the constructors `inl` (in left) and `inr` (in right) given in the body of the `data` declaration for `∨`. When viewed as introduction rules these traditionally revel in the names `∨-intro-left` and `∨-intro-right`, so we introduce those names as aliases for the constructors of `∨` here.

```agda 
∨-intro-left : { A B : UU lzero } → A → A ∨ B
∨-intro-left = inl

∨-intro-right : { A B : UU lzero } → B → A ∨ B
∨-intro-right = inr
```

Disjunction has a single elimination rule which is a little more involved.

```agda
∨-elim : { A B P : UU lzero } → (A → P) → (B → P) → A ∨ B → P
∨-elim f g r = {!   !}
```

We can interpret this as a logical rule in the following way:

* Given a procedure `f : A → P` that takes a proof of `A` and returns proof of `P`, and
* a procedure `g : B → P` that takes a proof of `B` and returns a proof of `P`, then 
* then `∨-elim f g` is a procedure which takes a proof `r : A ∨ B` that `A` or `B` holds and returns a proof `∨-elim f g r` that `P` holds.

#### Associativity, symmetry and idempotency laws

The disjunction operator is also associative, symmetric and idempotent. Try proving the following rules first by pattern matching and then by constructing expressions using `∨-intro-left`, `∨-intro-right` and `∨-elim`.

```agda 
∨-symm : { A B : UU lzero } → A ∨ B → B ∨ A 
∨-symm p = {!   !}

∨-assoc-left : { A B C : UU lzero } → A ∨ (B ∨ C) → (A ∨ B) ∨ C 
∨-assoc-left p = {!   !}

∨-assoc-right : { A B C : UU lzero } → (A ∨ B) ∨ C → A ∨ (B ∨ C)
∨-assoc-right p = {!   !}

∨-idempotent : { A : UU lzero } → A ∨ A → A 
∨-idempotent p = {!   !}
```

#### Distributive laws

In arithmetic we know that multiplication distributes over addition. Corresponding laws hold for conjunction and disjunction, though somehow it always surprises me the `∧` distributes over `∨` **and** `∨` distributes over `∧` - I guess because addition doesn't distribute over multiplication.

To demonstrate that these distributive laws do indeed hold, provide proofs of the following rules.

```agda 
∧-distributes-over-∨ : { A B C : UU lzero } → A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
∧-distributes-over-∨ p = {!   !}

∧-distributes-over-∨' : { A B C : UU lzero } → (A ∧ B) ∨ (A ∧ C)→ A ∧ (B ∨ C)
∧-distributes-over-∨' p = {!   !}

∨-distributes-over-∧ : { A B C : UU lzero } → A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C)
∨-distributes-over-∧ p = {!   !}

∨-distributes-over-∧' : { A B C : UU lzero } → (A ∨ B) ∧ (A ∨ C) → A ∨ (B ∧ C)
∨-distributes-over-∧' p = {!   !}
```

### Implication

Conjunction and disjunction are all well and good, but what about implication and those pesky quantifiers of the underworld of first order logic? We'll start with implication, specifying that is an infix operator....

```agda
infixr 0 _⇒_
```

**Notes:** You can enter an implication symbol `⇒` by typing "\=>". We've given this operator the lowest possible precedence 0 so it binds less tightly than either `∨` or `∧`. So the expression `A ∧ B ⇒ A ∨ B` is bracketed by Agda as `(A ∧ B) ⇒ (A ∨ B)`.

#### Introduction and elimination

... with the following declaration.

```agda
data _⇒_ (A B : UU lzero) : UU lzero where
    ⇒-intro : (A → B) → A ⇒ B
```

This defines our introduction rule, which can be interpreted as saying:

> Suppose we are given a procedure `f : A → B` which takes a proof of `A` and constructs a proof of `B` then we can build a proof `⇒-intro f` of `A ⇒ B`.

The elimination rule for implication is traditionally called **modus ponens**, but we will follow our naming convention and refer to it by the less interesting sounding moniker `⇒-elim`.

```agda
⇒-elim : { A B : UU lzero } → (A ⇒ B) → A → B
⇒-elim p a = {!   !}
```

As a simple example, we would expect there to be a proof that `A ⇒ A` holds for any proposition `A`, and this is indeed the case as demonstrated by the following rule definition.

```agda 
⇒-identity : { A : UU lzero } → A ⇒ A 
⇒-identity = ⇒-intro (λ x → x)
``` 

This, however, introduces a new expression type `λ x → t` which we haven't seen before, which are called **lambda expressions** or _anonymous functions_. The expression `λ x → t` stands for a function which takes a _parameter_ `x` and returns the value computed by the term `t`, which itself may contain instances of the variable `x`. So the function `λ x → x` takes an argument and simply returns that value unchanged - in other words, this is the **identity function** given as a lambda expression.

If you've done a traditional course in logic, you will probably recognise the following rules as appearing in Hilbert's presentation of propositional logic:

```agda 
K : { A B : UU lzero } → A ⇒ (B ⇒ A) 
K = {!   !}

S : { A B C : UU lzero } → (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C)
S = {!   !} 
```

These are called `K` and `S` because they also appear as key players in Moses Schönfinkel's [_Combinatory logic_](https://en.wikipedia.org/wiki/Combinatory_logic), where they are called _(K)onstant_ and _(S)chmelzen_ (which means to _fuse_ or _melt_ in German). Maybe it is more memorable to use the name _substitute_ as the name of the `S` combinator. Schönfinkel's name for `⇒-identity` was simply `I` for _(I)dentity_ I guess.

Now prove the rule I alluded to above when speaking of the binding power of `⇒`.

```agda 
∧-implies-∨ : { A B : UU lzero } → A ∧ B ⇒ A ∨ B
∧-implies-∨ = {!   !}
```
